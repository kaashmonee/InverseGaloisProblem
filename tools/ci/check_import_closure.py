#!/usr/bin/env python3
"""CI tripwire for this repository: import-closure and `sorry` checks.

Both checks use only the Python 3 standard library, are deterministic, and are
cheap enough to run on every push without a Lean toolchain or a Mathlib download.

closure
    Every tracked ``.lean`` file must be reachable through the ``import`` graph
    from a root module of one of the *default* Lake targets (``defaultTargets``
    in ``lakefile.toml``).  A file that is not reachable is not built, is not
    checked by anything, and can rot silently -- so it is reported unless it is
    excused in ``tools/ci/closure_allowlist.txt`` or lives under the source
    directory of a deliberately non-default library.

sorry
    No tracked ``.lean`` file outside a non-default library's source directory
    may contain ``sorry``.  The comparator library under ``extras/comparator``
    is the one place where an unproved statement is the point.

Exit status is 0 when every requested check passes and 1 otherwise.
"""

from __future__ import annotations

import argparse
import posixpath
import re
import subprocess
import sys
from pathlib import Path

# `sorry` is permitted here no matter what the lakefile says.
SORRY_EXEMPT_DIRS = ("extras/comparator",)

DEFAULT_ALLOWLIST = "tools/ci/closure_allowlist.txt"

# Lean import lines.  Tolerant of the modifiers newer Lean versions allow
# (`public import`, `import all`) while keeping the plain `import Foo.Bar` core.
IMPORT_RE = re.compile(
    r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([\w.À-￿]+)"
)

SORRY_RE = re.compile(r"\bsorry\b")


# --------------------------------------------------------------------------- #
# Minimal tolerant TOML-subset parser
# --------------------------------------------------------------------------- #

_ARRAY_TABLE_RE = re.compile(r"^\[\[\s*([^\]]+?)\s*\]\]\s*$")
_TABLE_RE = re.compile(r"^\[\s*([^\]]+?)\s*\]\s*$")
_KEY_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_.-]*)\s*=\s*(.*)$")


def _strip_comment(line):
    """Drop a trailing ``#`` comment, respecting quoted strings."""
    out = []
    quote = None
    for ch in line:
        if quote:
            out.append(ch)
            if ch == quote:
                quote = None
        elif ch in "\"'":
            quote = ch
            out.append(ch)
        elif ch == "#":
            break
        else:
            out.append(ch)
    return "".join(out)


def _parse_scalar(text):
    text = text.strip()
    if len(text) >= 2 and text[0] == text[-1] and text[0] in "\"'":
        return text[1:-1]
    if text == "true":
        return True
    if text == "false":
        return False
    try:
        return int(text)
    except ValueError:
        return text


def _split_top_level(text):
    """Split an array body on commas that are neither nested nor quoted."""
    parts, buf, depth, quote = [], [], 0, None
    for ch in text:
        if quote:
            buf.append(ch)
            if ch == quote:
                quote = None
            continue
        if ch in "\"'":
            quote = ch
            buf.append(ch)
        elif ch in "[{":
            depth += 1
            buf.append(ch)
        elif ch in "]}":
            depth -= 1
            buf.append(ch)
        elif ch == "," and depth == 0:
            parts.append("".join(buf))
            buf = []
        else:
            buf.append(ch)
    parts.append("".join(buf))
    return [p for p in (p.strip() for p in parts) if p]


def _finish_value(blob, close):
    blob = blob.strip()
    if close == "{}":
        return blob  # inline table: kept raw, never read
    inner = blob[1:-1] if blob.startswith("[") and blob.endswith("]") else blob
    return [_parse_scalar(p) for p in _split_top_level(inner)]


def parse_toml_subset(text):
    """Parse the subset of TOML this repository's lakefile uses.

    Handles ``key = value`` scalars, single- and multi-line arrays, ``[table]``
    and ``[[array_of_tables]]`` headers.  Inline tables are kept as raw strings;
    nothing here needs to read inside one.
    """
    root = {}
    current = root
    pending_key = None
    pending_buf = []
    pending_close = ""
    depth = 0

    for raw in text.splitlines():
        line = _strip_comment(raw).strip()
        if pending_key is not None:
            pending_buf.append(line)
            depth += line.count(pending_close[0]) - line.count(pending_close[1])
            if depth <= 0:
                current[pending_key] = _finish_value(" ".join(pending_buf), pending_close)
                pending_key, pending_buf, depth = None, [], 0
            continue
        if not line:
            continue
        m = _ARRAY_TABLE_RE.match(line)
        if m:
            table = {}
            root.setdefault(m.group(1), []).append(table)
            current = table
            continue
        m = _TABLE_RE.match(line)
        if m:
            current = root.setdefault(m.group(1), {})
            continue
        m = _KEY_RE.match(line)
        if not m:
            continue
        key, value = m.group(1), m.group(2).strip()
        if value[:1] in ("[", "{"):
            close = "[]" if value[0] == "[" else "{}"
            d = value.count(close[0]) - value.count(close[1])
            if d > 0:
                pending_key, pending_buf, pending_close, depth = key, [value], close, d
            else:
                current[key] = _finish_value(value, close)
        else:
            current[key] = _parse_scalar(value)
    return root


# --------------------------------------------------------------------------- #
# Lake model
# --------------------------------------------------------------------------- #


class LeanLib:
    """One ``[[lean_lib]]`` table."""

    def __init__(self, table):
        self.name = str(table.get("name", ""))
        self.roots = tuple(str(r) for r in table.get("roots", []) or [])
        self.globs = tuple(str(g) for g in table.get("globs", []) or [])
        self.src_dir = posixpath.normpath(str(table.get("srcDir", ".") or "."))

    def __repr__(self):  # pragma: no cover - debugging aid
        return "LeanLib(%r, srcDir=%r)" % (self.name, self.src_dir)


def module_to_path(module, src_dir):
    rel = module.replace(".", "/") + ".lean"
    if src_dir in (".", ""):
        return rel
    return posixpath.normpath(posixpath.join(src_dir, rel))


def _path_to_module(path, src_dir):
    rel = path
    if src_dir not in (".", "") and rel.startswith(src_dir + "/"):
        rel = rel[len(src_dir) + 1:]
    return rel[: -len(".lean")].replace("/", ".")


def expand_roots(lib, tracked):
    """Root modules of a library, expanding Lake's glob suffixes.

    ``Foo`` is the single module ``Foo``; ``Foo.*`` is every module strictly
    below ``Foo``; ``Foo.+`` is ``Foo`` together with everything below it.
    """
    if lib.roots:
        return list(lib.roots)
    if not lib.globs:
        return [lib.name] if lib.name else []
    modules = []
    for glob in lib.globs:
        if glob.endswith(".*") or glob.endswith(".+"):
            base = glob[:-2]
            if glob.endswith(".+"):
                modules.append(base)
            prefix = module_to_path(base, lib.src_dir)[: -len(".lean")] + "/"
            for path in sorted(tracked):
                if path.startswith(prefix):
                    modules.append(_path_to_module(path, lib.src_dir))
        else:
            modules.append(glob)
    seen, out = set(), []
    for m in modules:
        if m not in seen:
            seen.add(m)
            out.append(m)
    return out


# --------------------------------------------------------------------------- #
# Repository inspection
# --------------------------------------------------------------------------- #


def tracked_lean_files(repo_root):
    proc = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"],
        cwd=str(repo_root),
        check=True,
        capture_output=True,
        text=True,
    )
    return sorted(p for p in proc.stdout.split("\0") if p)


def header_imports(text):
    """Modules imported by a Lean file, read from its header only."""
    modules = []
    depth = 0
    for line in text.splitlines():
        if depth:
            depth = max(depth + line.count("/-") - line.count("-/"), 0)
            continue
        stripped = line.strip()
        if not stripped or stripped.startswith("--"):
            continue
        if stripped.startswith("/-"):
            depth = max(line.count("/-") - line.count("-/"), 0)
            continue
        m = IMPORT_RE.match(line)
        if m:
            modules.append(m.group(1))
            continue
        break  # first real declaration: the import header is over
    return modules


def compute_closure(libs, tracked, repo_root):
    """Walk the import graph out from the roots of ``libs``.

    Returns the reachable file set and any root module that resolves to no
    tracked file (a broken target, reported as a failure).
    """
    closure = set()
    missing_roots = []
    queue = []

    for lib in libs:
        for module in expand_roots(lib, tracked):
            path = module_to_path(module, lib.src_dir)
            if path in tracked:
                if path not in closure:
                    closure.add(path)
                    queue.append((path, lib.src_dir))
            else:
                missing_roots.append((lib.name, module, path))

    while queue:
        path, src_dir = queue.pop()
        try:
            text = (repo_root / path).read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for module in header_imports(text):
            for candidate_dir in (src_dir, "."):
                candidate = module_to_path(module, candidate_dir)
                if candidate in tracked:
                    if candidate not in closure:
                        closure.add(candidate)
                        queue.append((candidate, candidate_dir))
                    break
            # An import that resolves to no tracked file is external
            # (Mathlib, Batteries, Std, ...) and is ignored.
    return closure, missing_roots


def load_allowlist(path):
    if not path.is_file():
        return []
    entries = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            entries.append(line.lstrip("./"))
    return entries


def allowlist_match(rel, entries):
    for entry in entries:
        if rel == entry:
            return entry
        if entry.endswith("/") and rel.startswith(entry):
            return entry
        if rel.startswith(entry.rstrip("/") + "/"):
            return entry
    return None


def under_any(rel, dirs):
    for d in dirs:
        if d in (".", ""):
            continue
        if rel == d or rel.startswith(d.rstrip("/") + "/"):
            return d
    return None


# --------------------------------------------------------------------------- #
# Checks
# --------------------------------------------------------------------------- #


def check_closure(repo_root, tracked, default_libs, other_srcdirs, allowlist, out):
    closure, missing_roots = compute_closure(default_libs, set(tracked), repo_root)

    orphans = []
    excused = 0
    for rel in tracked:
        if rel in closure:
            continue
        if allowlist_match(rel, allowlist) or under_any(rel, other_srcdirs):
            excused += 1
            continue
        orphans.append(rel)

    targets = ", ".join(lib.name for lib in default_libs)
    ok = not orphans and not missing_roots

    if missing_roots:
        print(
            "closure: FAIL -- %d root module(s) of a default target resolve to no "
            "tracked file" % len(missing_roots),
            file=out,
        )
        for lib_name, module, path in missing_roots:
            print("%s  (root %s of lean_lib %s)" % (path, module, lib_name), file=out)

    if orphans:
        print(
            "closure: FAIL -- %d tracked .lean file(s) are not reachable from any "
            "default Lake target (%s)." % (len(orphans), targets),
            file=out,
        )
        print(
            "  Import each from a target's graph, or excuse it in %s with a reason."
            % DEFAULT_ALLOWLIST,
            file=out,
        )
        for rel in orphans:
            print(rel, file=out)

    if ok:
        print(
            "closure: OK -- %d tracked .lean file(s); %d in the default-target "
            "closure (%s); %d excused."
            % (len(tracked), len(closure), targets, excused),
            file=out,
        )
    return ok


def check_sorry(tracked, repo_root, exempt, out):
    hits = []
    scanned = 0
    exempted = 0
    for rel in tracked:
        if under_any(rel, exempt):
            exempted += 1
            continue
        scanned += 1
        try:
            text = (repo_root / rel).read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for lineno, line in enumerate(text.splitlines(), start=1):
            if SORRY_RE.search(line):
                hits.append((rel, lineno, line.strip()))

    where = ", ".join(d.rstrip("/") + "/" for d in exempt) or "(nothing)"
    if hits:
        print(
            "sorry: FAIL -- `sorry` appears in %d tracked .lean file(s) outside %s"
            % (len(set(h[0] for h in hits)), where),
            file=out,
        )
        for rel, lineno, line in hits:
            print("%s:%d: %s" % (rel, lineno, line), file=out)
        return False
    print(
        "sorry: OK -- no `sorry` in %d tracked .lean file(s); %d exempt under %s"
        % (scanned, exempted, where),
        file=out,
    )
    return True


# --------------------------------------------------------------------------- #
# Entry point
# --------------------------------------------------------------------------- #


def run(repo_root, do_closure, do_sorry, allowlist_path, out):
    lakefile = repo_root / "lakefile.toml"
    if not lakefile.is_file():
        print("error: no lakefile.toml at %s" % lakefile, file=out)
        return 1

    config = parse_toml_subset(lakefile.read_text(encoding="utf-8"))
    default_targets = [str(t) for t in config.get("defaultTargets", []) or []]
    libs = [LeanLib(t) for t in config.get("lean_lib", []) or []]
    default_libs = [lib for lib in libs if lib.name in default_targets]
    if not default_libs:
        print(
            "error: lakefile.toml declares no default lean_lib targets "
            "(defaultTargets = %s)" % default_targets,
            file=out,
        )
        return 1

    default_srcdirs = set(lib.src_dir for lib in default_libs)
    # A non-default library's source directory is excused wholesale.  "." is
    # never treated that way: it would excuse the entire repository.
    other_srcdirs = sorted(
        set(lib.src_dir for lib in libs if lib.name not in default_targets)
        - default_srcdirs
        - set([".", ""])
    )

    tracked = tracked_lean_files(repo_root)
    allowlist = load_allowlist(allowlist_path)

    for src in other_srcdirs:
        print(
            "note: %s/ is the source directory of a non-default lean_lib; its files "
            "are excused from both checks." % src,
            file=out,
        )

    ok = True
    if do_closure:
        ok = check_closure(
            repo_root, tracked, default_libs, other_srcdirs, allowlist, out
        ) and ok
    if do_sorry:
        exempt = sorted(set(other_srcdirs) | set(SORRY_EXEMPT_DIRS))
        ok = check_sorry(tracked, repo_root, exempt, out) and ok
    return 0 if ok else 1


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--repo-root",
        default=str(Path(__file__).resolve().parents[2]),
        help="repository to check (default: the checkout this script lives in)",
    )
    parser.add_argument(
        "--allowlist", default=None, help="default: <repo-root>/" + DEFAULT_ALLOWLIST
    )
    parser.add_argument(
        "--check-closure", action="store_true", help="run only the import-closure check"
    )
    parser.add_argument(
        "--check-sorry", action="store_true", help="run only the sorry check"
    )
    args = parser.parse_args(argv)

    repo_root = Path(args.repo_root).resolve()
    allowlist_path = (
        Path(args.allowlist) if args.allowlist else repo_root / DEFAULT_ALLOWLIST
    )
    do_closure = args.check_closure or not args.check_sorry
    do_sorry = args.check_sorry or not args.check_closure
    return run(repo_root, do_closure, do_sorry, allowlist_path, sys.stdout)


if __name__ == "__main__":
    sys.exit(main())
