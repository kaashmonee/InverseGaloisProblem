"""Tests for tools/ci/check_import_closure.py.

Each test builds a throwaway git repository with its own lakefile and a handful
of tiny Lean files, so the assertions are about the checker's behaviour and not
about whatever this repository's tree happens to look like today.
"""

import importlib.util
import io
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
CHECKER_PATH = REPO_ROOT / "tools" / "ci" / "check_import_closure.py"


def _load_checker():
    spec = importlib.util.spec_from_file_location("check_import_closure", CHECKER_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


checker = _load_checker()


# One default target rooted at `Main`, one non-default library whose sources
# live in `extras/side` -- the shape of the real lakefile, in miniature.
LAKEFILE = """\
name = "Mini"
defaultTargets = ["Main"]

[[lean_lib]]
name = "Main"
roots = ["Main"]
leanOptions = { linter.style.multiGoal = true }

# Deliberately not a default target.
[[lean_lib]]
name = "Extra"
srcDir = "extras/side"
"""

BASE_FILES = {
    "Main.lean": "import Mathlib\nimport Main.Helper\n\n/-! # Entry point -/\n",
    "Main/Helper.lean": "import Mathlib\n\ntheorem helper : True := trivial\n",
    "extras/side/Extra.lean": "import Mathlib\n\ntheorem extra : True := trivial\n",
}


def make_repo(tmp_path, files=None, allowlist=None, lakefile=LAKEFILE):
    """Write a mini repository into ``tmp_path`` and stage it so git ls-files works."""
    contents = dict(BASE_FILES)
    contents.update(files or {})
    for rel, text in contents.items():
        path = tmp_path / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
    (tmp_path / "lakefile.toml").write_text(lakefile, encoding="utf-8")
    if allowlist is not None:
        path = tmp_path / "tools" / "ci" / "closure_allowlist.txt"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(allowlist, encoding="utf-8")
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
    return tmp_path


def run_checks(repo, closure=True, sorry_check=True):
    buf = io.StringIO()
    code = checker.run(
        Path(repo),
        closure,
        sorry_check,
        Path(repo) / "tools" / "ci" / "closure_allowlist.txt",
        buf,
    )
    return code, buf.getvalue()


def reported_paths(output):
    """The bare paths the checker prints, one per line, under its headers."""
    return [
        line
        for line in output.splitlines()
        if line and not line.startswith((" ", "closure:", "sorry:", "note:", "error:"))
    ]


# --------------------------------------------------------------------------- #
# Closure check
# --------------------------------------------------------------------------- #


def test_file_reachable_from_a_default_root_passes(tmp_path):
    code, out = run_checks(make_repo(tmp_path))
    assert code == 0, out
    assert "closure: OK" in out
    assert "Main/Helper.lean" not in reported_paths(out)


def test_orphan_is_detected(tmp_path):
    repo = make_repo(tmp_path, {"Main/Stray.lean": "import Mathlib\n"})
    code, out = run_checks(repo)
    assert code == 1
    assert "closure: FAIL" in out
    assert reported_paths(out) == ["Main/Stray.lean"]


def test_transitive_import_keeps_a_file_in_the_closure(tmp_path):
    repo = make_repo(
        tmp_path,
        {
            "Main/Helper.lean": "import Mathlib\nimport Main.Deep\n",
            "Main/Deep.lean": "import Mathlib\n",
        },
    )
    code, out = run_checks(repo)
    assert code == 0, out


def test_import_header_is_read_through_a_copyright_block(tmp_path):
    repo = make_repo(
        tmp_path,
        {
            "Main.lean": "/-\nCopyright (c) 2025.\n-/\nimport Main.Helper\nimport Main.Deep\n",
            "Main/Deep.lean": "import Mathlib\n",
        },
    )
    code, out = run_checks(repo)
    assert code == 0, out


@pytest.mark.parametrize(
    "entry", ["Main/Stray.lean", "Main/Stray.lean  # parked on purpose", "Main/"]
)
def test_allowlisted_file_is_ignored(tmp_path, entry):
    repo = make_repo(
        tmp_path,
        {"Main/Stray.lean": "import Mathlib\n"},
        allowlist="# reason: kept for reference\n" + entry + "\n",
    )
    code, out = run_checks(repo)
    assert code == 0, out
    assert "closure: OK" in out


def test_non_default_srcdir_is_excused_and_noted(tmp_path):
    repo = make_repo(tmp_path)
    code, out = run_checks(repo)
    assert code == 0, out
    assert "note: extras/side/ is the source directory of a non-default lean_lib" in out
    assert "extras/side/Extra.lean" not in reported_paths(out)


def test_broken_default_root_fails(tmp_path):
    repo = make_repo(
        tmp_path,
        lakefile='defaultTargets = ["Main"]\n\n[[lean_lib]]\nname = "Main"\nroots = ["Absent"]\n',
    )
    code, out = run_checks(repo)
    assert code == 1
    assert "resolve to no tracked file" in out
    assert "Absent.lean" in out


# --------------------------------------------------------------------------- #
# sorry check
# --------------------------------------------------------------------------- #


def test_sorry_outside_the_permitted_directory_is_detected(tmp_path):
    repo = make_repo(
        tmp_path,
        {"Main/Helper.lean": "import Mathlib\n\ntheorem helper : True := sorry\n"},
    )
    code, out = run_checks(repo)
    assert code == 1
    assert "sorry: FAIL" in out
    assert "Main/Helper.lean:3:" in out


def test_sorry_inside_a_non_default_srcdir_is_permitted(tmp_path):
    repo = make_repo(
        tmp_path,
        {"extras/side/Extra.lean": "import Mathlib\n\ntheorem extra : True := sorry\n"},
    )
    code, out = run_checks(repo)
    assert code == 0, out
    assert "sorry: OK" in out


def test_sorry_ax_is_not_a_sorry(tmp_path):
    repo = make_repo(
        tmp_path,
        {"Main/Helper.lean": "import Mathlib\n\n#print axioms sorryAxFree\n"},
    )
    code, out = run_checks(repo)
    assert code == 0, out


def test_checks_can_run_one_at_a_time(tmp_path):
    repo = make_repo(
        tmp_path,
        {
            "Main/Stray.lean": "import Mathlib\n",
            "Main/Helper.lean": "import Mathlib\n\ntheorem helper : True := sorry\n",
        },
    )
    code, out = run_checks(repo, closure=True, sorry_check=False)
    assert code == 1 and "closure: FAIL" in out and "sorry:" not in out
    code, out = run_checks(repo, closure=False, sorry_check=True)
    assert code == 1 and "sorry: FAIL" in out and "closure:" not in out


# --------------------------------------------------------------------------- #
# Reading the import header
#
# Every case here is a way the header parser could quietly read *fewer* imports
# than a file really has.  That is the dangerous direction: a dropped edge does
# not fail loudly, it invents an orphan somewhere else in the tree.
# --------------------------------------------------------------------------- #


def test_guillemet_module_name_is_read(tmp_path):
    repo = make_repo(
        tmp_path,
        {
            "Main.lean": "import Mathlib\nimport «Odd Name»\nimport Main.Helper\n",
            "Main/Deep.lean": "import Mathlib\n",
            "Main/Helper.lean": "import Mathlib\nimport Main.Deep\n",
        },
    )
    code, out = run_checks(repo)
    assert code == 0, out


def test_byte_order_mark_does_not_hide_the_header(tmp_path):
    repo = make_repo(
        tmp_path,
        {
            "Main.lean": "\ufeffimport Mathlib\nimport Main.Helper\n",
            "Main/Helper.lean": "import Mathlib\n",
        },
    )
    code, out = run_checks(repo)
    assert code == 0, out


def test_import_sharing_a_line_with_the_end_of_a_comment_block(tmp_path):
    repo = make_repo(
        tmp_path,
        {"Main.lean": "/-\nCopyright (c) 2025.\n-/ import Main.Helper\n"},
    )
    code, out = run_checks(repo)
    assert code == 0, out


def test_crlf_header_is_read(tmp_path):
    repo = make_repo(
        tmp_path,
        {
            "Main.lean": "import Mathlib\r\nimport Main.Helper\r\n\r\n/-! # Entry -/\r\n",
            "Main/Helper.lean": "import Mathlib\r\n",
        },
    )
    code, out = run_checks(repo)
    assert code == 0, out


def test_unreadable_import_line_fails_instead_of_being_swallowed(tmp_path):
    # `«` with no closing `»` is not a module name.  The old parser treated such
    # a line as the first declaration and dropped every import after it.
    repo = make_repo(
        tmp_path,
        {"Main.lean": "import Mathlib\nimport «unclosed\nimport Main.Helper\n"},
    )
    code, out = run_checks(repo)
    assert code == 1
    assert "could not be parsed" in out
    assert "Main.lean:2:" in out


# --------------------------------------------------------------------------- #
# Target shapes: dotted roots, globs, a module beside a directory of the same name
# --------------------------------------------------------------------------- #


NESTED_LAKEFILE = """\
defaultTargets = ["Main", "Nested"]

[[lean_lib]]
name = "Main"
roots = ["Main"]

[[lean_lib]]
name = "Nested"
roots = ["Main.Deep.One", "Main.Deep.Two"]

[[lean_lib]]
name = "Extra"
srcDir = "extras/side"
"""


def test_dotted_roots_resolve_to_nested_paths(tmp_path):
    """The `MathieuRigidity` shape: a target whose roots are dotted module names."""
    repo = make_repo(
        tmp_path,
        {
            "Main/Deep/One.lean": "import Mathlib\nimport Main.Deep.Shared\n",
            "Main/Deep/Two.lean": "import Mathlib\n",
            "Main/Deep/Shared.lean": "import Mathlib\n",
        },
        lakefile=NESTED_LAKEFILE,
    )
    code, out = run_checks(repo)
    assert code == 0, out
    assert "closure: OK" in out


def test_a_dotted_root_that_names_no_file_is_reported(tmp_path):
    repo = make_repo(
        tmp_path,
        {"Main/Deep/One.lean": "import Mathlib\n"},
        lakefile=NESTED_LAKEFILE,
    )
    code, out = run_checks(repo)
    assert code == 1
    assert "Main/Deep/Two.lean  (root Main.Deep.Two of lean_lib Nested)" in out


def _glob_lakefile(glob):
    return (
        'defaultTargets = ["Main"]\n\n[[lean_lib]]\nname = "Main"\n'
        'globs = ["%s"]\n\n[[lean_lib]]\nname = "Extra"\nsrcDir = "extras/side"\n' % glob
    )


def test_plus_glob_covers_the_root_module_and_everything_below(tmp_path):
    repo = make_repo(
        tmp_path,
        {"Main/Stray.lean": "import Mathlib\n"},
        lakefile=_glob_lakefile("Main.+"),
    )
    code, out = run_checks(repo)
    assert code == 0, out


def test_star_glob_excludes_the_root_module_itself(tmp_path):
    # `Main.*` is everything strictly below `Main`, so `Main.lean` is built by
    # nothing and must be reported.
    repo = make_repo(tmp_path, lakefile=_glob_lakefile("Main.*"))
    code, out = run_checks(repo)
    assert code == 1
    assert reported_paths(out) == ["Main.lean"]


def test_module_beside_a_directory_of_the_same_name_is_judged_separately(tmp_path):
    """`Main/Poly.lean` and `Main/Poly/*.lean` are different modules.

    This is the shape of the real `InverseGalois/Polynomial.lean` finding: the
    umbrella module is dead while every leaf under the directory is alive.
    """
    repo = make_repo(
        tmp_path,
        {
            "Main/Helper.lean": "import Mathlib\nimport Main.Poly.Sub\n",
            "Main/Poly.lean": "import Mathlib\nimport Main.Poly.Sub\n",
            "Main/Poly/Sub.lean": "import Mathlib\n",
        },
    )
    code, out = run_checks(repo)
    assert code == 1
    assert reported_paths(out) == ["Main/Poly.lean"]


def test_allowlist_keeps_a_leading_dot_in_a_directory_name(tmp_path):
    repo = make_repo(
        tmp_path,
        {".vendor/Stray.lean": "import Mathlib\n"},
        allowlist="# reason: vendored\n.vendor/\n",
    )
    code, out = run_checks(repo)
    assert code == 0, out


def test_allowlist_entry_may_be_written_with_a_leading_dot_slash(tmp_path):
    repo = make_repo(
        tmp_path,
        {"Main/Stray.lean": "import Mathlib\n"},
        allowlist="# reason: parked\n./Main/Stray.lean\n",
    )
    code, out = run_checks(repo)
    assert code == 0, out


# --------------------------------------------------------------------------- #
# lakefile parsing, against the real file
# --------------------------------------------------------------------------- #


def test_parses_this_repositorys_lakefile():
    config = checker.parse_toml_subset(
        (REPO_ROOT / "lakefile.toml").read_text(encoding="utf-8")
    )
    assert config["defaultTargets"] == ["InverseGalois", "Mathieu", "MathieuRigidity"]
    libs = {lib.name: lib for lib in (checker.LeanLib(t) for t in config["lean_lib"])}
    assert libs["InverseGalois"].roots == ("InverseGalois",)
    assert libs["Mathieu"].globs == ("Mathieu",)
    assert libs["MathieuRigidity"].roots == (
        "InverseGalois.Rigidity.Examples.MathieuM11",
        "InverseGalois.Rigidity.Examples.MathieuM12",
    )
    assert libs["Challenge"].src_dir == "extras/comparator"
    assert libs["Solution"].src_dir == "extras/comparator"
