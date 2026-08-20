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
