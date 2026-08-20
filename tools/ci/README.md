# CI tripwire

`check_import_closure.py` runs two structural checks over the source tree. It needs
only Python 3 and `git` -- no Lean toolchain, no Mathlib -- and finishes in well under
a second, so `.github/workflows/tripwire.yml` runs it on every push and pull request.

**closure.** Reads `defaultTargets` and the `[[lean_lib]]` tables from `lakefile.toml`,
resolves each default target's root modules to files, and walks the `import` graph out
from them. Every tracked `.lean` file the walk never reaches is reported: nothing builds
it, so nothing checks it, and it can rot while the tree still looks healthy. Imports
that resolve to no tracked file are external (Mathlib, Batteries, ...) and are ignored.

**sorry.** No tracked `.lean` file may contain `sorry` outside the source directory of a
non-default library -- in practice `extras/comparator`, whose `Challenge` depends on one.

## Running it

    python3 tools/ci/check_import_closure.py                   # both checks
    python3 tools/ci/check_import_closure.py --check-closure   # or --check-sorry
    python3 -m pytest tests/ci -v                              # the checker's own tests

Exit status is 0 when every requested check passes, 1 otherwise; every offending file is
named on its own line.

## The allowlist

`closure_allowlist.txt` excuses files from the closure check only: one exact path or one
directory prefix (trailing `/`) per line, `#` starts a comment. Give every entry a
reason -- it is all that separates "parked on purpose" from "forgotten". Files under a
non-default library's `srcDir` are excused automatically, with a note in the output.
