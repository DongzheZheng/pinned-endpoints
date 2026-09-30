#!/bin/sh
set -eu
# All proof-assistant execution stays on an explicitly chosen Linux server.
if [ "${PINNED_LEAN_SERVER:-}" != "1" ] || [ "$(uname -s)" != "Linux" ]; then
  echo "Run on the chosen Linux server with PINNED_LEAN_SERVER=1; local Lean execution is disabled." >&2
  exit 2
fi
if [ "$#" -gt 1 ]; then
  echo "Usage: server-verify.sh [--fresh]" >&2
  exit 2
fi
case "${1:-}" in
  ""|--fresh) ;;
  *) echo "Usage: server-verify.sh [--fresh]" >&2; exit 2 ;;
esac
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
if ! command -v lake >/dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then
  PATH="$HOME/.elan/bin:$PATH"
  export PATH
fi
command -v lake >/dev/null || { echo "Install elan/Lake on the server first." >&2; exit 2; }
command -v python3 >/dev/null
command -v git >/dev/null
python3 scripts/verify.py --source-only
python3 -m unittest discover -s scripts -p 'test_verify.py' -v
if [ -n "${PINNED_LEAN_PACKAGES:-}" ]; then
  test -d "$PINNED_LEAN_PACKAGES/mathlib" || { echo "Missing cached Mathlib checkout." >&2; exit 2; }
  mkdir -p .lake
  test -e .lake/packages || ln -s "$PINNED_LEAN_PACKAGES" .lake/packages
fi
if [ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]; then
  lake exe cache get
fi
run_dir="$(pwd)/.verification-runs/server-$(date -u +%Y%m%dT%H%M%SZ)"
# Default is a new project build plus type and axiom audits. Fresh replay is opt-in.
python3 scripts/verify.py "$@" --output "$run_dir"
