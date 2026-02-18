#!/usr/bin/env bash
set -euo pipefail

have_rg=0
if command -v rg >/dev/null 2>&1; then
  have_rg=1
fi

if [[ "$have_rg" -ne 1 ]]; then
  echo "ℹ️ rg not found; using grep fallback"
fi

filter_lean_files() {
  # Reads paths on stdin; prints only *.lean paths, one per line.
  if [[ "$have_rg" -eq 1 ]]; then
    rg -N '\.lean$' || true
  else
    grep -E '\.lean$' || true
  fi
}

search_forbidden_tokens() {
  # Usage: search_forbidden_tokens <file>...
  # Searches for whole-word sorry/admit/axiom.
  if [[ "$have_rg" -eq 1 ]]; then
    rg -n '\b(sorry|admit|axiom)\b' -- "$@"
  else
    # -I: skip binary files; -n: line numbers; -E: extended regex
    grep -nIE '(^|[^[:alnum:]_])(sorry|admit|axiom)([^[:alnum:]_]|$)' -- "$@"
  fi
}

filter_import_changes() {
  # Reads diff on stdin; prints +import/-import lines.
  if [[ "$have_rg" -eq 1 ]]; then
    rg '^\+import |^\-import ' || true
  else
    grep -E '^\+import |^\-import ' || true
  fi
}

echo "== git status =="
git status --porcelain

CHANGED_TRACKED_FILES=$( { git diff --name-only; git diff --name-only --cached; } | sort -u || true )
CHANGED_LEAN=$(printf '%s\n' "${CHANGED_TRACKED_FILES:-}" | filter_lean_files)

echo
echo "== changed lean files =="
echo "${CHANGED_LEAN:-<none>}"

if [[ -n "${CHANGED_LEAN:-}" ]]; then
  echo
  echo "== forbidden tokens in changed lean files (sorry/admit/axiom) =="
  # shellcheck disable=SC2086
  if ! search_forbidden_tokens $CHANGED_LEAN; then
    echo "✅ none found"
  fi

  echo
  echo "== import changes in changed lean files =="
  for f in $CHANGED_LEAN; do
    echo "---- $f ----"
    git diff --unified=0 -- "$f" | filter_import_changes || echo "(no import changes)"
  done
fi

echo
echo "== report.txt =="
REPORT_TXT=$(find . -path './.git' -prune -o -name report.txt -print | sed 's|^\./||' || true)
if [[ -z "${REPORT_TXT:-}" ]]; then
  echo "❌ report.txt missing"
else
  echo "✅ found report.txt at:"
  printf '%s\n' "$REPORT_TXT"
  echo
  while IFS= read -r p; do
    [[ -z "$p" ]] && continue
    echo "---- $p (first 120 lines) ----"
    sed -n '1,120p' "$p"
    echo
  done <<< "$REPORT_TXT"
fi

echo
echo "== save git diff (tracked files only) =="
stamp=$(date +"%Y%m%d_%H%M%S" 2>/dev/null || echo "unknown_time")
out="diff_${stamp}.patch"

# Save only tracked diffs; this will not include untracked report.txt
git diff > "$out"

# Helpful summary
if [[ -s "$out" ]]; then
  echo "✅ saved patch: $out"
  echo "== patch stat =="
  git diff --stat
else
  echo "ℹ️ no tracked changes; patch file is empty: $out"
fi