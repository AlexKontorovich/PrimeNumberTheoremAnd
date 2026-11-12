#!/bin/bash
# Build the Mathlib-free campaign modules M0..M(n-1) in batches of $JOBS,
# within cores 0..JOBS-1, waiting while available memory is low.
# Usage: tools/psi_planner/build_campaign.sh <name> <nmodules> <log> [JOBS=6] [minFreeGB=9]
name=$1; n=$2; log=$3; JOBS=${4:-6}; MINFREE=${5:-9}
cd "$(dirname "$0")/../.."
for ((i=0; i<n; i+=JOBS)); do
  while [ "$(awk '/MemAvailable/ {print int($2/1048576)}' /proc/meminfo)" -lt "$MINFREE" ]; do
    echo "$(date +%T) waiting for memory" >> "$log"; sleep 60; done
  mods=""
  for ((j=i; j<i+JOBS && j<n; j++)); do mods="$mods RSBounds.PsiFinite.Campaign.$name.M$j"; done
  start=$(date +%s)
  nice -n 19 taskset -c 0-$((JOBS-1)) lake build $mods > "$log.batch" 2>&1
  st=$?
  echo "$(date +%T) batch $i status $st $(( $(date +%s) - start ))s $(grep -o 'Built [^ ]* ([0-9.]*s)' "$log.batch" | tr '\n' ' ')" >> "$log"
  if [ $st -ne 0 ]; then grep -E "error" "$log.batch" | head -20 >> "$log"; echo FAILED >> "$log"; exit 1; fi
done
echo DONE >> "$log"
