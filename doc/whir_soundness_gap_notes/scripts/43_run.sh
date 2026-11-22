#!/bin/sh
# Runs every check of 43-low-rate-residuals.md and writes 43_results.txt (about 4 minutes, one core).
cd "$(dirname "$0")" || exit 1
{
  echo "== 43_structure.py"; python3 43_structure.py
  echo "== 43_flat_sections.py"; python3 43_flat_sections.py
  echo "== 43_flat_sections.py 7 7 field 4 14"; python3 43_flat_sections.py 7 7 field 4 14
  echo "== 43_flat_K.py"; python3 43_flat_K.py
  echo "== 43_gold_window.py 1000"; python3 43_gold_window.py 1000
  echo "== 43_rate16_family.py 12"; python3 43_rate16_family.py 12
  echo "== 43_rates.py"; python3 43_rates.py
} > 43_results.txt 2>&1
