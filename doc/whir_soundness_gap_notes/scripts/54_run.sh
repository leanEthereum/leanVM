#!/bin/sh
# 54_run.sh: regenerates 54_results.txt (referee report 54). Run inside scripts/. About 9 CPU-minutes, 4 processes at a time.
out=54_results.txt
tmp=$(mktemp -d)
: > $out

echo "=== python3 54_lemmaB_thm4.py" >> $out
python3 54_lemmaB_thm4.py >> $out
echo "=== python3 54_sections.py" >> $out
python3 54_sections.py >> $out

# the covering: mode M (j <= delta, as in note 51) and mode Mp (j <= max(K, (D_c + 1) // 2)), two agreements, four sizes
python3 54_cover.py a=0.7065 lg=25 depth=8 mode=M part=self > $tmp/self.txt 2>&1
for a in 0.7065 0.705; do
  for mode in M Mp; do
    for lg in 25 26 27 28; do
      python3 54_cover.py a=$a lg=$lg depth=8 mode=$mode part=cover sample=1000 > $tmp/c_${a}_${mode}_$lg.txt 2>&1 &
    done
    wait
  done
done
# finer cells for the open case
python3 54_cover.py a=0.7065 lg=25 depth=9 mode=M cases=open part=cover > $tmp/d9_M.txt 2>&1 &
python3 54_cover.py a=0.7065 lg=25 depth=9 mode=Mp cases=open part=cover > $tmp/d9_Mp.txt 2>&1 &
python3 54_cover.py a=0.7065 lg=25 depth=10 mode=Mp cases=open part=cover > $tmp/d10_Mp.txt 2>&1 &
python3 54_cover.py a=0.705 lg=25 depth=9 mode=Mp cases=open part=cover > $tmp/d9_Mp_705.txt 2>&1 &
wait
head -4 $tmp/self.txt >> $out
for a in 0.7065 0.705; do
  for mode in M Mp; do
    for lg in 25 26 27 28; do
      cat $tmp/c_${a}_${mode}_$lg.txt >> $out
    done
  done
done
cat $tmp/d9_M.txt $tmp/d9_Mp.txt $tmp/d10_Mp.txt $tmp/d9_Mp_705.txt >> $out
rm -r $tmp
echo "=== python3 54_single_cell.py" >> $out
python3 54_single_cell.py >> $out
