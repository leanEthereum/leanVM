#!/bin/sh
# 59_run_keylemma.sh: all exact checks of Section 2 and Section 5.1 of note 59 (about 40 seconds).
cd "$(dirname "$0")"
OUT=59_keylemma_output.txt
python3 59_keylemma.py > $OUT
python3 59_keylemma_slab.py 13 13 3072 "2,5,6" 1 "00;10;01;11" >> $OUT
python3 59_keylemma_slab.py 13 13 4096 "2,3,4,4" 1 "000;100;010;001;110;101;011" >> $OUT
python3 59_keylemma_slab.py 17 17 65536 "3,4,5,5" 3 "000;100;010;001;110;101" >> $OUT
python3 59_keylemma_slab.py 13 13 4096 "2,3,4,4" 1 "000;100;010;001;110" >> $OUT
python3 59_keylemma_slab.py 13 13 4096 "3,5,5" 3 "00;10;01;11" >> $OUT
python3 59_toy_keylemma.py >> $OUT
