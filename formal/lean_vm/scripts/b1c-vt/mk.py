import os, sys
# usage: python3 -I mk.py <t>  (t = 0..4) writes Tables/Vt/FormsT<t>.lean; `import mk; mk.gen_t5()` writes FormsT5a/T5b/T5.
# First run: python3 -I dump.py ../../LeanVM/Guest/Data vt_ir.txt (from this directory).
import sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genforms import *
IMP='LeanVM.Guest.B1.Tables.Vt.FormsDiff\npublic import LeanVM.Guest.B1.Tables.Vt.PullSels\npublic import LeanVM.Guest.B1.Tables.Vt.Pi'
def write(mod,doc,imp,body):
    open(os.path.join(VT_LEAN, f'{mod}.lean'),'w').write(HDR%dict(mod=mod,doc=doc,imp=imp)+body+'\n'+FTR)
if __name__=='__main__':
    t=int(sys.argv[1])
    doc="Table %d's forms on the three sides, from the guest's statements: each block's value from its\n  baked terms, the table's form the blocks' selectors times their values."%t
    write(f'FormsT{t}',doc,IMP,gen_table(t))

def gen_t5():
    doc5="Table 5's blocks' values on the %s side, from the guest's statements."
    imp=IMP
    write('FormsT5a',doc5%'push',imp,gen_table(5,sides=(0,),with_side=False))
    write('FormsT5b',doc5%'pull',imp,pull_side(5,with_side=False))
    out=[]
    for sd in range(3):
        if sd==1:
            out.append(pull_side(5,blocks=[])); continue
        data,lit=bterms_lit(sd,5); F=FV['5'][sd]; ch,_=chain(F,D)
        bn=[f'vtB{sd}5_{bi}' for bi in range(len(ch))]
        n,txt=side_lemma(5,sd,data,ch,bn); out.append('set_option maxRecDepth 10000 in\n'+txt)
    write('FormsT5',"Table 5's forms on the three sides: the blocks' selectors times their values.",
      'LeanVM.Guest.B1.Tables.Vt.FormsT5a\npublic import LeanVM.Guest.B1.Tables.Vt.FormsT5b','\n\n'.join(out))
