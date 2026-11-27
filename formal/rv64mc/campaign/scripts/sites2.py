import re,sys,glob
target=sys.argv[1]
def short(x):
    x=x.replace('LinstrR.','').replace('Expr.','').replace('BinOp.','').replace('Reg.','').replace('Op.','').replace('0x000000000000','0x').replace('LOperand.','')
    return x
for f in sorted(glob.glob('Rv64mc/Gen/Tmpl/**/*.lean',recursive=True)):
    lines=[l.strip() for l in open(f) if 'Linstr' in l]
    ins=[l for l in lines if 'Llabel' not in l]
    for k,l in enumerate(ins):
        if ('L.%s.idx'%target) in l and ('Lcall' in l or 'Ltail' in l):
            out={}
            for r in ['x10','x11','x12']:
                for q in range(k-1,max(-1,k-40),-1):
                    x=ins[q]
                    if re.search(r'Op\.(set|load) \(Reg\.%s\)'%r, x) or 'Lcall' in x:
                        out[r]=short(x)[:110] if 'Lcall' not in x else 'CALL '+short(x)[-40:]
                        break
            print(f.split('Tmpl/')[1].replace('.lean',''),k, 'tail' if 'Ltail' in l else '')
            for r in ['x10','x11','x12']: print('   ',r,out.get(r,'?'))
