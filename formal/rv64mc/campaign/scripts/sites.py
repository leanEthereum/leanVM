import re,sys,glob
target=sys.argv[1]  # memcpy or memmove
N=int(sys.argv[2]) if len(sys.argv)>2 else 10
for f in sorted(glob.glob('Rv64mc/Gen/Tmpl/**/*.lean',recursive=True)):
    lines=[l.strip() for l in open(f) if 'Linstr' in l]
    ins=[l for l in lines if 'Llabel' not in l]
    for k,l in enumerate(ins):
        if ('L.%s.idx'%target) in l and ('Lcall' in l or 'Ltail' in l):
            print('==',f.split('Tmpl/')[1],k)
            for x in ins[max(0,k-N):k+1]:
                x=x.replace('LinstrR.','').replace('Expr.','').replace('BinOp.','').replace('Reg.','').replace('0x000000000000','0x')
                print('   ',x[:150])
