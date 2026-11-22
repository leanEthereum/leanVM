# Referee 75: certified upper bounds on tau*_J(rho), the limit threshold that uses only Q_2..Q_{J+1} (output 75_lp_fewJ_output.txt).
import importlib.util
spec = importlib.util.spec_from_file_location("lp75", "75_lp.py"); lp = importlib.util.module_from_spec(spec); spec.loader.exec_module(lp)
print("certified upper bounds on tau*_J (only Q_2..Q_{J+1} used)")
for lg in (2, 3, 4, 5, 7, 10):
    row = []
    for J in (1, 2, 3, 4, 7, 15):
        if J >= 2 ** lg: row.append("   -   "); continue
        row.append(f"{lp.limit_lp(2.0 ** -lg, J)[1]:.5f}")
    print(f"rate 2^-{lg}: J=1,2,3,4,7,15: " + "  ".join(row) + f"   (all j: {lp.limit_lp(2.0 ** -lg, 10**9)[1]:.5f})")
