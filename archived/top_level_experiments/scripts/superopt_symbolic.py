import z3
import random
from problem import HASH_STAGES

MASK32 = (1 << 32) - 1

def _bv(x, w): return z3.BitVecVal(x & ((1<<w)-1), w)

def target_hash(a, w):
    out = a
    mask = (1 << w) - 1
    for op1, val1, op2, op3, val3 in HASH_STAGES:
        v1 = _bv(val1, w)
        v3 = _bv(val3 % w if op3 in ("<<", ">>") else val3, w)
        if op1 == "+": t1 = out + v1
        else: t1 = out ^ v1
        if op3 == "<<": t3 = out << v3
        else: t3 = z3.LShR(out, v3)
        if op2 == "+": out = t1 + t3
        else: out = t1 ^ t3
    return out

def build_expr(a, n_ops, width, ops, dsts, src_a, src_b, src_c, consts):
    curr_val = a
    curr_tmp = z3.BitVecVal(0, width)
    for i in range(n_ops):
        sa = z3.If(src_a[i] == 0, curr_val, curr_tmp)
        sb = z3.If(src_b[i] == 0, curr_val, z3.If(src_b[i] == 1, curr_tmp, consts[i]))
        sc = z3.If(src_c[i] == 0, curr_val, z3.If(src_c[i] == 1, curr_tmp, consts[i]))
        
        res = z3.If(ops[i] == 0, sa + sb,
              z3.If(ops[i] == 1, sa ^ sb,
              z3.If(ops[i] == 2, sa << consts[i],
              z3.If(ops[i] == 3, z3.LShR(sa, consts[i]),
              sa * sb + sc)))) # muladd
        
        new_val = z3.If(dsts[i] == 0, res, curr_val)
        new_tmp = z3.If(dsts[i] == 1, res, curr_tmp)
        curr_val, curr_tmp = new_val, new_tmp
    return curr_val

def solve(n_ops, width):
    print(f"Solving for {n_ops} ops at {width} bits...")
    a = z3.BitVec('a', width)
    target = target_hash(a, width)
    
    ops = [z3.Int(f'op{i}') for i in range(n_ops)]
    dsts = [z3.Int(f'dst{i}') for i in range(n_ops)]
    src_a = [z3.Int(f'sa{i}') for i in range(n_ops)]
    src_b = [z3.Int(f'sb{i}') for i in range(n_ops)]
    src_c = [z3.Int(f'sc{i}') for i in range(n_ops)]
    consts = [z3.BitVec(f'k{i}', width) for i in range(n_ops)]
    
    s = z3.Solver()
    for i in range(n_ops):
        s.add(ops[i] >= 0, ops[i] <= 4)
        s.add(dsts[i] >= 0, dsts[i] <= 1)
        s.add(src_a[i] >= 0, src_a[i] <= 1)
        s.add(src_b[i] >= 0, src_b[i] <= 2)
        s.add(src_c[i] >= 0, src_c[i] <= 2)
        s.add(z3.Implies(z3.Or(ops[i] == 2, ops[i] == 3), srcs_b[i] == 2)) # Error here: srcs_b vs src_b
        # ... fixing ...