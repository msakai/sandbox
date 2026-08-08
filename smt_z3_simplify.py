#!/usr/bin/env python3
"""Read an SMT-LIB2 file, apply a tactic (default: simplify), and write the
result back as SMT-LIB2.
"""
import argparse
import z3


def apply_tactic(in_path: str, out_path: str, tactic_name: str = "simplify") -> None:
    ctx = z3.Context()

    # parse_smt2_file returns an AstVector of the (assert ...) formulas.
    # set-logic / check-sat / get-model などのコマンドは失われる点に注意。
    fmls = z3.parse_smt2_file(in_path, ctx=ctx)

    goal = z3.Goal(ctx=ctx)
    goal.add(fmls)

    result = z3.Tactic(tactic_name, ctx=ctx)(goal)  # -> ApplyResult

    solver = z3.Solver(ctx=ctx)
    if len(result) == 0:
        # サブゴールが 0 個 = unsat が確定
        solver.add(z3.BoolVal(False, ctx))
    elif len(result) == 1:
        # トップレベルの連言構造を保ったまま assert を並べる
        solver.add(*list(result[0]))
    else:
        # サブゴール同士は選言 (どれか一つが sat なら元も sat)
        solver.add(z3.Or([sg.as_expr() for sg in result]))

    with open(out_path, "w") as f:
        f.write(solver.to_smt2())


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("input")
    p.add_argument("output")
    p.add_argument("-t", "--tactic", default="simplify")
    a = p.parse_args()
    apply_tactic(a.input, a.output, a.tactic)
