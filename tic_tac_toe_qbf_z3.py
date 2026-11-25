from pathlib import Path

import z3

# 012
# 345
# 678
type Marks = tuple[z3.ExprRef, ...]


def is_winning_board(marks: Marks) -> z3.ExprRef:
    return z3.Or(
        *[
            z3.And(*[marks[i] for i in xs])
            for xs in [
                (0, 1, 2),
                (3, 4, 5),
                (6, 7, 8),
                (0, 3, 6),
                (1, 4, 7),
                (2, 5, 8),
                (0, 4, 8),
                (2, 4, 6),
            ]
        ]
    )


def is_valid_move(
    player1_marks: Marks, player2_marks: Marks, move: tuple[z3.ExprRef]
) -> z3.ExprRef:
    cs = []
    cs.append(z3.Or(*move))
    for i in range(9):
        for j in range(i + 1, 9):
            cs.append(z3.Or(z3.Not(move[i]), z3.Not(move[j])))
    for i in range(9):
        cs.append(z3.Implies(player1_marks[i], z3.Not(move[i])))
        cs.append(z3.Implies(player2_marks[i], z3.Not(move[i])))
    return z3.And(*cs)


def problem(allow_draw: bool) -> z3.ExprRef:
    def player1(
        num_marks: int, player1_marks: Marks, player2_marks: Marks
    ) -> z3.ExprRef:
        if num_marks == 9:
            return finished(num_marks, player1_marks, player2_marks)

        move = tuple(z3.Bool(f"p1_{num_marks + 1}_{i}") for i in range(9))

        player1_marks_new = tuple(
            z3.Or(orig, v) for (orig, v) in zip(player1_marks, move)
        )

        return z3.And(
            z3.Not(is_winning_board(player2_marks)),
            z3.Or(
                is_winning_board(player1_marks),
                z3.Exists(
                    move,
                    z3.And(
                        is_valid_move(player1_marks, player2_marks, move),
                        player2(
                            num_marks + 1,
                            player1_marks_new,
                            player2_marks,
                        ),
                    ),
                ),
            ),
        )

    def player2(
        num_marks: int, player1_marks: Marks, player2_marks: Marks
    ) -> z3.ExprRef:
        if num_marks == 9:
            return finished(num_marks, player1_marks, player2_marks)

        move = tuple(z3.Bool(f"p2_{num_marks + 1}_{i}") for i in range(9))

        player2_marks_new = tuple(
            z3.Or(orig, v) for (orig, v) in zip(player2_marks, move)
        )

        return z3.Or(
            is_winning_board(player1_marks),
            z3.And(
                z3.Not(is_winning_board(player2_marks)),
                z3.ForAll(
                    move,
                    z3.Implies(
                        is_valid_move(player1_marks, player2_marks, move),
                        player1(
                            num_marks + 1,
                            player1_marks,
                            player2_marks_new,
                        ),
                    ),
                ),
            ),
        )

    def finished(
        num_marks: int, player1_marks: Marks, player2_marks: Marks
    ) -> z3.ExprRef:
        if allow_draw:
            return z3.Or(
                is_winning_board(player1_marks),
                z3.Not(is_winning_board(player2_marks)),
            )
        else:
            return is_winning_board(player1_marks)

    return player1(0, tuple([z3.BoolVal(False)] * 9), tuple([z3.BoolVal(False)] * 9))


solver = z3.Solver()
solver.append(problem(allow_draw=False))
Path("tic_tac_toe_player1_win.smt2").write_text(solver.to_smt2())
assert solver.check() == z3.unsat


solver = z3.Solver()
solver.append(problem(allow_draw=True))
Path("tic_tac_toe_player1_win_or_draw.smt2").write_text(solver.to_smt2())
assert solver.check() == z3.sat
