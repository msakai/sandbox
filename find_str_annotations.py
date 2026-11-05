import ast
import sys
from pathlib import Path


def iter_annotations(tree):
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            args = node.args
            all_args = args.posonlyargs + args.args + args.kwonlyargs
            if args.vararg:
                all_args.append(args.vararg)
            if args.kwarg:
                all_args.append(args.kwarg)
            for a in all_args:
                if a.annotation:
                    yield a.annotation
            if node.returns:
                yield node.returns
        elif isinstance(node, ast.AnnAssign):
            yield node.annotation


def has_string(ann):
    # Detects not only “Foo” but also the contents inside list["Foo"] and “Foo” | None
    return any(
        isinstance(n, ast.Constant) and isinstance(n.value, str) for n in ast.walk(ann)
    )


def main(paths):
    for root in paths:
        files = [Path(root)] if Path(root).is_file() else Path(root).rglob("*.py")
        for f in files:
            try:
                tree = ast.parse(f.read_text(encoding="utf-8"), str(f))
            except SyntaxError as e:
                print(f"{f}: SyntaxError: {e}", file=sys.stderr)
                continue
            for ann in iter_annotations(tree):
                if has_string(ann):
                    print(f"{f}:{ann.lineno}:{ann.col_offset}: {ast.unparse(ann)}")


if __name__ == "__main__":
    main(sys.argv[1:] or ["."])
