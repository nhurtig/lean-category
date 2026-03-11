import sys
import re


def parse_sexp(s):
    """Parse a string S-expression into a nested list."""
    tokens = re.findall(r"\(|\)|[^\s()]+", s)
    stack = []
    curr = []
    for tok in tokens:
        if tok == "(":
            stack.append(curr)
            curr = []
        elif tok == ")":
            if not stack:
                raise ValueError("Unmatched )")
            last = stack.pop()
            last.append(curr)
            curr = last
        else:
            curr.append(tok)
    if stack:
        raise ValueError("Unmatched (")
    return curr[0] if curr and len(curr) == 1 else curr


def pretty_sexp(sexp, depth=0):
    indent = "  " * depth
    if isinstance(sexp, list):
        if not sexp:
            return indent + "(\n" + indent + ")"
        s = indent + "(\n"
        for x in sexp:
            s += pretty_sexp(x, depth + 1) + "\n"
        s += indent + ")"
        return s
    else:
        return indent + str(sexp)


def sexp_to_str(sexp):
    return "\n" + pretty_sexp(sexp)


# """Convert a nested S-expression back to a string."""
# if isinstance(sexp, list):
#     return "(" + " ".join(sexp_to_str(x) for x in sexp) + ")"
# else:
#     return str(sexp)


def is_hole(x):
    return isinstance(x, str) and x.startswith("?")


import difflib


def first_difference(a, b):
    if type(a) != type(b):
        return (a, b)
    if isinstance(a, str):
        if a != b:
            return (a, b)
        else:
            return (None, None)
    if len(a) != len(b):
        return (a, b)
    for x, y in zip(a, b):
        diff = first_difference(x, y)
        if diff != (None, None):
            return diff
    return (None, None)


def compare_trees(a, b, holes, path=""):
    """Compare two S-expression trees, filling holes and reporting mismatches."""
    mismatches = []
    if is_hole(a):
        if a in holes:
            if holes[a] != sexp_to_str(b):
                diff_a, diff_b = first_difference(parse_sexp(holes[a]), b)
                mismatches.append(
                    (
                        path,
                        f"hole {a} previously unified to {holes[a]}, now to {sexp_to_str(b)}; first difference: {sexp_to_str(diff_a)} vs {sexp_to_str(diff_b)}",
                    )
                )
        else:
            holes[a] = sexp_to_str(b)
        return mismatches
    if is_hole(b):
        if b in holes:
            if holes[b] != sexp_to_str(a):
                diff_a, diff_b = first_difference(parse_sexp(holes[a]), b)
                mismatches.append(
                    (
                        path,
                        f"hole {a} previously unified to {holes[a]}, now to {sexp_to_str(b)}; first difference: {diff_a} vs {diff_b}",
                    )
                )
        else:
            holes[b] = sexp_to_str(a)
        return mismatches
    if type(a) != type(b):
        mismatches.append((path, f"type mismatch: {type(a)} vs {type(b)}"))
        return mismatches
    if isinstance(a, str):
        if a != b:
            mismatches.append((path, f"value mismatch: {a} vs {b}"))
        return mismatches
    if len(a) != len(b):
        mismatches.append((path, f"length mismatch: {len(a)} vs {len(b)}"))
        return mismatches
    for i, (x, y) in enumerate(zip(a, b)):
        mismatches.extend(compare_trees(x, y, holes, path + f"/{i}"))
    return mismatches


def main():
    if len(sys.argv) != 3:
        print("Usage: python sexp_compare.py file1 file2")
        sys.exit(1)
    with open(sys.argv[1]) as f1, open(sys.argv[2]) as f2:
        s1 = f1.read()
        s2 = f2.read()
    t1 = parse_sexp(s1)
    t2 = parse_sexp(s2)
    holes = {}
    mismatches = compare_trees(t1, t2, holes)
    print("Mismatches:")
    for path, msg in mismatches:
        print(f"{path}: {msg}")
    print("\nHole unifications:")
    for k, v in holes.items():
        print(f"{k} => {v}")


if __name__ == "__main__":
    main()
