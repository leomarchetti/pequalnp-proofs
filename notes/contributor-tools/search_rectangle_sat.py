import argparse
import json
import re
import subprocess
from pathlib import Path


def encode(rows, width, limit, colour):
    clauses = []
    variables = 0

    def fresh():
        nonlocal variables
        variables += 1
        return variables

    row_membership = [[fresh() for _ in rows] for _ in range(limit)]
    col_membership = [[fresh() for _ in range(width)] for _ in range(limit)]
    for i, row in enumerate(rows):
        for j in range(width):
            if bool(row & (1 << j)) != colour:
                clauses.extend([-rs[i], -cs[j]] for rs, cs in zip(row_membership, col_membership))
                continue
            covering = [fresh() for _ in range(limit)]
            clauses.append(covering)
            for item, rs, cs in zip(covering, row_membership, col_membership):
                clauses.extend(([-item, rs[i]], [-item, cs[j]]))

    rows_and_cols = [rs + cs for rs, cs in zip(row_membership, col_membership)]
    for first, second in zip(rows_and_cols, rows_and_cols[1:]):
        equal_prefix = fresh()
        clauses.append([equal_prefix])
        for a, b in zip(first, second):
            clauses.append([-equal_prefix, a, -b])
            longer_prefix = fresh()
            clauses.extend(([-longer_prefix, equal_prefix], [-longer_prefix, -a, b],
                            [-longer_prefix, a, -b], [-equal_prefix, -a, -b, longer_prefix],
                            [-equal_prefix, a, b, longer_prefix]))
            equal_prefix = longer_prefix
    return variables, clauses, row_membership, col_membership


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('snapshot', type=Path)
    parser.add_argument('gap')
    parser.add_argument('cadical', type=Path)
    parser.add_argument('--seconds', type=int, default=45)
    parser.add_argument('--output-dir', type=Path, default=Path('.pnp/solver'))
    args = parser.parse_args()
    row = next((g for g in json.loads(args.snapshot.read_bytes())['gaps'] if g['id'] == args.gap), None)
    if row is None:
        parser.error(f'{args.gap} is absent from the supplied snapshot')
    statement = row['statement']
    shape = re.search(r'Finset \(Fin (\d+)\) × Finset \(Fin (\d+)\)\), L.length ≤ (\d+)', statement)
    spec = re.search(r'\[([\d, ]+)\] : List ℕ\).*?testBit j.val = (true|false)', statement)
    if not statement.startswith('∃ L :') or shape is None or spec is None:
        raise ValueError('Expected a positive rectangle-cover statement')
    height, width, limit = map(int, shape.groups())
    rows = tuple(map(int, spec[1].split(',')))
    assert len(rows) == height
    colour = spec[2] == 'true'
    count, clauses, rs, cs = encode(rows, width, limit, colour)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    path = args.output_dir / f'{args.gap}-rectangle.cnf'
    with path.open('w', newline='\n') as file:
        file.write(f'p cnf {count} {len(clauses)}\n')
        file.writelines(' '.join(map(str, clause)) + ' 0\n' for clause in clauses)
    try:
        solved = subprocess.run([str(args.cadical), '-q', str(path)], text=True,
                                capture_output=True, timeout=args.seconds)
    except subprocess.TimeoutExpired:
        print(f'{args.gap}: timed out after {args.seconds}s')
        return
    if solved.returncode != 10:
        print(f'{args.gap}: {"UNSAT" if solved.returncode == 20 else f"solver exit {solved.returncode}"}')
        return
    selected = {int(token) for line in solved.stdout.splitlines() if line.startswith('v ')
                for token in line[2:].split() if int(token) > 0}
    rectangles = [([i for i, item in enumerate(r) if item in selected],
                   [j for j, item in enumerate(c) if item in selected]) for r, c in zip(rs, cs)]
    rectangles = [(r, c) for r, c in rectangles if r and c]
    expected = {(i, j) for i, value in enumerate(rows) for j in range(width)
                if bool(value & (1 << j)) == colour}
    if {(i, j) for r, c in rectangles for i in r for j in c} != expected:
        raise ValueError('Solver output failed independent rectangle verification')
    path.with_suffix('.witness.json').write_text(json.dumps(rectangles), encoding='utf-8')
    print(f'{args.gap}: verified cover by {len(rectangles)} rectangles')


if __name__ == '__main__':
    main()
