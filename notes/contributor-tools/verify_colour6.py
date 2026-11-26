import argparse
from itertools import combinations, product
from pathlib import Path


def colourable_graphs(edges):
    colourable = {0}
    for colours in product(range(3), repeat=6):
        allowed = sum(1 << i for i, (a, b) in enumerate(edges) if colours[a] != colours[b])
        graph = allowed
        while graph:
            colourable.add(graph)
            graph = (graph - 1) & allowed
    return colourable


def main():
    parser = argparse.ArgumentParser(description="Replay a six-vertex 3-colourability circuit.")
    parser.add_argument("witness", nargs="?", type=Path,
                        default=Path(__file__).with_name("examples") / "colour6-212.txt")
    args = parser.parse_args()

    rows = args.witness.read_text(encoding="utf-8").splitlines()
    output = int(rows[0])
    gates = [tuple(map(int, row.split())) for row in rows[1:]]
    edges = list(combinations(range(6), 2))
    for wire, (op, a, b) in enumerate(gates, start=len(edges)):
        if op not in (0, 1) or not (0 <= a < wire and 0 <= b < wire):
            raise ValueError(f"Invalid gate at wire {wire}")
    if not 0 <= output < len(edges) + len(gates):
        raise ValueError("Invalid output wire")

    colourable = colourable_graphs(edges)
    for graph in range(1 << len(edges)):
        wires = [(graph >> i) & 1 for i in range(len(edges))]
        for op, a, b in gates:
            wires.append(wires[a] | wires[b] if op else wires[a] & wires[b])
        if (not wires[output]) != (graph in colourable):
            raise ValueError(f"Circuit disagrees with direct colouring on graph mask {graph}")
    print(f"{len(gates) + 1} gates, all {1 << len(edges)} graphs agree with direct colouring")


if __name__ == "__main__":
    main()
