import argparse
import json
import re
from pathlib import Path

CORE_TMPL = Path(__file__).with_name("mono6_core.lean.tmpl")


def strip_comments(src: str) -> str:
    out = []
    for line in src.splitlines():
        s = line.lstrip()
        if s.startswith("--"):
            continue
        if "--" in line:
            line = line.split("--", 1)[0].rstrip()
        out.append(line)
    # Collapse >2 consecutive blank lines
    res = "\n".join(out)
    res = re.sub(r"\n{3,}", "\n\n", res).strip() + "\n"
    return res


def hash_state(ws):
    acc = 0
    for w in ws:
        acc = acc * 31 + (w & 255) + ((w >> 16) & 255)
    return acc


def build_buckets(states):
    # 16 x 16 nested list of states
    tbl = [[[] for _ in range(16)] for _ in range(16)]
    for st in states:
        h = hash_state(st)
        r = h & 15
        c = (h >> 4) & 15
        tbl[r][c].append(st)
    return tbl


def fmt_sig(w: int) -> str:
    return f"(0x{w:x} : Sig)"


def fmt_state(st) -> str:
    return "[" + ", ".join(f"0x{w:x}" for w in st) + "]"


def fmt_bkt_row(row) -> str:
    return "[" + ", ".join("[" + ", ".join(fmt_state(st) for st in bkt) + "]" for bkt in row) + "]"


def restrict_tt(f: int, z: int, o: int) -> int:
    res = 0
    for x in range(64):
        y = (x & (~z & 63)) | o
        if (f >> y) & 1:
            res |= (1 << x)
    return res


def generate_lean(gap: dict, cert: dict, out_path: Path):
    mod = gap["module"]
    stmt = gap["statement"].strip()
    tt_hex = cert["tt_hex"]
    tt = int(tt_hex, 16)
    c_mono = cert["c_mono"]
    target_bin_lb = cert["target_bin_lb"]
    out_wire = cert["out_wire"]
    mono_gates = cert["mono_gates"]
    certs = cert["certs"]

    core = strip_comments(CORE_TMPL.read_text(encoding="utf-8"))
    core = core.replace("__NAMESPACE__", mod)
    # Remove trailing "end Core\nend <mod>" so we can insert proof inside Core & mod
    marker = f"end Core\nend {mod}"
    assert core.rstrip().endswith(marker), "Core template must end with end Core / end __NAMESPACE__"
    body_prefix = core.rstrip()[: -len(marker)]

    lines = [body_prefix]

    cert_by_sidx = {c["sidx"]: c for c in certs}

    for c in certs:
        sidx = c["sidx"]
        z = c["z"]
        o = c["o"]
        g_int = int(c["g"], 16)
        ess = c["ess"]
        lb = c["lb"]
        by_count = c["by_count"]
        ess_pairs = c["ess_pairs"]

        lines.append(f"def c{sidx}_roots : List Sig := maskVars {ess}")
        lines.append(f"def c{sidx}_T : Sig := 0x{g_int:x}")
        es_elems = ", ".join(
            f"(xVars.getD {i} zero, ⟨{r}, by decide⟩, ⟨{s}, by decide⟩)"
            for i, r, s in ess_pairs
        )
        lines.append(f"def c{sidx}_es : List (Sig × Row × Row) := [{es_elems}]")

        if by_count:
            lines.append(f"theorem c{sidx}_lower : Lower true c{sidx}_roots c{sidx}_T {lb} := by")
            lines.append(f"  have h := lower_of_count (u := true) (by unfold proper; decide +kernel : proper c{sidx}_T) c{sidx}_es (by decide +kernel)")
            lines.append(f"  have hle : {lb} ≤ (c{sidx}_es.map Prod.fst).toFinset.card - 1 := by decide +kernel")
            lines.append(f"  exact fun p bank hr ha => hle.trans (h p bank hr ha)")
            lines.append("")
            continue

        cap = lb - 1
        sep_elems = ", ".join(f"(⟨{p}, by decide⟩, ⟨{q}, by decide⟩)" for p, q in c["sep_pairs"])
        lines.append(f"def c{sidx}_sep : List (Row × Row) := [{sep_elems}]")
        lines.append(f"theorem c{sidx}_sep_ok : c{sidx}_sep.all (fun p => bit p.1 c{sidx}_T && !(bit p.2 c{sidx}_T)) = true := by decide +kernel")

        children = c["children"]
        sl_elems = ", ".join(
            f"(0x{int(cert_by_sidx[cs]['d'], 16):x}, {cert_by_sidx[cs]['lb']})"
            for cs in children
        )
        lines.append(f"def c{sidx}_slices : List (Sig × Nat) := [{sl_elems}]")
        lines.append(f"theorem c{sidx}_slices_ok : ∀ sl ∈ c{sidx}_slices, Slice true c{sidx}_roots c{sidx}_T sl.1 sl.2 := by")
        if not children:
            lines.append("  intro sl hsl; cases hsl")
        else:
            lines.append("  intro sl hsl")
            lines.append("  simp only [c" + str(sidx) + "_slices, List.mem_cons, List.not_mem_nil, or_false] at hsl")
            rc_pat = " | ".join(["rfl"] * len(children))
            lines.append(f"  rcases hsl with {rc_pat}")
            for cs in children:
                cc = cert_by_sidx[cs]
                cz, co = cc["z"], cc["o"]
                cg = int(cc["g"], 16)
                ren_val = restrict_tt(g_int, cz, co)
                if ren_val == cg:
                    heq_term = "(Or.inl (by decide +kernel))"
                elif ren_val == (~cg & ((1 << 64) - 1)):
                    heq_term = "(Or.inr ⟨rfl, by decide +kernel⟩)"
                else:
                    raise RuntimeError(f"Mismatch renameSig on sidx={sidx} -> cs={cs}: {ren_val:x} vs {cg:x}")
                lines.append(
                    f"  · exact slice_of_lower (u := true) (z := {cz}) (o := {co}) "
                    f"(by decide +kernel) {heq_term} (by decide +kernel) "
                    f"(by unfold proper; decide +kernel) c{cs}_lower"
                )

        levels = c["levels"]
        # Level 1..cap
        for k_rem in range(1, cap + 1):
            raw_states = [[int(x, 16) for x in st] for st in levels[k_rem]]
            tbl = build_buckets(raw_states)
            for r_idx in range(16):
                if any(tbl[r_idx]):
                    lines.append(f"def c{sidx}_t{k_rem}_r{r_idx} : List (List (List Sig)) := {fmt_bkt_row(tbl[r_idx])}")
            row_refs = ", ".join(
                f"c{sidx}_t{k_rem}_r{r_idx}" if any(tbl[r_idx]) else "[]"
                for r_idx in range(16)
            )
            lines.append(f"def c{sidx}_tbl_{k_rem} : List (List (List (List Sig))) := [{row_refs}]")

            if k_rem == 1:
                next_mem = f"(fun ch => !ch.contains c{sidx}_T)"
            else:
                next_mem = f"(fun ch => quickPrune true {cap} {k_rem - 1} c{sidx}_sep c{sidx}_slices ch || memBucket c{sidx}_tbl_{k_rem - 1} ch)"

            # Verify each non-empty outer row individually with decide +kernel
            non_empty_rows = [r_idx for r_idx in range(16) if any(tbl[r_idx])]
            for r_idx in non_empty_rows:
                lines.append("set_option maxRecDepth 32768 in")
                lines.append("set_option maxHeartbeats 0 in")
                lines.append(
                    f"theorem c{sidx}_ok_{k_rem}_r{r_idx} : "
                    f"c{sidx}_t{k_rem}_r{r_idx}.all (fun bkt => bkt.all (checkState true c{sidx}_T {cap} {k_rem} c{sidx}_sep c{sidx}_slices {next_mem})) = true := by decide +kernel"
                )

            lines.append(f"theorem c{sidx}_lvl_{k_rem} : ∀ ch, memBucket c{sidx}_tbl_{k_rem} ch = true → ImpossibleFrom true c{sidx}_roots c{sidx}_T {cap} {k_rem} ch := by")
            lines.append("  intro ch hch")
            lines.append(f"  apply memBucket_sound c{sidx}_tbl_{k_rem} (ImpossibleFrom true c{sidx}_roots c{sidx}_T {cap} {k_rem}) _ hch")
            lines.append("  intro row hrow bkt hbkt ws hws")
            lines.append("  have hcs : checkState true c" + str(sidx) + f"_T {cap} {k_rem} c{sidx}_sep c{sidx}_slices {next_mem} ws = true := by")
            if not non_empty_rows:
                lines.append(f"    simp only [c{sidx}_tbl_{k_rem}, List.mem_cons, List.not_mem_nil, or_false] at hrow")
                lines.append("    rcases hrow with " + " | ".join(["rfl"] * 16) + " <;> cases hbkt")
            else:
                lines.append(f"    simp only [c{sidx}_tbl_{k_rem}, List.mem_cons, List.not_mem_nil, or_false] at hrow")
                lines.append("    rcases hrow with " + " | ".join(["rfl"] * 16))
                for r_idx in range(16):
                    if r_idx in non_empty_rows:
                        lines.append(f"    · exact List.all_eq_true.mp (List.all_eq_true.mp c{sidx}_ok_{k_rem}_r{r_idx} bkt hbkt) ws hws")
                    else:
                        lines.append("    · cases hbkt")
            lines.append(f"  refine checkState_sound (by omega) c{sidx}_sep_ok c{sidx}_slices_ok ?_ hcs")
            lines.append("  intro ch' hnd' hmem'")
            if k_rem == 1:
                lines.append("  apply impossible_zero")
                lines.append("  intro hm; have hc : ch'.contains c" + str(sidx) + "_T = true := List.contains_iff_mem.mpr hm; rw [hc] at hmem'; exact Bool.noConfusion hmem'")
            else:
                lines.append("  simp only [Bool.or_eq_true] at hmem'")
                lines.append("  rcases hmem' with hq | hm")
                lines.append(f"  · exact quickPrune_sound hnd' (by omega) c{sidx}_sep_ok c{sidx}_slices_ok hq")
                lines.append(f"  · exact c{sidx}_lvl_{k_rem - 1} ch' hm")

        # Root impossibility at cap
        lines.append(f"theorem c{sidx}_lower : Lower true c{sidx}_roots c{sidx}_T {lb} := by")
        lines.append(f"  refine lower_of_impossible (cap := {cap}) (by unfold proper; decide +kernel) c{sidx}_es (by decide +kernel) (by decide +kernel) ?_")
        if cap == 0:
            lines.append(f"  exact impossible_zero (by decide +kernel)")
        else:
            var6_hex = [
                "aaaaaaaaaaaaaaaa", "cccccccccccccccc", "f0f0f0f0f0f0f0f0",
                "ff00ff00ff00ff00", "ffff0000ffff0000", "ffffffff00000000",
            ]
            root_ws = sorted(int(var6_hex[i], 16) for i in range(6) if (ess & (1 << i)))
            root_in_lvl = any([int(x, 16) for x in st] == root_ws for st in levels[cap])
            if root_in_lvl:
                lines.append(f"  exact c{sidx}_lvl_{cap} c{sidx}_roots (by decide +kernel)")
            else:
                lines.append(f"  exact quickPrune_sound (sortedStrict_nodup (by decide +kernel : isSortedStrict c{sidx}_roots = true)) le_rfl c{sidx}_sep_ok c{sidx}_slices_ok (by decide +kernel)")
        lines.append("")

    # Lift c0_lower to xVars if ess != 63
    c0 = cert_by_sidx[0]
    if c0["ess"] == 63:
        lines.append(f"theorem rootLower : Lower true xVars c0_T {target_bin_lb} := c0_lower")
    else:
        z_drop = 63 ^ c0["ess"]
        lines.append(f"theorem rootLower : Lower true xVars c0_T {target_bin_lb} := by")
        lines.append("  intro p bank hr ha")
        lines.append(f"  have hsl : Slice true xVars c0_T 0xffffffffffffffff {target_bin_lb} := by")
        lines.append(f"    have hdom : ∀ r : Row, bit (restrictRow {z_drop} 0 r) 0xffffffffffffffff = true := by decide +kernel")
        lines.append(f"    exact slice_of_lower (u := true) (z := {z_drop}) (o := 0) hdom (Or.inl (by decide +kernel)) (by decide +kernel) (by unfold proper; decide +kernel) c0_lower")
        lines.append("  obtain ⟨f, base, _, hroots, _, hlo⟩ := hsl")
        lines.append("  obtain ⟨bank', hr', hsub⟩ := restrict_reach f hr (fun a ha => by obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha; exact hroots w hw)")
        lines.append("  have hsubM : ∀ x ∈ bank.map (restrictRows f), Available true bank' x := fun x hx => by obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx; exact hsub v hv")
        lines.append("  exact hlo p bank' hr' (avail_trans hsubM (restrict_avail f ha))")

    lines.append("end Core")
    lines.append("")
    lines.append("open Core")
    lines.append("")

    # Target function matching the exact statement
    m_fn = re.search(r"(fun x : Fin 6 → Bool => Nat\.testBit [^\)]+\)\s*\(∑ i : Fin 6, if x i then 2 \^ \(i : ℕ\) else 0\))", stmt)
    if not m_fn:
        raise RuntimeError(f"Could not extract target function from statement: {stmt}")
    fn_expr = m_fn.group(1)

    lines.append(f"def targetFn : (Fin 6 → Bool) → Bool := {fn_expr}")
    lines.append("set_option maxRecDepth 12000 in")
    lines.append("set_option maxHeartbeats 0 in")
    lines.append("theorem matchTarget : ∀ r : Row, bit r c0_T = targetFn (sampleRow r) := by decide +kernel")

    gate_strs = []
    for op, a, b in mono_gates:
        op_name = "GateOp.and" if op == 0 else "GateOp.or"
        gate_strs.append(f"⟨{op_name}, [{a}, {b}]⟩")
    lines.append(f"def witnessGates : List Gate := [{', '.join(gate_strs)}]")
    lines.append(f"def witnessCirc : Circuit := ⟨witnessGates, {out_wire}⟩")
    lines.append("theorem witnessMono : Monotone2 witnessCirc := by")
    lines.append("  intro g hg")
    lines.append("  simp only [witnessCirc, witnessGates, List.mem_cons, List.not_mem_nil, or_false] at hg")
    if mono_gates:
        rc_g = " | ".join(["rfl"] * len(mono_gates))
        lines.append(f"  rcases hg with {rc_g} <;> simp")
    else:
        lines.append("  cases hg")
    lines.append("set_option maxRecDepth 12000 in")
    lines.append("set_option maxHeartbeats 0 in")
    lines.append("theorem witnessEval : ∀ x : Fin 6 → Bool, witnessCirc.eval (List.ofFn x) = targetFn x := by decide +kernel")
    lines.append("")
    lines.append(f"end {mod}")
    lines.append("")
    lines.append(f"theorem {mod} : ({stmt}) := by")
    lines.append("  intro s hcs")
    lines.append("  obtain ⟨C, hfit, hsz, hev⟩ := hcs")
    lines.append("  by_cases hnot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not")
    lines.append("  · have hbin := " + f"{mod}.Core.binaryLower_of_lower {mod}.Core.c0_T {mod}.targetFn {target_bin_lb} (by unfold {mod}.Core.proper; decide +kernel) (by decide +kernel) {mod}.matchTarget {mod}.Core.rootLower C hfit hev")
    lines.append("    obtain ⟨g, hg, hop⟩ := hnot")
    lines.append("    have hextra : C.gates.countP (fun t => !" + f"{mod}.Core.isNot t) < C.gates.length := by")
    lines.append("      by_contra! hge")
    lines.append("      have hall := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length hge) g hg")
    lines.append(f"      simp [{mod}.Core.isNot, hop] at hall")
    lines.append(f"    have hwl : {mod}.witnessCirc.size = {c_mono} := rfl")
    lines.append("    have hcsz : C.size = C.gates.length := rfl")
    lines.append(f"    exact ⟨{mod}.witnessCirc, {mod}.witnessMono, by omega, {mod}.witnessEval⟩")
    lines.append("  · refine ⟨C, ?_, hsz, hev⟩")
    lines.append("    intro g hg")
    lines.append("    obtain ⟨ho, hl⟩ := hfit g hg")
    lines.append("    refine ⟨?_, hl⟩")
    lines.append("    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢")
    lines.append("    rcases ho with h | h | h")
    lines.append("    · exact Or.inl h")
    lines.append("    · exact Or.inr h")
    lines.append("    · exact absurd ⟨g, hg, h⟩ hnot")

    final_src = "\n".join(lines) + "\n"
    out_path.write_text(final_src, encoding="utf-8", newline="\n")
    print(f"Wrote {out_path} ({len(final_src)} bytes, {final_src.count(chr(10))} lines)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate a positive mono6 proof from a circuit certificate.")
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("gap_id")
    parser.add_argument("certificate", type=Path)
    parser.add_argument("out_file", type=Path)
    args = parser.parse_args()
    snapshot = json.loads(args.snapshot.read_bytes())
    gap = next((item for item in snapshot["gaps"] if item["id"] == args.gap_id), None)
    if gap is None or not gap["statement"].lstrip().startswith("∀"):
        parser.error("Expected the ID of a positive mono6 statement in the snapshot")
    cert = json.loads(args.certificate.read_bytes())
    if not cert["ok"]:
        parser.error("The search did not produce a complete certificate")
    generate_lean(gap, cert, args.out_file)
