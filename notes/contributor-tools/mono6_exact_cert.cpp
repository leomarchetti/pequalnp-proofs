#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using namespace std;

static constexpr uint64_t VAR_MASK[6] = {
    0xAAAAAAAAAAAAAAAAULL,
    0xCCCCCCCCCCCCCCCCULL,
    0xF0F0F0F0F0F0F0F0ULL,
    0xFF00FF00FF00FF00ULL,
    0xFFFF0000FFFF0000ULL,
    0xFFFFFFFF00000000ULL,
};

static inline uint64_t norm_u(bool u, uint64_t w) {
    if (u && (w & 1ULL)) return ~w;
    return w;
}

static inline uint64_t bin_op(int d, uint64_t a, uint64_t b) {
    switch (d) {
        case 0: return a & b;
        case 1: return a | b;
        case 2: return a & (~b);
        case 3: return (~a) & b;
    }
    return 0;
}

static inline bool is_proper(uint64_t w) {
    return w != 0ULL && w != ~0ULL;
}

static inline uint64_t subcube_mask(int z_mask, int o_mask) {
    uint64_t d = ~0ULL;
    for (int i = 0; i < 6; ++i) {
        if (z_mask & (1 << i)) d &= ~VAR_MASK[i];
        else if (o_mask & (1 << i)) d &= VAR_MASK[i];
    }
    return d;
}

static inline uint64_t restrict_tt(uint64_t f, int z_mask, int o_mask) {
    uint64_t res = 0;
    for (int x = 0; x < 64; ++x) {
        int y = (x & ~z_mask) | o_mask;
        if ((f >> y) & 1ULL) res |= (1ULL << x);
    }
    return res;
}

static int essential_mask(uint64_t f) {
    int m = 0;
    for (int i = 0; i < 6; ++i) {
        int step = 1 << i;
        uint64_t low = f & ~VAR_MASK[i];
        uint64_t high = (f & VAR_MASK[i]) >> step;
        if (low != high) m |= (1 << i);
    }
    return m;
}

// Find witness (r, s) for essential variable i of f
static pair<int, int> essential_pair(uint64_t f, int i) {
    int b = 1 << i;
    for (int r = 0; r < 64; ++r) {
        if ((r & b) == 0 && (((f >> r) & 1ULL) != ((f >> (r | b)) & 1ULL))) {
            return {r, r | b};
        }
    }
    return {0, 0};
}

struct SepInfo {
    vector<pair<int, int>> pairs;
    uint64_t pos_row[64], neg_row[64];
    int used_pairs = 0;

    void build(uint64_t f, int ess_mask) {
        pairs.clear();
        vector<int> pos_rows, neg_rows;
        for (int x = 0; x < 64; ++x) {
            if (x & ~ess_mask) continue;
            if ((f >> x) & 1ULL) pos_rows.push_back(x);
            else neg_rows.push_back(x);
        }
        vector<int> min_pos, max_neg;
        for (int p : pos_rows) {
            bool is_min = true;
            for (int i = 0; i < 6; ++i)
                if ((p & (1 << i)) && ((f >> (p ^ (1 << i))) & 1ULL)) { is_min = false; break; }
            if (is_min) min_pos.push_back(p);
        }
        for (int q : neg_rows) {
            bool is_max = true;
            for (int i = 0; i < 6; ++i)
                if ((ess_mask & (1 << i)) && !(q & (1 << i)) && !((f >> (q | (1 << i))) & 1ULL)) { is_max = false; break; }
            if (is_max) max_neg.push_back(q);
        }
        for (int p : min_pos)
            for (int i = 0; i < 6; ++i)
                if ((p & (1 << i)) && !((f >> (p ^ (1 << i))) & 1ULL)) pairs.push_back({p, p ^ (1 << i)});
        for (int q : max_neg)
            for (int i = 0; i < 6; ++i)
                if ((ess_mask & (1 << i)) && !(q & (1 << i)) && ((f >> (q | (1 << i))) & 1ULL)) pairs.push_back({q | (1 << i), q});
        for (int p : min_pos)
            for (int q : max_neg)
                pairs.push_back({p, q});
        sort(pairs.begin(), pairs.end());
        pairs.erase(unique(pairs.begin(), pairs.end()), pairs.end());
        used_pairs = min((int)pairs.size(), 64);
        for (int i = 0; i < used_pairs; ++i) {
            pos_row[i] = pairs[i].first;
            neg_row[i] = pairs[i].second;
        }
    }

    inline uint64_t wire_col(bool u, uint64_t w) const {
        uint64_t c = 0;
        if (!u) {
            for (int i = 0; i < used_pairs; ++i) {
                if (((w >> pos_row[i]) & 1ULL) && !((w >> neg_row[i]) & 1ULL)) c |= (1ULL << i);
            }
        } else {
            for (int i = 0; i < used_pairs; ++i) {
                if (((w >> pos_row[i]) & 1ULL) != ((w >> neg_row[i]) & 1ULL)) c |= (1ULL << i);
            }
        }
        return c;
    }
};

struct State {
    uint8_t n;
    uint64_t w[12];
    bool operator==(const State &o) const {
        if (n != o.n) return false;
        for (int i = 0; i < n; ++i) if (w[i] != o.w[i]) return false;
        return true;
    }
    bool operator<(const State &o) const {
        if (n != o.n) return n < o.n;
        for (int i = 0; i < n; ++i) if (w[i] != o.w[i]) return w[i] < o.w[i];
        return false;
    }
};

struct StateHash {
    size_t operator()(const State &s) const {
        uint64_t h = s.n * 0x9e3779b97f4a7c15ULL;
        for (int i = 0; i < s.n; ++i) {
            uint64_t x = s.w[i] + 0x9e3779b97f4a7c15ULL;
            x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
            x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
            h ^= x ^ (x >> 31);
            h *= 0x100000001b3ULL;
        }
        return (size_t)h;
    }
};

struct SubcubeBound {
    int sidx;
    uint64_t d;
    int lb;
    int z_mask, o_mask;
};

struct CircuitStep {
    int op;
    uint64_t a, b, out;
};

struct Gate {
    int op; // 0=and, 1=or, 2=not
    int a, b;
};

static inline bool is_const_on(uint64_t w, uint64_t d) {
    uint64_t m = w & d;
    return m == 0ULL || m == d;
}

// Note: in Lean `Live`, when u=true and all roots have bit 0 = 0,
// bin d a b ALREADY has bit 0 = 0 for all d in {0,1,2,3}!
// So we NEVER need `norm_u` inside the search when target also has bit 0 = 0!
// (Every monotone function with f(0)=0 has bit 0 = 0! If f(0)=1, it's constant 1!)
struct LiveSolver {
    bool u;
    uint64_t target;
    SepInfo sep;
    uint64_t all_sep_mask;
    vector<SubcubeBound> bounds;
    uint64_t node_limit;
    uint64_t nodes;
    bool aborted;

    bool record_dag = false;
    vector<unordered_set<State, StateHash>> dead;
    // Recorded branching states per k_rem (only states that were NOT pruned immediately!)
    vector<vector<State>> branch_states;
    vector<unordered_set<State, StateHash>> branch_seen;
    unordered_set<int> used_sidx;
    unordered_set<int> used_sep_idx;
    vector<CircuitStep> solution;

    bool can_reach(int cap_root, int k_rem, const State &s) {
        if (aborted) return false;
        if (s.n == 1 && s.w[0] == target) return true;
        if (k_rem == 0) return false;
        if (s.n > k_rem + 1) return false;
        for (int i = 0; i < s.n; ++i) if (s.w[i] == target) return true;

        // Rule 1: Separator cover
        uint64_t cov = 0;
        for (int i = 0; i < s.n; ++i) cov |= sep.wire_col(u, s.w[i]);
        if (cov != all_sep_mask) {
            if (record_dag) {
                uint64_t miss = all_sep_mask & ~cov;
                int p_idx = __builtin_ctzll(miss);
                used_sep_idx.insert(p_idx);
            }
            return false;
        }

        // Rule 2: Subcube projection bound: cap_root < sb.lb + count_const(sb.d, s)
        for (const auto &sb : bounds) {
            int c = 0;
            for (int i = 0; i < s.n; ++i) {
                if (is_const_on(s.w[i], sb.d)) ++c;
            }
            if (cap_root < sb.lb + c) {
                if (record_dag) used_sidx.insert(sb.sidx);
                return false;
            }
        }

        if (++nodes > node_limit) { aborted = true; return false; }
        if (dead[k_rem].count(s)) return false;

        int max_d = u ? 4 : 2;
        int n = s.n;

        // Check 1-gate hit
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                for (int d = 0; d < max_d; ++d) {
                    uint64_t out = bin_op(d, s.w[i], s.w[j]);
                    if (out == target) {
                        solution.push_back({d, s.w[i], s.w[j], out});
                        return true;
                    }
                }
            }
        }
        if (k_rem == 1) {
            dead[k_rem].insert(s);
            if (record_dag && branch_seen[k_rem].insert(s).second) branch_states[k_rem].push_back(s);
            return false;
        }

        // Branch on all canonical pairs (i < j, so s.w[i] < s.w[j] since s is sorted!)
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                for (int d = 0; d < max_d; ++d) {
                    uint64_t out = bin_op(d, s.w[i], s.w[j]);
                    if (!is_proper(out)) continue;
                    bool dup = false;
                    for (int t = 0; t < n; ++t) if (s.w[t] == out) { dup = true; break; }
                    if (dup) continue;

                    for (int ka = 0; ka <= 1; ++ka) {
                        for (int kb = 0; kb <= 1; ++kb) {
                            int new_n = n - 2 + ka + kb + 1;
                            if (new_n > k_rem || new_n > 12) continue;
                            State ns;
                            ns.n = 0;
                            for (int t = 0; t < n; ++t) {
                                if (t == i && !ka) continue;
                                if (t == j && !kb) continue;
                                ns.w[ns.n++] = s.w[t];
                            }
                            ns.w[ns.n++] = out;
                            int pos = ns.n - 1;
                            while (pos > 0 && ns.w[pos - 1] > ns.w[pos]) {
                                swap(ns.w[pos - 1], ns.w[pos]);
                                --pos;
                            }
                            if (can_reach(cap_root, k_rem - 1, ns)) {
                                solution.push_back({d, s.w[i], s.w[j], out});
                                return true;
                            }
                            if (aborted) return false;
                        }
                    }
                }
            }
        }

        dead[k_rem].insert(s);
        if (record_dag && branch_seen[k_rem].insert(s).second) branch_states[k_rem].push_back(s);
        return false;
    }

    int solve(int cap, const vector<uint64_t> &init_wires, bool rec = false, uint64_t limit = 3000000ULL) {
        all_sep_mask = (sep.used_pairs == 64) ? ~0ULL : ((1ULL << sep.used_pairs) - 1ULL);
        node_limit = limit;
        nodes = 0;
        aborted = false;
        record_dag = rec;
        solution.clear();
        dead.assign(cap + 1, {});
        if (rec) {
            branch_states.assign(cap + 1, {});
            branch_seen.assign(cap + 1, {});
            used_sidx.clear();
            used_sep_idx.clear();
        }

        State s0;
        s0.n = 0;
        for (uint64_t w : init_wires) {
            if (!is_proper(w)) continue;
            bool dup = false;
            for (int i = 0; i < s0.n; ++i) if (s0.w[i] == w) { dup = true; break; }
            if (!dup) s0.w[s0.n++] = w;
        }
        sort(s0.w, s0.w + s0.n);

        bool ok = can_reach(cap, cap, s0);
        if (aborted) return -1;
        if (ok) { reverse(solution.begin(), solution.end()); return 1; }
        return 0;
    }
};

struct SubcubeCert {
    int sidx;
    int z_mask, o_mask;
    uint64_t d;
    uint64_t g;
    int ess;
    int lb;          // proved Lower u roots g lb
    bool by_count;   // true if lb <= popcount(ess) - 1 (no DAG needed!)
    vector<pair<int, int>> used_sep;
    vector<int> child_sidx; // subcube indices used in this subcube's DAG
    vector<vector<State>> levels; // levels[0..cap]
};

static void emit_json_cert(uint64_t f, ostream &out) {
    // 1. Find exact C_mono and optimal monotone circuit
    int lb_m[729], lb_b[729];
    uint64_t mask_t[729], tt_t[729];
    int z_t[729], o_t[729];
    vector<int> by_free[7];

    for (int idx = 0; idx < 729; ++idx) {
        int tmp = idx, z = 0, o = 0, fc = 0;
        for (int i = 0; i < 6; ++i) {
            int r = tmp % 3; tmp /= 3;
            if (r == 0) ++fc;
            else if (r == 1) z |= (1 << i);
            else o |= (1 << i);
        }
        z_t[idx] = z; o_t[idx] = o;
        mask_t[idx] = subcube_mask(z, o);
        tt_t[idx] = restrict_tt(f, z, o);
        lb_m[idx] = lb_b[idx] = 0;
        by_free[fc].push_back(idx);
    }

    auto collect_sbs = [&](int idx, int ess, int *lb_arr, int &min_lb) {
        vector<SubcubeBound> sbs;
        int bz = z_t[idx], bo = o_t[idx];
        for (int sub = ess; sub > 0; sub = (sub - 1) & ess) {
            int fixed_cnt = __builtin_popcount(sub);
            for (int val = sub; ; val = (val - 1) & sub) {
                int nz = bz | (sub & ~val);
                int no = bo | val;
                int sidx = 0, p3 = 1;
                for (int i = 0; i < 6; ++i) {
                    int d3 = (nz & (1 << i)) ? 1 : ((no & (1 << i)) ? 2 : 0);
                    sidx += d3 * p3; p3 *= 3;
                }
                int slb = lb_arr[sidx];
                if (slb > 0) {
                    min_lb = max(min_lb, slb + fixed_cnt);
                    sbs.push_back({sidx, mask_t[sidx], slb, nz, no});
                }
                if (val == 0) break;
            }
        }
        // Prefer highest lb, then fewest fixed vars (easier to prove!)
        sort(sbs.begin(), sbs.end(), [](const SubcubeBound &a, const SubcubeBound &b) {
            if (a.lb != b.lb) return a.lb > b.lb;
            return __builtin_popcount(a.z_mask | a.o_mask) > __builtin_popcount(b.z_mask | b.o_mask);
        });
        return sbs;
    };

    // Solve monotone exact C_mono(f)
    vector<CircuitStep> mono_steps;
    unordered_map<uint64_t, int> m_cache;
    for (int fc = 0; fc <= 6; ++fc) {
        for (int idx : by_free[fc]) {
            uint64_t g = tt_t[idx];
            if (!is_proper(g)) { lb_m[idx] = 0; continue; }
            int ess = essential_mask(g);
            int k_ess = __builtin_popcount(ess);
            if (k_ess <= 1) { lb_m[idx] = 0; continue; }
            if (fc < 6 && m_cache.count(g)) { lb_m[idx] = m_cache[g]; continue; }
            vector<uint64_t> roots;
            for (int i = 0; i < 6; ++i) if (ess & (1 << i)) roots.push_back(VAR_MASK[i]);
            int min_lb = k_ess - 1;
            auto sbs = collect_sbs(idx, ess, lb_m, min_lb);
            LiveSolver slv; slv.u = false; slv.target = g; slv.sep.build(g, ess); slv.bounds = sbs;
            for (int cap = min_lb; cap <= 14; ++cap) {
                int r = slv.solve(cap, roots, false, 3000000ULL);
                if (r == 1) {
                    lb_m[idx] = cap;
                    m_cache[g] = cap;
                    if (fc == 6) mono_steps = slv.solution;
                    break;
                }
            }
        }
    }
    int c_mono = lb_m[0];
    int target_bin_lb = c_mono;

    // Solve binary-gate lower bounds for all subcubes (u = true)
    // Note: if restricted g has bit 0 = 1, we normalize g -> ~g because nrm true g = ~g has same binary complexity!
    unordered_map<uint64_t, int> b_cache;
    for (int fc = 0; fc <= 5; ++fc) {
        for (int idx : by_free[fc]) {
            uint64_t g = norm_u(true, tt_t[idx]);
            if (!is_proper(g)) { lb_b[idx] = 0; continue; }
            int ess = essential_mask(g);
            int k_ess = __builtin_popcount(ess);
            if (k_ess <= 1) { lb_b[idx] = 0; continue; }
            if (b_cache.count(g)) { lb_b[idx] = b_cache[g]; continue; }
            vector<uint64_t> roots;
            for (int i = 0; i < 6; ++i) if (ess & (1 << i)) roots.push_back(VAR_MASK[i]);
            int min_lb = k_ess - 1;
            auto sbs = collect_sbs(idx, ess, lb_b, min_lb);
            LiveSolver slv; slv.u = true; slv.target = g; slv.sep.build(g, ess); slv.bounds = sbs;
            for (int cap = min_lb; cap <= 12; ++cap) {
                int r = slv.solve(cap, roots, false, 1000000ULL);
                if (r == 1) { lb_b[idx] = cap; b_cache[g] = cap; break; }
            }
        }
    }

    // Now recursively build certificates starting from root (sidx = 0, needed_lb = target_bin_lb)
    map<int, SubcubeCert> certs;
    function<bool(int, int)> build_cert = [&](int idx, int needed_lb) -> bool {
        if (certs.count(idx) && certs[idx].lb >= needed_lb) return true;
        uint64_t g = norm_u(true, tt_t[idx]);
        int ess = essential_mask(g);
        int k_ess = __builtin_popcount(ess);

        SubcubeCert cert;
        cert.sidx = idx;
        cert.z_mask = z_t[idx];
        cert.o_mask = o_t[idx];
        cert.d = mask_t[idx];
        cert.g = g;
        cert.ess = ess;
        cert.lb = needed_lb;

        if (needed_lb <= k_ess - 1) {
            cert.by_count = true;
            certs[idx] = cert;
            return true;
        }
        cert.by_count = false;

        vector<uint64_t> roots;
        for (int i = 0; i < 6; ++i) if (ess & (1 << i)) roots.push_back(VAR_MASK[i]);
        int dummy_min = k_ess - 1;
        auto sbs = collect_sbs(idx, ess, lb_b, dummy_min);
        // Prefer count-only subcubes first if their lb is good, to minimize recursive DAGs!
        LiveSolver slv;
        slv.u = true;
        slv.target = g;
        slv.sep.build(g, ess);
        slv.bounds = sbs;

        int cap = needed_lb - 1;
        int r = slv.solve(cap, roots, true, 3000000ULL);
        if (r != 0) return false; // failed to prove impossibility!

        for (int pidx : slv.used_sep_idx) cert.used_sep.push_back(slv.sep.pairs[pidx]);
        sort(cert.used_sep.begin(), cert.used_sep.end());

        for (int cs : slv.used_sidx) cert.child_sidx.push_back(cs);
        sort(cert.child_sidx.begin(), cert.child_sidx.end());
        cert.levels = slv.branch_states;

        // Recursively certify every child subcube used!
        for (int cs : cert.child_sidx) {
            if (!build_cert(cs, lb_b[cs])) return false;
        }
        certs[idx] = std::move(cert);
        return true;
    };

    bool ok = build_cert(0, target_bin_lb);
    if (!ok) {
        out << "{\"ok\": false}\n";
        return;
    }

    // Convert mono_steps to concrete gate list
    vector<uint64_t> wval(6);
    for (int i = 0; i < 6; ++i) wval[i] = VAR_MASK[i];
    vector<Gate> mono_gates;
    auto find_w = [&](uint64_t v) {
        for (int i = 0; i < (int)wval.size(); ++i) if (wval[i] == v) return i;
        return -1;
    };
    for (auto &st : mono_steps) {
        int ia = find_w(st.a), ib = find_w(st.b);
        mono_gates.push_back({st.op, ia, ib});
        wval.push_back(st.out);
    }
    int out_wire = find_w(f);

    // Topological order of certs (children before parents, i.e., ascending free_cnt)
    vector<int> order;
    for (auto &[k, v] : certs) order.push_back(k);
    sort(order.begin(), order.end(), [&](int a, int b) {
        int fa = 6 - __builtin_popcount(z_t[a] | o_t[a]);
        int fb = 6 - __builtin_popcount(z_t[b] | o_t[b]);
        if (fa != fb) return fa < fb;
        return a < b;
    });

    int total_dag_states = 0;
    for (int k : order) for (auto &lv : certs[k].levels) total_dag_states += (int)lv.size();

    out << "{\n";
    out << "  \"ok\": true,\n";
    out << "  \"tt_hex\": \"" << hex << setw(16) << setfill('0') << f << dec << "\",\n";
    out << "  \"c_mono\": " << c_mono << ",\n";
    out << "  \"target_bin_lb\": " << target_bin_lb << ",\n";
    out << "  \"total_dag_states\": " << total_dag_states << ",\n";
    out << "  \"num_certs\": " << order.size() << ",\n";
    out << "  \"out_wire\": " << out_wire << ",\n";
    out << "  \"mono_gates\": [";
    for (size_t i = 0; i < mono_gates.size(); ++i) {
        if (i) out << ", ";
        out << "[" << mono_gates[i].op << ", " << mono_gates[i].a << ", " << mono_gates[i].b << "]";
    }
    out << "],\n";
    out << "  \"certs\": [\n";
    for (size_t ci = 0; ci < order.size(); ++ci) {
        const auto &c = certs[order[ci]];
        out << "    {\n";
        out << "      \"sidx\": " << c.sidx << ", \"z\": " << c.z_mask << ", \"o\": " << c.o_mask
            << ", \"d\": \"" << hex << setw(16) << setfill('0') << c.d
            << "\", \"g\": \"" << setw(16) << setfill('0') << c.g << dec
            << "\", \"ess\": " << c.ess << ", \"lb\": " << c.lb
            << ", \"by_count\": " << (c.by_count ? "true" : "false") << ",\n";
        // Essential pairs
        out << "      \"ess_pairs\": [";
        bool first = true;
        for (int i = 0; i < 6; ++i) {
            if (c.ess & (1 << i)) {
                auto [r, s] = essential_pair(c.g, i);
                if (!first) out << ", ";
                first = false;
                out << "[" << i << ", " << r << ", " << s << "]";
            }
        }
        out << "],\n";
        out << "      \"sep_pairs\": [";
        for (size_t i = 0; i < c.used_sep.size(); ++i) {
            if (i) out << ", ";
            out << "[" << c.used_sep[i].first << ", " << c.used_sep[i].second << "]";
        }
        out << "],\n";
        out << "      \"children\": [";
        for (size_t i = 0; i < c.child_sidx.size(); ++i) {
            if (i) out << ", ";
            out << c.child_sidx[i];
        }
        out << "],\n";
        out << "      \"levels\": [";
        for (size_t lv = 0; lv < c.levels.size(); ++lv) {
            if (lv) out << ", ";
            out << "[";
            for (size_t si = 0; si < c.levels[lv].size(); ++si) {
                if (si) out << ", ";
                out << "[";
                for (int wi = 0; wi < c.levels[lv][si].n; ++wi) {
                    if (wi) out << ", ";
                    out << "\"0x" << hex << c.levels[lv][si].w[wi] << dec << "\"";
                }
                out << "]";
            }
            out << "]";
        }
        out << "]\n";
        out << "    }" << (ci + 1 < order.size() ? "," : "") << "\n";
    }
    out << "  ]\n";
    out << "}\n";
}

int main(int argc, char **argv) {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    if (argc < 2) {
        cerr << "Usage: mono6_cert <tt_hex> [out.json]\n";
        return 1;
    }
    uint64_t f = strtoull(argv[1], nullptr, 16);
    if (argc >= 3) {
        ofstream fout(argv[2]);
        emit_json_cert(f, fout);
    } else {
        emit_json_cert(f, cout);
    }
    return 0;
}
