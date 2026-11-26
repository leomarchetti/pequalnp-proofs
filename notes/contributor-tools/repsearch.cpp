// Exact search for "represents" semantics (PEqualNP.Represents): inputs x_0..x_{n-1}, y_0..y_{m-1};
// a wire is a relation on [n]x[m] (bit u*m+v); x_u = row u, y_v = column v. Target relation A.
// Gates AND2/OR2 (and NOT1 if allowNot). Every gate is read later or is the output (last gate);
// no duplicate or constant wires; canonical topological order. Parallel over 2-gate prefixes.
// Usage: repsearch n m <hex A> <size> <allowNot 0/1>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <atomic>
#include <omp.h>
typedef uint64_t T;
static int NI, S, allowNot; static T target, FULL;
static std::atomic<int> found(0);
struct G { int op, a, b; };
struct St { T w[64]; int reads[64]; bool isnot[64]; G g[64]; int n; long long cnt; };
static inline long key(const G& x) { return ((long)x.op * 64 + x.a) * 64 + (x.b + 1); }
static void report(St& s) {
  if (found.exchange(1)) return;
  #pragma omp critical
  { printf("FOUND size %d\n", s.n - NI);
    for (int j = NI; j < s.n; j++) printf("%d %d %d\n", s.g[j].op, s.g[j].a, s.g[j].b);
    fflush(stdout); }
}
static inline T val(const St& s, const G& x) {
  return x.op == 0 ? (s.w[x.a] & s.w[x.b]) : x.op == 1 ? (s.w[x.a] | s.w[x.b]) : (~s.w[x.a] & FULL);
}
static void apply(St& s, const G& x) {
  int j = s.n; s.g[j] = x; s.w[j] = val(s, x); s.isnot[j] = x.op == 2; s.reads[j] = 0;
  s.reads[x.a]++; if (x.b >= 0) s.reads[x.b]++; s.n++;
}
static void unapply(St& s) { s.n--; G& x = s.g[s.n]; s.reads[x.a]--; if (x.b >= 0) s.reads[x.b]--; }
static void expand(St& s, std::vector<G>* col) {
  if (found) return;
  s.cnt++;
  int used = s.n - NI, r = S - used;
  int unused = 0; for (int i = NI; i < s.n; i++) if (!s.reads[i]) unused++;
  if (unused > r + 1 || r <= 0) return;
  bool last = r == 1;
  long pk = s.n > NI ? key(s.g[s.n - 1]) : -1; int prev = s.n - 1;
  for (int op = 0; op < (allowNot ? 3 : 2); op++)
  for (int b = (op == 2 ? -1 : 1); b < (op == 2 ? 0 : s.n); b++)
  for (int a = 0; a < (op == 2 ? s.n : b); a++) {
    G x{op, a, b};
    if (op == 2 && s.isnot[a]) continue;
    if (s.n > NI && a != prev && b != prev && key(x) <= pk) continue;
    T v = val(s, x);
    if (last) {
      if (v != target) continue;
      int un = unused - (a >= NI && !s.reads[a]) - (b >= NI && !s.reads[b]);
      if (un) continue;
      s.g[s.n] = x; s.n++; report(s); s.n--; return;
    }
    if (v == 0 || v == FULL) continue;
    bool d = false; for (int i = 0; i < s.n; i++) if (s.w[i] == v) { d = true; break; }
    if (d) continue;
    if (col) { col->push_back(x); continue; }
    apply(s, x); expand(s, nullptr); unapply(s);
  }
}
int main(int argc, char** argv) {
  int n = atoi(argv[1]), m = atoi(argv[2]); target = strtoull(argv[3], 0, 16); S = atoi(argv[4]);
  allowNot = argc > 5 ? atoi(argv[5]) : 0;
  NI = n + m; FULL = (n * m == 64) ? ~0ULL : ((1ULL << (n * m)) - 1);
  St s0; s0.n = NI; s0.cnt = 0;
  for (int u = 0; u < n; u++) { T v = 0; for (int c = 0; c < m; c++) v |= 1ULL << (u * m + c); s0.w[u] = v; s0.reads[u] = 0; s0.isnot[u] = 0; }
  for (int c = 0; c < m; c++) { T v = 0; for (int u = 0; u < n; u++) v |= 1ULL << (u * m + c); s0.w[n + c] = v; s0.reads[n + c] = 0; s0.isnot[n + c] = 0; }
  std::vector<std::vector<G>> pre;
  std::vector<G> l1; expand(s0, &l1);
  for (auto& x : l1) {
    St s = s0; apply(s, x);
    std::vector<G> l2; expand(s, &l2);
    for (auto& y : l2) pre.push_back({x, y});
  }
  long long total = 0;
  #pragma omp parallel for schedule(dynamic, 1) reduction(+:total)
  for (long i = 0; i < (long)pre.size(); i++) {
    if (found) continue;
    St s = s0; s.cnt = 0;
    for (auto& x : pre[i]) apply(s, x);
    expand(s, nullptr); total += s.cnt;
  }
  if (!found) printf("NONE size %d nodes %lld\n", S, total);
  return 0;
}
