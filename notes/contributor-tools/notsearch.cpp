// Exact search: 5-input circuits of AND2/OR2/NOT1 gates computing a target table.
// Every gate is read later or is the output (= last gate); no NOT reads a NOT.
// Canonical topological order (each gate reads its predecessor or has a larger key)
// and truth-table dedup (no constant, no repeated wire) are complete for minimal-type
// existence questions: a duplicate wire can always be redirected and removed.
// Usage: notsearch <table_u32> <size> <mode>
//   mode 0: some NOT reads a gate (L-meta-18089..18098 shape)
//   mode 1: some NOT exists, may read an input (L-meta-17974..17976 shape)
//   mode 2: no NOT (monotone sanity check)
// Exhaustive at exactly <size> gates; prints FOUND + gates, or NONE.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <atomic>
#include <omp.h>
typedef uint32_t T;
static const int N = 5;
static T target; static int S; static int mode;
std::atomic<int> found(0);
struct G { int op, a, b; };  // op 0 AND, 1 OR, 2 NOT (b=-1)
struct St { T w[40]; bool isnot[40]; int reads[40]; G g[40]; int n; bool ok; long long cnt; };
static inline long key(const G& x) { return ((long)x.op * 64 + x.a) * 64 + (x.b + 1); }
static bool okAfter(const St& s, const G& x) {
  if (s.ok) return true;
  if (x.op != 2) return false;
  return mode == 1 || x.a >= N;
}
static void report(St& s) {
  if (found.exchange(1)) return;
  #pragma omp critical
  {
    printf("FOUND size %d\n", s.n - N);
    for (int j = N; j < s.n; j++) printf("%d %d %d\n", s.g[j].op, s.g[j].a, s.g[j].b);
    fflush(stdout);
  }
}
static bool dup(const St& s, T v) {
  if (v == 0 || v == 0xFFFFFFFFu) return true;
  for (int i = 0; i < s.n; i++) if (s.w[i] == v) return true;
  return false;
}
static void dfs(St& s);
static void push(St& s, const G& x, T v) {
  int j = s.n; s.g[j] = x; s.w[j] = v; s.isnot[j] = (x.op == 2);
  s.reads[j] = 0; s.reads[x.a]++; if (x.b >= 0) s.reads[x.b]++;
  bool o = s.ok; s.ok = okAfter(s, x);
  s.n++; dfs(s); s.n--;
  s.reads[x.a]--; if (x.b >= 0) s.reads[x.b]--; s.ok = o;
}
// enumerate candidate gates at current state; if collect != null, store instead of recursing
static void expand(St& s, std::vector<G>* collect) {
  int used = s.n - N, r = S - used;
  int unused = 0; for (int i = N; i < s.n; i++) if (!s.reads[i]) unused++;
  if (unused > r + 1 || r <= 0) return;
  bool last = (r == 1);
  long prevkey = (s.n > N) ? key(s.g[s.n - 1]) : -1;
  int prev = s.n - 1;
  for (int op = 0; op < 3; op++) {
    if (op == 2 && mode == 2) continue;
    for (int b = (op == 2 ? -1 : 1); b < (op == 2 ? 0 : s.n); b++)
    for (int a = 0; a < (op == 2 ? s.n : b); a++) {
      G x{op, a, b};
      if (op == 2 && s.isnot[a]) continue;
      if (s.n > N && a != prev && b != prev && key(x) <= prevkey) continue;
      T v = op == 0 ? (s.w[a] & s.w[b]) : op == 1 ? (s.w[a] | s.w[b]) : ~s.w[a];
      if (last) {
        if (v != target || !okAfter(s, x)) continue;
        int un = unused - (a >= N && !s.reads[a]) - (b >= N && !s.reads[b]);
        if (un) continue;
        s.g[s.n] = x; s.n++; report(s); s.n--; return;
      }
      if (dup(s, v)) continue;
      if (r == 2 && !s.ok && !okAfter(s, x)) {
        // last gate must then be a qualifying NOT whose value is target: v must be ~target
        // (NOT reads one wire); prune unless some wire or v equals ~target
        bool can = (v == ~target);
        for (int i = 0; i < s.n && !can; i++) if (s.w[i] == ~target) can = true;
        if (!can) continue;
      }
      if (collect) collect->push_back(x); else push(s, x, v);
    }
  }
}
static void dfs(St& s) {
  if (found.load(std::memory_order_relaxed)) return;
  s.cnt++;
  expand(s, nullptr);
}
static void init(St& s) {
  s.n = N; s.ok = (mode == 2); s.cnt = 0;
  for (int i = 0; i < N; i++) {
    T v = 0; for (int r = 0; r < 32; r++) if (r >> i & 1) v |= (T)1 << r;
    s.w[i] = v; s.isnot[i] = false; s.reads[i] = 0;
  }
}
int main(int argc, char** argv) {
  target = (T)strtoul(argv[1], 0, 10); S = atoi(argv[2]); mode = atoi(argv[3]);
  // build prefixes of depth 2 (or less)
  St s0; init(s0);
  std::vector<std::vector<G>> pre;
  std::vector<G> l1; expand(s0, &l1);
  if (found) return 0;
  for (auto& x : l1) {
    St s = s0; T v = x.op == 0 ? (s.w[x.a] & s.w[x.b]) : x.op == 1 ? (s.w[x.a] | s.w[x.b]) : ~s.w[x.a];
    int j = s.n; s.g[j] = x; s.w[j] = v; s.isnot[j] = x.op == 2; s.reads[j] = 0; s.reads[x.a]++; if (x.b >= 0) s.reads[x.b]++;
    s.ok = okAfter(s0, x); s.n++;
    std::vector<G> l2; if (S >= 3) expand(s, &l2);
    if (S < 3) { pre.push_back({x}); continue; }
    for (auto& y : l2) pre.push_back({x, y});
  }
  long long total = 0;
  #pragma omp parallel for schedule(dynamic, 1) reduction(+:total)
  for (long i = 0; i < (long)pre.size(); i++) {
    if (found) continue;
    St s; init(s);
    for (auto& x : pre[i]) {
      T v = x.op == 0 ? (s.w[x.a] & s.w[x.b]) : x.op == 1 ? (s.w[x.a] | s.w[x.b]) : ~s.w[x.a];
      int j = s.n; s.g[j] = x; s.w[j] = v; s.isnot[j] = x.op == 2; s.reads[j] = 0; s.reads[x.a]++; if (x.b >= 0) s.reads[x.b]++;
      s.ok = okAfter(s, x); s.n++;
    }
    dfs(s); total += s.cnt;
  }
  if (!found) printf("NONE size %d nodes %lld\n", S, total);
  else fprintf(stderr, "nodes %lld\n", total);
  return 0;
}
