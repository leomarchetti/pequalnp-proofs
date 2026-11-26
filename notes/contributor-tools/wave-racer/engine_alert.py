"""Alert for new steps shaped like the ones the L_meta_1673 search engine (Trey Kind, PR 6929) proves.

Reads gaps.json every POLL s and looks for open steps with weight >= MIN_WEIGHT whose statement has one of the shapes
of the 214 engine proofs on main:
  - graph lower bound: forall t, HasCircuitSize n (OR of edges) t -> c <= t
  - gate-list lower bound: forall (gates : List Gate) (o : N), ...
  - Monotone2 suffices for one function: forall s, HasCircuitSize n f s -> exists C, Monotone2 C and C.size <= s ...
  - first-gate structure: forall C, FanInTwo C -> (output wire ...) -> ...
  - any other lower bound ending in "-> c <= t / s / C.size"
Steps seen before (state in engine_seen.json) never alert again; on the first start everything already open is
recorded as seen. Each new hit is written to engine_alerts.log, and the script exits after a snapshot with hits,
so whoever started it in the background is told. Start it again to keep watching.
usage: python -I -X utf8 -u .pnp/race/engine_alert.py [--once]
"""
import json, os, re, sys, time, urllib.request
from datetime import datetime

DIR = os.path.dirname(os.path.abspath(__file__))
SNAP = 'https://data.pequalnp.com/data/desk/gaps.json'
POLL, MIN_WEIGHT = 60, 20
SHAPES = [
    ('graph lower bound', r'^∀ [ts] : ℕ, PEqualNP\.MetaComplexity\.HasCircuitSize \d+ \(fun x : Fin \d+ → Bool => [\(\)x\d&|\s]+\) [ts] → \d+ ≤ [ts]$'),
    ('gate-list lower bound', r'^∀ \(gates : List PEqualNP\.CircuitLowerBounds\.Gate\) \(o : ℕ\)'),
    ('Monotone2 suffices', r'∀ s : ℕ, PEqualNP\.MetaComplexity\.HasCircuitSize \d+ .* s → ∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.Monotone2 C ∧ C\.size ≤ s'),
    ('first-gate structure', r'^∀ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C → .*\.getD \d+ false'),
    ('other lower bound', r'→ \d+ ≤ (t|s|C\.size)$'),
]

def shape(stmt):
    s = (stmt or '').strip()
    for name, p in SHAPES:
        if re.search(p, s, re.S): return name
    return None

def snapshot():
    req = urllib.request.Request(SNAP, headers={'User-Agent': 'curl/8.0', 'Cache-Control': 'no-cache'})
    with urllib.request.urlopen(req, timeout=40) as r:
        return json.load(r)['gaps']

def log(line):
    line = datetime.now().strftime('%Y-%m-%d %H:%M:%S ') + line
    print(line, flush=True)
    with open(os.path.join(DIR, 'engine_alerts.log'), 'a', encoding='utf-8') as f: f.write(line + '\n')

def main():
    path = os.path.join(DIR, 'engine_seen.json')
    seen = json.load(open(path, encoding='utf-8')) if os.path.exists(path) else None
    first = seen is None
    seen = set(seen or [])
    while True:
        try:
            G = snapshot()
        except Exception as e:
            print('snapshot failed:', str(e)[:120], flush=True); time.sleep(POLL); continue
        hits = []
        for g in G:
            if g['id'] in seen or int(g.get('weight') or 0) < MIN_WEIGHT or g.get('dead'): continue
            k = shape(g.get('statement'))
            if k: hits.append((k, g))
        for k, g in hits: seen.add(g['id'])
        json.dump(sorted(seen), open(path, 'w', encoding='utf-8'))
        if first:
            log('first start: %d engine-shaped open step(s) with weight >= %d recorded as seen: %s'
                % (len(hits), MIN_WEIGHT, ', '.join('%s (w%s, %s)' % (g['id'], g.get('weight'), k) for k, g in hits) or 'none'))
            first = False
        elif hits:
            for k, g in sorted(hits, key=lambda h: -int(h[1].get('weight') or 0)):
                log('NEW %s: %s weight %s, depth %s, PR open %s, held %s | %s' % (k, g['id'], g.get('weight'), g.get('depth'),
                    g.get('pr_open'), g.get('held_now'), (g.get('statement') or '')[:220].replace('\n', ' ')))
            log('%d new engine-shaped step(s); exiting so the watcher is told' % len(hits))
            return
        if '--once' in sys.argv: return
        time.sleep(POLL)

if __name__ == '__main__':
    main()
