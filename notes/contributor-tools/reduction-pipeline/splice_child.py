"""Splice a prepared proof into a desk skeleton.

usage: splice_child.py <skeleton L_meta_N.lean (in place)> <prepared.lean> <helper namespace>
prepared.lean: imports, `namespace <helper ns> ... end <helper ns>`, then one theorem whose proof
starts after the first ':= by' following the theorem keyword. The helper namespace is renamed to
the gap's own namespace, and the skeleton's exact statement is kept verbatim.
"""
import re, sys

skel_p, prep_p, hns = sys.argv[1:4]
skel = open(skel_p, encoding='utf-8').read()
prep = open(prep_p, encoding='utf-8').read()
m = re.search(r'^theorem (PEqualNP\.Outside\.(L_[a-z0-9_]+)) :', skel, re.M)
full, short = m.group(1), m.group(2)
own_ns = 'PEqualNP.Outside.' + short
imports = [l for l in skel.splitlines() if l.startswith('import ')]
for l in prep.splitlines():
    if l.startswith('import ') and l not in imports:
        imports.append(l)
helpers = prep[prep.index('namespace ' + hns):prep.index('end ' + hns) + len('end ' + hns)]
helpers = helpers.replace(hns, own_ns)
thm_at = prep.index('\ntheorem ')
opts = ''
pre = prep[:thm_at].rstrip().splitlines()
if pre and pre[-1].startswith('set_option '):
    opts = pre[-1] + '\n'
proof = prep[prep.index(':= by', thm_at) + len(':= by'):].replace(hns, own_ns)
stmt_start = skel.index('theorem ' + full)
stmt_end = skel.rindex(':= by')
stmt = skel[stmt_start:stmt_end]
out = '\n'.join(imports) + '\n\n' + helpers + '\n\n' + opts + stmt + ':= by' + proof
open(skel_p, 'w', encoding='utf-8', newline='\n').write(out)
print('spliced', full)
