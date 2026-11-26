import sys,pickle
meta=pickle.load(open(sys.argv[1]+'.meta','rb'))
val=set()
for line in open(sys.argv[2]):
  if line.startswith('v'):
    for t in line.split()[1:]:
      t=int(t)
      if t>0: val.add(t)
T=meta['T'];A=meta['A'];NV=meta['NV'];vars_=meta['vars_']
lines=[]
for k in range(T):
  cl=frozenset(l for l in range(2*NV) if (meta['c'][k][l] in val if meta['c'][k][l]>1 else (meta['c'][k][l]==1)))
  if k<A: lines.append((cl,None if k<len(meta["axioms"]) and sorted(cl)==meta["axioms"][k] and k<meta.get("NAX",A) else "?"))
  else:
    i=[x for x,y in enumerate(meta['Lp'][k]) if y in val][0]
    j=[x for x,y in enumerate(meta['Rp'][k]) if y in val][0]
    v=[x for x,y in enumerate(meta['pv'][k]) if y in val][0]
    lines.append((cl,(i,j,v)))
# independent check
for k,(cl,h) in enumerate(lines):
  if h=="?":
    h=[(i,j,v) for i in range(k) for j in range(k) for v in range(NV) if 2*v in lines[i][0] and 2*v+1 in lines[j][0] and cl==(lines[i][0]-{2*v})|(lines[j][0]-{2*v+1})][0]
    lines[k]=(cl,h)
  if h is None: assert sorted(cl)==meta['axioms'][k]
  else:
    i,j,v=h; assert i<k and j<k
    C=lines[i][0]; Dd=lines[j][0]
    assert 2*v in C and 2*v+1 in Dd
    assert cl==(C-{2*v})|(Dd-{2*v+1}), k
import os
if not os.environ.get("NOEMPTY"): assert any(len(cl)==0 for cl,_ in lines)
print('OK',len(lines))
def fmt(cl): return ' '.join(('' if l%2==0 else '-')+'x%d%d'%vars_[l//2] for l in sorted(cl))
with open(sys.argv[3],'w') as f:
  for k,(cl,h) in enumerate(lines): f.write('%d\t%s\t%s\n'%(k,h,fmt(cl)))
pickle.dump(dict(lines=[(sorted(cl),h) for cl,h in lines],vars_=vars_),open(sys.argv[3]+'.pkl','wb'))
