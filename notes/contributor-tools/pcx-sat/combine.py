# combine an H-derivation for pigeons 0..n-1 into a PHP(n+1,n) refutation
import sys,pickle
H=pickle.load(open(sys.argv[1],'rb')); out=sys.argv[2]
hv=H['vars_']; n=max(v[1] for v in hv)+1; m=n+1
vars_=[(i,j) for i in range(m) for j in range(n)]; vid={v:k for k,v in enumerate(vars_)}
def L(v,s): return 2*vid[v]+(0 if s else 1)
def conv(l): return L(hv[l//2], l%2==0)
lines=[]; idx={}
def add(cl,h):
  cl=frozenset(cl)
  lines.append((cl,h)); idx.setdefault(cl,len(lines)-1); return len(lines)-1
axioms=[]
for i in range(m): axioms.append(frozenset(L((i,j),1) for j in range(n)))
for j in range(n):
  for i in range(m):
    for i2 in range(i+1,m): axioms.append(frozenset([L((i,j),0),L((i2,j),0)]))
for a in axioms: add(a,None)
hmap={}
for k,(cl,h) in enumerate(H['lines']):
  c2=frozenset(conv(l) for l in cl)
  if h is None: hmap[k]=idx[c2]
  else:
    i,j,v=h; hmap[k]=add(c2,(hmap[i],hmap[j],vid[hv[v]]))
def res(a,b,v):
  A=lines[a][0]; B=lines[b][0]; p=L(v,1); q=L(v,0)
  assert p in A and q in B
  return add((A-{p})|(B-{q}),(a,b,vid[v]))
last=n
units=[]
for j in range(n):
  cur=idx[frozenset(L((i,j),1) for i in range(n))]
  for i in range(n):
    cur=res(cur,idx[frozenset([L((i,j),0),L((last,j),0)])],(i,j))
  units.append(cur)
cur=idx[axioms[last]]
for j in range(n): cur=res(cur,units[j],(last,j))
assert len(lines[cur][0])==0
for k,(cl,h) in enumerate(lines):
  if h is None: assert cl in axioms
  else:
    i,j,v=h; assert i<k and j<k and 2*v in lines[i][0] and 2*v+1 in lines[j][0]
    assert cl==(lines[i][0]-{2*v})|(lines[j][0]-{2*v+1})
print('total lines',len(lines))
pickle.dump(dict(lines=[(sorted(c),h) for c,h in lines],vars_=vars_),open(out,'wb'))
