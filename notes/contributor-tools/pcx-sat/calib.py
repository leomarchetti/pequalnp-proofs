import pickle,sys
meta=pickle.load(open(sys.argv[1]+'.meta','rb'))
vars_=meta['vars_']; vid={v:k for k,v in enumerate(vars_)}
def L(i,j,s): return 2*vid[(i,j)]+(0 if s else 1)
A=meta['A']
pre=[frozenset(a) for a in meta['axioms']]
# K lines and combos from the 58 proof (pigeons 0,1 pair lemmas in prefix)
lines=[]
for k in range(3):
  for j in range(3):
    if j==k: continue
    jp=3-j-k
    # from R_k: kill hole jp via pigeon 2 : first with h(0,2,jp) then h(1,2,jp)
    Rk=frozenset([L(0,j,1),L(0,jp,1),L(1,j,1),L(1,jp,1)])
    a=frozenset([L(0,j,1),L(1,j,1),L(1,jp,1),L(2,jp,0)]); b=frozenset([L(0,j,1),L(1,j,1),L(2,jp,0)])
    lines+= [a,b]
for j in range(3):
  o=[x for x in range(3) if x!=j]
  c1=frozenset([L(2,j,1),L(2,o[1],1),L(0,j,1),L(1,j,1)])
  lines+=[c1, frozenset([L(0,j,1),L(1,j,1),L(2,j,1)])]
lines=list(dict.fromkeys(lines))
print(len(lines))
# dependency: compute parents by search
allc=pre[:]
def parents(c,avail):
  for x in avail:
    for y in avail:
      for v in range(len(vars_)):
        if 2*v in x and 2*v+1 in y and c==(x-{2*v})|(y-{2*v+1}): return (x,y)
  return None
# order: repeatedly pick lex-smallest available line
key=lambda c: tuple(1 if l in c else 0 for l in range(2*len(vars_)))
order=[]; avail=set(pre); rest=set(lines)
while rest:
  cand=[c for c in rest if parents(c,avail)]
  # choose: must satisfy: if next not dependent on prev, key(prev)<key(next). choose a dependent one if exists, else smallest key > prev
  prev=order[-1] if order else None
  ok=[c for c in cand if prev is None or prev in parents(c,avail) or key(prev)<key(c)]
  c=min(ok,key=key) if ok else None
  if c is None: print('stuck'); break
  order.append(c); avail.add(c); rest.remove(c)
units=[]
for k,c in enumerate(order):
  for l in range(2*len(vars_)):
    x=meta['c'][A+k][l]; units.append(x if l in c else -x)
src=open(sys.argv[1]).read().split('\n',1)
hdr=src[0].split(); nv,nc=int(hdr[2]),int(hdr[3])
open(sys.argv[2],'w').write('p cnf %d %d\n'%(nv,nc+len(units))+src[1]+''.join('%d 0\n'%u for u in units))
