# SAT model of a resolution refutation of PHP(m,n): axioms first, then D derived lines.
import sys, itertools, subprocess
m=int(sys.argv[1]); n=int(sys.argv[2]); D=int(sys.argv[3]); W=int(sys.argv[4]) if len(sys.argv)>4 else 99
out=sys.argv[5] if len(sys.argv)>5 else 'f.cnf'
NEG=int(sys.argv[7]) if len(sys.argv)>7 else 99
HMODE=len(sys.argv)>6 and sys.argv[6]=='H'
vars_=[(i,j) for i in range(m) for j in range(n)]
NV=len(vars_); vid={v:k for k,v in enumerate(vars_)}
lits=[(v,s) for v in range(NV) for s in (1,0)]  # lit index = 2*v + (0 if pos else 1)
def L(v,s): return 2*v+(0 if s else 1)
axioms=[]
for i in range(m): axioms.append(frozenset(L(vid[(i,j)],1) for j in range(n)))
for j in range(n):
  for i in range(m):
    for i2 in range(i+1,m): axioms.append(frozenset([L(vid[(i,j)],0),L(vid[(i2,j)],0)]))
import os
NAX=len(axioms)
if os.environ.get("PREFIX")=="pair01":
  for j in range(n):
    P0=set(L(vid[(0,jj)],1) for jj in range(n) if jj!=j)
    axioms.append(frozenset(P0|{L(vid[(1,j)],0)}))
    axioms.append(frozenset(P0|set(L(vid[(1,jj)],1) for jj in range(n) if jj!=j)))
A=len(axioms); T=A+D
cnt=[0]; cls=[]
def nv(): cnt[0]+=1; return cnt[0]
TRUE=nv(); cls.append([TRUE])
c=[[None]*(2*NV) for _ in range(T)]
for k,ax in enumerate(axioms):
  for l in range(2*NV): c[k][l]=TRUE if l in ax else -TRUE
for k in range(A,T):
  for l in range(2*NV): c[k][l]=nv()
Lp={};Rp={};pv={}
def amo(xs):
  # sequential counter
  if len(xs)<=1: return
  s=[nv() for _ in xs[:-1]]
  cls.append([-xs[0],s[0]])
  for i in range(1,len(xs)-1):
    cls.append([-xs[i],s[i]]); cls.append([-s[i-1],s[i]]); cls.append([-xs[i],-s[i-1]])
  cls.append([-xs[-1],-s[-1]])
def atmost(xs,k):
  # sequential counter at most k
  nn=len(xs)
  if k>=nn: return
  s=[[nv() for _ in range(k)] for _ in range(nn)]
  for i in range(nn):
    cls.append([-xs[i],s[i][0]])
    if i>0:
      for j in range(k): cls.append([-s[i-1][j],s[i][j]])
      for j in range(1,k): cls.append([-xs[i],-s[i-1][j-1],s[i][j]])
      cls.append([-xs[i],-s[i-1][k-1]])
for k in range(A,T):
  Lp[k]=[nv() for i in range(k)]; Rp[k]=[nv() for i in range(k)]; pv[k]=[nv() for v in range(NV)]
  cls.append(Lp[k][:]); amo(Lp[k]); cls.append(Rp[k][:]); amo(Rp[k]); cls.append(pv[k][:]); amo(pv[k])
  Av=[nv() for l in range(2*NV)]; Bv=[nv() for l in range(2*NV)]
  for i in range(k):
    for l in range(2*NV):
      x=c[i][l]
      cls.append([-Lp[k][i],-x,Av[l]]); cls.append([-Lp[k][i],x,-Av[l]])
      cls.append([-Rp[k][i],-x,Bv[l]]); cls.append([-Rp[k][i],x,-Bv[l]])
  for v in range(NV):
    p=2*v; q=2*v+1; P=pv[k][v]
    cls.append([-P,Av[p]]); cls.append([-P,Bv[q]])
    # c_p <-> (Av_p & -P) | Bv_p
    cls.append([-c[k][p],Av[p],Bv[p]]); cls.append([-c[k][p],-P,Bv[p]])
    cls.append([c[k][p],-Av[p],P]); cls.append([c[k][p],-Bv[p]])
    # c_q <-> Av_q | (Bv_q & -P)
    cls.append([-c[k][q],Av[q],Bv[q]]); cls.append([-c[k][q],-P,Av[q]])
    cls.append([c[k][q],-Av[q]]); cls.append([c[k][q],-Bv[q],P])
    cls.append([-c[k][p],-c[k][q]])
  if W<99: atmost(c[k],W)
  if NEG<99: atmost([c[k][2*v+1] for v in range(NV)],NEG)
targets=[]
if HMODE:
  for j in range(n): targets.append(set(L(vid[(i,j)],1) for i in range(m)))
  ES=[]
  for tg in targets:
    es=[]; ES.append(es)
    for k in range(A,T):
      e=nv(); es.append(e)
      for l in range(2*NV): cls.append([-e,c[k][l] if l in tg else -c[k][l]])
    cls.append(es)
  isT={}
  for k in range(A,T):
    isT[k]=nv()  # line k is not required to be used if isT
    cls.append([-isT[k]]+[ES[t][k-A] for t in range(len(targets))])
else:
  for l in range(2*NV): cls.append([-c[T-1][l]])
# every line except last used later
for k in [kk for kk in range(T-1 if not HMODE else T) if not ((0 if A>NAX else NAX)<=kk<A)]:
  cls.append(([isT[k]] if HMODE and k>=A else [])+[Lp[t][k] for t in range(max(k+1,A),T)]+[Rp[t][k] for t in range(max(k+1,A),T)])

# symmetry breaking: last pivot is variable 0; consecutive independent derived lines are in strict lex order
if not HMODE and A==NAX: cls.append([pv[T-1][0]])
def lexless(a,b):
  # returns literal r with r -> a < b (a,b lists of literals, first element most significant)
  r=nv(); e=r  # e: prefix equal so far (implied by r)
  for t in range(len(a)):
    # if e: either (a_t=0,b_t=1) -> done, or a_t==b_t and continue with e2
    d=nv(); e2=nv() if t<len(a)-1 else None
    if e2 is None: cls.append([-e,d])
    else: cls.append([-e,d,e2])
    cls.append([-d,-a[t]]); cls.append([-d,b[t]])
    if e2 is not None:
      cls.append([-e2,-a[t],b[t]]); cls.append([-e2,a[t],-b[t]])
      e=e2
  return r
for k in (range(A,T-2 if not HMODE else T-1) if not os.environ.get("NOLEX") else []):
  r=lexless(c[k],c[k+1])
  cls.append([Lp[k+1][k],Rp[k+1][k],r])

with open(out,'w') as f:
  f.write('p cnf %d %d\n'%(cnt[0],len(cls)))
  for cl in cls: f.write(' '.join(map(str,cl))+' 0\n')
import pickle
pickle.dump(dict(NAX=NAX,m=m,n=n,A=A,T=T,axioms=[sorted(a) for a in axioms],c=c,Lp=Lp,Rp=Rp,pv=pv,NV=NV,vars_=vars_),open(out+'.meta','wb'))
print('vars',cnt[0],'clauses',len(cls))
