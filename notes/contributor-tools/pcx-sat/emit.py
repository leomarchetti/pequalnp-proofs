import sys,pickle
pk,mode,num,bound,out=sys.argv[1],sys.argv[2],sys.argv[3],int(sys.argv[4]),sys.argv[5]
d=pickle.load(open(pk,'rb')); lines=d['lines']; vars_=d['vars_']
m=max(v[0] for v in vars_)+1; n=max(v[1] for v in vars_)+1
ns='PEqualNP.Outside.L_pcx_%s_aux'%num
hdr=open(__file__.rsplit('/',1)[0]+'/header.lean').read().replace('NSNAME','L_pcx_%s_aux'%num)
def lit(l): return '((%d, %d), %s)'%(vars_[l//2]+('true' if l%2==0 else 'false',))
def linlit(l): return '({(%d, %d)}, %s)'%(vars_[l//2]+('true' if l%2==0 else 'false',))
def cl(c,f): return '∅' if not c else '{'+', '.join(f(l) for l in c)+'}'
V='Fin %d × Fin %d'%(m,n)
rows=[]
for k in range(len(lines)-1,-1,-1):
  c,h=lines[k]
  if mode=='res':
    if h is None: rows.append('(%s, none)'%cl(c,lit))
    else:
      i,j,v=h; rows.append('(%s, some (%d, %d, (%d, %d)))'%((cl(c,lit),k-1-i,k-1-j)+vars_[v]))
  else:
    if h is None: rows.append('(%s, .ax %s)'%(cl(c,linlit),cl(c,lit)))
    else:
      i,j,v=h; rows.append('(%s, .rs %d %d {(%d, %d)})'%((cl(c,linlit),k-1-j,k-1-i)+vars_[v]))
if mode=='res':
  T='Clause'; certT='List (Clause (%s) × Option (ℕ × ℕ × (%s)))'%(V,V); chk='chkR'; Rf='IsRefutation'; snd='chkR_sound'
else:
  T='LinClause'; certT='List (LinClause (%s) × Step (%s))'%(V,V); chk='chkL'; Rf='IsLinRefutation'; snd='chkL_sound'
s=hdr+'def cert : %s := [\n  '%certT+',\n  '.join(rows)+']\n\n'
s+='''set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hc : %s (axPHP %d %d) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hm : (∅ : %s (%s)) ∈ cert.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hl : (cert.map Prod.fst).length ≤ %d := by decide +kernel

end %s

'''%(chk,m,n,T,V,bound,ns)
s+='theorem PEqualNP.Outside.L_pcx_%s : ∃ π : List (PEqualNP.ProofComplexity.%s (%s)), PEqualNP.ProofComplexity.%s (PEqualNP.ProofComplexity.PHP %d %d) π ∧ π.length ≤ %d := by\n'%(num,T,V,Rf,m,n,bound)
s+='  exact ⟨%s.cert.map Prod.fst, ⟨%s.%s _ (%s.axPHP %d %d) (%s.axPHP_sound %d %d) _ %s.hc, %s.hm⟩, %s.hl⟩\n'%(ns,ns,snd,ns,m,n,ns,m,n,ns,ns,ns)
open(out,'w').write(s)
print('lines',len(lines))
