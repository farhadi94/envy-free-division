#!/usr/bin/env python3
"""Exact-rational finite-tape regression for the moving-frontier proof.
This is a fixture, not a proof of the measurable randomized construction.
"""
from fractions import Fraction as F
from dataclasses import dataclass
from collections import Counter
from pathlib import Path
import json,hashlib
N=3
ALPHA=F(1)
K=(1+ALPHA)/ALPHA

@dataclass
class Profile:
    knots:list
    densities:list
    def cumulative(self,i,x):
        out=F(0)
        for a,b,d in zip(self.knots,self.knots[1:],self.densities):
            if x<=a:break
            out+=d[i]*(min(x,b)-a)
        return out
    def evaluate(self,i,a,b):return self.cumulative(i,b)-self.cumulative(i,a)
    def cut(self,i,a,b,t):
        B=self.evaluate(i,a,b)
        assert min(0,B)<=t<=max(0,B)
        level=self.cumulative(i,a)+t
        if t==0:return a
        for lo,hi,d in zip(self.knots,self.knots[1:],self.densities):
            lo=max(lo,a);hi=min(hi,b)
            if lo>hi:continue
            u=self.cumulative(i,lo);v=self.cumulative(i,hi)
            if min(u,v)<=level<=max(u,v):
                return lo if u==v else lo+(level-u)/d[i]
        raise AssertionError('no legal root')
    def check(self):
        assert len(self.densities)+1==len(self.knots)
        assert self.knots[0]==0 and self.knots[-1]==1
        assert all(a<b for a,b in zip(self.knots,self.knots[1:]))
        assert all(d>0 for d in self.densities[-1])
        for i in range(N):
            assert self.cumulative(i,F(1))==1
            assert all(self.cumulative(i,x)<1 for x in self.knots[:-1])
        for d in self.densities[:-1]:
            positive=[i for i in range(N) if d[i]>0]
            assert len(positive)<=1
            if positive:
                j=positive[0]
                assert all(d[i]<=-K*d[j] for i in range(N) if i!=j)
    def refine(self,r,j=None):
        l=self.knots[-2]
        assert l<r<1
        old=self.densities[-1]
        head=[F(-1)]*N if j is None else [old[j] if i==j else -K*old[j] for i in range(N)]
        tail=[(1-self.cumulative(i,l)-head[i]*(r-l))/(1-r) for i in range(N)]
        p=Profile(self.knots[:-1]+[r,F(1)],self.densities[:-1]+[head,tail])
        p.check()
        if j is not None:
            assert tail[j]==old[j]
            assert all(self.cumulative(j,x)==p.cumulative(j,x) for x in p.knots)
        return p

def run(p,tape):
    # All queries are legal, and the fixtures exercise negative targets after
    # refinement, zero targets, full targets, endpoint1, and free output cuts.
    j=tape%N;h=(tape//N+j+1)%N
    a=F(tape%5,8); b=F(1)
    B=p.evaluate(j,a,b)
    first=('eval',j,a,b,B)
    theta=[F(0),F(1,3),F(1,2),F(1)][tape%4]
    root=p.cut(j,a,b,theta*B)
    second=('cut',j,a,b,theta*B,root)
    B2=p.evaluate(h,F(0),root)
    third=('eval',h,F(0),root,B2)
    theta2=[F(1),F(0),F(2,3)][(tape//2)%3]
    root2=p.cut(h,F(0),root,theta2*B2)
    fourth=('cut',h,F(0),root,theta2*B2,root2)
    points=sorted(set([F(0),F(1),root,root2,F(tape%11+1,13),F(2,7)]))
    allocation=[(lo,hi,(tape+c)%N) for c,(lo,hi) in enumerate(zip(points,points[1:]))]
    return [first,second,third,fourth],allocation

def coordinates(query):
    return query[2:4]+((query[-1],) if query[0]=='cut' else ())
def values(p,A):
    return [[sum((p.evaluate(i,a,b) for a,b,j in A if j==k),F(0)) for k in range(N)] for i in range(N)]
def same_replay(old,new,trace):
    for query in trace:
        typ,j,a,b=query[:4]
        assert old.evaluate(j,a,b)==new.evaluate(j,a,b)
        if typ=='cut':assert new.cut(j,a,b,query[4])==query[5]
def r_after(p,coords):
    x=max([p.knots[-2]]+[x for x in coords if x<1])
    return (1+x)/2

p=Profile([F(0),F(1)],[[F(1)]*N]);p.check()
captured={};remaining=set(range(24));batches=[];updates=0;negative_targets=0
while remaining:
    S=set(remaining)
    for stage in range(4):
        executions={t:run(p,t) for t in S}
        counts=Counter(trace[stage][1] for trace,A in executions.values())
        j=max(sorted(counts),key=counts.get)
        S={t for t in S if executions[t][0][stage][1]==j}
        r=r_after(p,[x for t in S for x in coordinates(executions[t][0][stage])])
        new=p.refine(r,j)
        for t in S:
            trace=executions[t][0]
            same_replay(p,new,trace[:stage+1])
            assert run(new,t)[0][:stage+1]==trace[:stage+1]
            negative_targets+=int(trace[stage][0]=='cut' and trace[stage][4]<0)
        for t,(trace,A,V) in captured.items():
            same_replay(p,new,trace)
            assert run(new,t)==(trace,A) and values(new,A)==V
        p=new;updates+=1
    executions={t:run(p,t) for t in S}
    r=r_after(p,[x for trace,A in executions.values() for a,b,j in A for x in (a,b)])
    new=p.refine(r)
    for t in S:
        trace,A=executions[t]
        same_replay(p,new,trace)
        assert run(new,t)==(trace,A)
        V=values(new,A)
        tail_owner=next(j for a,b,j in A if a<=r<b)
        score=sum((ALPHA*V[i][tail_owner]-V[i][i] for i in range(N) if i!=tail_owner),F(0))/(N-1)
        assert score>=ALPHA
        captured[t]=(trace,A,V)
    for t,(trace,A,V) in captured.items():
        same_replay(p,new,trace)
        assert run(new,t)==(trace,A) and values(new,A)==V
    p=new;updates+=1;remaining-=S
    batches.append({'new_tapes':sorted(S),'captured_total':len(captured),'resolved_cells':len(p.densities)-1})

fixture={'knots':[str(x) for x in p.knots],'densities':[[str(x) for x in d] for d in p.densities]}
encoded=json.dumps(fixture,separators=(',',':')).encode()
record={'status':'passed','arithmetic':'exact rational','n':N,'alpha':str(ALPHA),'tapes':len(captured),'queries_per_tape':4,'batches':batches,'updates':updates,'negative_target_stages':negative_targets,'profile_sha256':hashlib.sha256(encoded).hexdigest(),'max_fraction_digit_count':max(len(str(abs(x.numerator)))+len(str(x.denominator)) for row in p.densities for x in row),'checks':['every intermediate profile has the density cone, positive tail, strict cumulative ceiling and total1','new queried row unchanged','every selected query prefix replays','every previously captured full transcript and output replays','every previously captured bundle table unchanged','every captured output has average signed envy at least alpha'],'scope':'Finite-tape regression only; measurable arbitrary-tape construction is a separate written proof.'}
base=Path(__file__)
base.with_name('coordinated_family_capture_profile.json').write_text(json.dumps(fixture,indent=2)+'\n')
base.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
