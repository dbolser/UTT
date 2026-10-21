import re,sys
def strip(t):
    t=re.sub(r'/--.*?-/', '', t, flags=re.S)
    t=re.sub(r'--[^\n]*', '', t)
    return ' '.join(t.split())
sx=open('/tmp/utt-snap15b/Lean4Lean/Experimental/SExpr.lean').read()
a=sx.index('class Params where\n')+len('class Params where\n'); b=sx.index('open Params\nvariable [Params]')
cls=sx[a:b]
# split out extra_patV field (from its docstring to ctor_syn's docstring)
e1=cls.index('  /-- Every defeq rule of the environment'); e2=cls.index('  /-- The type of a constructor')
cls_before=cls[:e1]; old_extra=cls[e1:e2]; cls_after=cls[e2:]
lam=open('/home/dan/Build/UTT/docs/const-case/plan/E5/LamRules.lean').read()
la=lam.index('def ExtraPatVLam : Prop :=\n')+len('def ExtraPatVLam : Prop :=\n'); lb=lam.index('namespace T')
body=lam[la:lb]
# field form: "∀ {df} {ls} {Γ}, X" -> "extra_patV {df} {ls} {Γ} : X"
body=strip(body)
assert body.startswith('∀ {df : VDefEq} {ls : List VLevel} {Γ : List VExpr},')
body='extra_patV {df : VDefEq} {ls : List VLevel} {Γ : List VExpr} :'+body[len('∀ {df : VDefEq} {ls : List VLevel} {Γ : List VExpr},'):]
m7=open('/tmp/utt-snap15b/Lean4Lean/Experimental/E3/Measure7.lean').read()
ra=m7.index('structure RankParams where\n')+len('structure RankParams where\n'); rb=m7.index('/-- Spec lemma (e) `gen_arity`, for any `Pat`')
rp=m7[ra:rb]
def sub(t):
    for f in ['env','univs','Pat','classify']:
        t=t.replace('Params.'+f, f)
    return t
expected=strip(cls_before)+' '+sub(body)+' '+strip(cls_after)+' '+sub(strip(rp))
mine=open('/tmp/utt-snap15b/Lean4Lean/Experimental/E4/NatParamsA.lean').read()
ma=mine.index('structure ParamsR where\n')+len('structure ParamsR where\n'); mb=mine.index('namespace NatEnvA')
got=strip(mine[ma:mb])
print('MATCH' if got==expected else 'DIFF')
if got!=expected:
    import difflib
    for l in difflib.unified_diff(expected.split(' '),got.split(' '),lineterm='',n=3): print(l)
print('old extra_patV removed:', 'r.1.apply m1 m2\n' and strip(old_extra) not in got)
