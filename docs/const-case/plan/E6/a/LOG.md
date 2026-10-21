# E6 attempt a: log

Snapshot /tmp/utt-snap19a, scratch /tmp/utt-exp/e6/a.

## Analysis (before coding)
- Step 2 as written is circular: rhs_lower's main conjunct needs `a'` with `y' : a'` and
  `LE_Interp ρ_low a' (type)`, and soundness at ρ_low only gives such an `a'` *after*
  `LE_Interp ρ_low y' rhsAbs`. The goal's own `a` interprets `B` at `ρ`, whose major entry may
  have untyped fields, so it does not interpret the lowered type in general.
  Route taken: rhs_lower_core's second conjunct (the RHS shape itself is interpreted at ρ_low
  unless the RHS root is a constructor-field variable), soundness at ρ_low for a typed pair
  (y, b) above it, WFIH at (y, b), then a type transfer: every b interpreting the lowered type
  interprets B at ρ (needs a new bound: interpretations of a ctor spine lie below
  `ctor' c' (argument shapes)`), so `a` and `b` are compatible and the Adequate.mono_r pattern
  moves the DefEq to (m, a).
- Gaps found: (F1) the ctor clause's levels `ls₂` equal the pattern's `us.map (instV ls)` only
  if the major domain `const I ls''` is whnf (I not symb); (F2) bare constructor-field RHS root
  with an untyped/Prop field shape.

## Steps
- S1 (helpers: substWF_val, range_foldr_self, spine_bvars_typed): OK.
- S2 (G1: const_beyond, ctor_spine_bound, ctor_spine_le, ctor'_le_T): OK.
- S3 (defEq_transfer = Adequate.mono_r core; substWF_push = iterated Adequate.cons): OK.
- S4 (T.rhs_lower2 = LR.rhs_lower + the root conjunct of rhs_lower_core): OK.
- S5 (T.rhs_core: W_p selfs, root interpretation, soundness pair (y,b), WFIH, gen_rhsAbs): OK.
- S6 (strong_env_defeq, pat_defeq_inst, finish, tyV_const, T.pat_leaf_delta): OK, sorry-free.
- S7 (mkInst_subst, type_subst (d), hasType_ctor_inv, fieldsEq_get, indTy_interp_le, lowF,
  lowF_entry, hvar_field): OK.
- S8/S10 (HheadSupply port, gen_lhs_matches with pathIdx, matchesS_spine, telStrong_last): OK.
- S9 (T.pat_leaf_iota, with the gap facts hgapI/hgapF as hypotheses): OK, sorry-free.
- Modules E6/{Helpers,RhsCore,Parts,IotaData,Iota,PatLeaf}.lean build.
- PatLeaf: T.pat_leaf_1a (pinned statement, checked by `example`), one sorry in T.pat_leaf_gap.
- Refinement: bare non-Prop constructor-field RHS roots proved (T.le_indTy_of_compat,
  T.indTy_interp_const, StrongSound inversion of the RHS typing at the bvar root, the type
  transfer `htrans` moved before `T.rhs_core`, whose root hypothesis now also accepts a direct
  bound `m ≤ lowered entry`). The gap F2 is now only: a bare field root has a never-Prop type.
- Clean rebuild of E6/* OK (23 s). Check.lean: statement check elaborates; tracer at
  [T.pat_leaf_1a] reaches sorryAx only through T.pat_leaf_gap; T.pat_leaf_delta and
  T.pat_leaf_iota are sorry-free (propext, Classical.choice, Quot.sound); all 99 E6 constants:
  only T.pat_leaf_gap contains sorry.

## Outcome
Proved up to T.pat_leaf_gap (two iota-rule invariants not in Params):
(F1) the recursor's major-domain head is not `symb` (ctor-clause levels = pattern levels);
(F2) a bare constructor-field RHS root has a never-Prop field type.
Neither is suppliable by R9 (properties of the rule). F1: Params field (classify I = indTy 0)
or ctor `uvars = 0`; F2: Params field, or D1 fallback (b) (typed ctor fields).

## Fixer round 1 (after the verifier's rejection)
Verifier issues: (1) one sorry (T.pat_leaf_gap); (2) F1 is cheaper via Pattern.genIota;
(3) F1/F2 overstated (sufficient, not necessary; F2 stronger than used); (4) hty/hdef unused;
(5) HEAD moved (port).

Analysis: re-derived both gaps; still not closable from the landed definitions.
- F1 needs ls₂ = ls' when the major domain head I has a delta rule. Only pat_defeq's LHS typing
  ties c'.{us} to const I us; using it needs typing inversion + type uniqueness + level
  injectivity. WFIH is at a fixed Γ₀ and lower rank; pat_defeq is a full-env derivation that
  contains rec itself; shapes carry no levels. UniqueTyping.lean derives uniqueness from
  forallE_inv/sort_inv, i.e. from full adequacy (circular here).
- F2 needs B's sort = 0 at a bare Prop-field root with B depending on the major: sort/type
  uniqueness. Semantically a Type-sorted type may be interpreted by ⊥ only, so StrongSound.uniq
  (SoundEq only) does not give it.

Changes (all under E6/):
- New Gaps.lean: T.gap_major_levels (F1) proves (a) I has no delta rule (T.const_whnf) and
  (b) c' has no universe parameters (T.lhs_ctor_levels, StrongSound inversion of the pinned hdef);
  ONE sorry for "I has a delta rule ∧ c' universe-polymorphic". T.gap_field_sort (F2) states the
  exact missing fact (B's sort v₁ = 0) for "bare Prop-field RHS ∧ B depends on the major"; ONE
  sorry. Sorry-free helpers: T.major_levels_of_indTy (F1 under the genIota fix), T.prop_sort_bot,
  T.prop_interp_bot (verifier's V.prop_interp_bot), T.le_bot_of_type_le_bot, T.nondep_type_low.
- Iota.lean: T.pat_leaf_iota_of (sorry-free, parameterized by F1/F2 in exactly the gap lemmas'
  form); T.pat_leaf_iota (landed defs: _of + the gap lemmas); T.pat_leaf_iota_fixed (sorry-free
  under the two proposed definition fixes: major domain head indTy; bare-field RHS ⇒ Bmaj does
  not mention the major). Bare field root now split: non-Prop (old route), Prop + nondep B
  (new, proved), Prop + dependent B (F2 + prop_sort_bot).
- Pinned hty/hdef now used: T.pat_defeq_inst_of (hty.1, hdef) replaces Params.pat_typed/pat_defeq;
  T.rhs_core takes hty for the RHS typing (Params.strong_below hty.1 hty.2); T.lhs_ctor_levels
  uses hdef. Delta leaf takes hty/hdef too.
- PatLeaf.lean: T.pat_leaf_gap removed; T.pat_leaf_1a passes hty/hdef.
- Clean rebuild of E6/* OK (25 s). Check.lean updated (both statement directions, axioms of all
  parts, tracers): pat_leaf_1a reaches sorryAx only via T.gap_major_levels and T.gap_field_sort;
  pat_leaf_delta, pat_leaf_iota_of, pat_leaf_iota_fixed sorry-free.
