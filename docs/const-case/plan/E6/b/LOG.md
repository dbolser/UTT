# E6 attempt b: log

- Basic.lean: `T.strong_env_defeq`, `T.retype` (join retyping), `T.cons_closed`, `T.extra_true`. Built.
- Lower.lean: `T.rhs_lower2` = E6a `LR.rhs_lower` + raw conjunct (`LE_Interp ρ_low mC rhsAbs` when
  root vars are below their entries). Built, sorry-free.
- Selfs.lean: `T.cons_self`, `T.cons_selfs` (self entries of `W_p` over any SubstWF). Built.
- Delta.lean: `T.rhs_adequate` (generic steps 1-4 for both shapes, given a `SubstWF` of the
  pattern context over `lowerCtx`), `T.pat_leaf_delta` (delta case, proved, sorry-free).
- Iota1.lean: ports of HheadSupply (`T.matches_varN`, `T.ofRargs_get`, `T.lowerCtx_rec`,
  `T.hhead_supply`), `T.interp_indTy_le`, the lowering `T.lowerA`/`T.lowerF` and its facts,
  `T.field_var_le` (hvar's field case). Built, sorry-free.
- Iota2.lean: `T.const_full_bound`, `T.matchesS_varN`, `T.ctor_spine_interp` (inversion of
  constructor-spine interpretations), `T.ctor'_T_le`. Built, sorry-free.
- Iota3.lean: `T.substWF_cons_inv`, `T.substWF_nil_beyond`, `T.major_ctor` (the major entry's
  typed shape is `ctor c' l`, the pair satisfies the clause), `T.ctor_clause_data`,
  `T.major_levels_whnf`, `T.cons_fields` (field entries of W_p). Built, sorry-free.
- Iota4.lean: `T.mkInst_inst`, `T.type_inv` (interpretations of the RHS type at ρ_low are
  interpretations of B at ρ), `T.compat_indTy_le`, `T.foldl_cons_*`, `T.telStrong_body`,
  `T.openSpine_typing`. Built, sorry-free.
- Iota5.lean: `T.type_subst`, `T.iota_typed_red` (typed head reduction of one goal side: appDF +
  pat_defeq along W_ctx, untyped major+extra). Built, sorry-free.
- Iota6.lean: `T.major_replace` (SubstWF for (σ, σ[0 := c' Xs]) via whr on the right),
  `T.recVal_eq` (the recursor part of lowerCtx is W's base valuation), `T.fields_typing`
  (field types' rank-bounded typings from EnvStrongR.ctx), `T.hvar_iota`. Built, sorry-free.
- Iota7.lean: the two corner helpers, each with ONE marked sorry in one branch:
  * `T.gap_major_levels` (gap A): `us.map (instV ls) = ls''` (clause levels = major-domain levels).
    Proved if the major domain head `I` has no delta rule (`T.const_whnf`) or the ctor has 0
    uvars (`T.lhs_ctor_levels`); sorry: `I` has a delta rule and `c'` is universe-polymorphic.
  * `T.gap_prop_field_root` (gap B): RHS root = constructor-field variable whose closed field
    type admits no indTy shape (a Prop instance). Proved if B's sort is Prop (`T.prop_sort_bot`);
    sorry: B's sort `vB ≠ 0` (needs sort uniqueness for `g.rhs`).
  Also `T.fieldsEq_len`, `T.rec_path_bound`, `T.lhs_ctor_levels`, `T.spine_head_sound`.
- Iota8.lean: `T.pat_leaf_iota` (assembly of steps 1-6). Built; depends on the two gaps only.
- PatLeaf.lean: `T.pat_leaf_1a` (pinned statement verbatim; case split by `pat_simple`).
- Check.lean: statement check passes; `#print axioms` shows sorryAx; tracer: 2 constants
  directly containing sorry (the gap helpers); `T.pat_leaf_delta` tracer: 0.

## Outcome
Proved up to two corner facts (gaps A and B above), both needing unique typing / a Params-level
restriction; neither is suppliable by R9. Delta rules: fully proved (`T.pat_leaf_delta`).
Check: `lake env lean /tmp/utt-exp/e6/b/Check.lean` from /tmp/utt-snap19b (output in check_out.txt).

## Fix round 1 (after the verifier's rejection)
- Gap B restated (`Iota7.lean`, `T.gap_prop_root_sort`): the old helper decoupled F, Γ, B, ρ, W,
  m, a from the rule and was refutable. The new sorried fact is `vB = 0` with every datum the
  rule's own: hP, hg, h1, h2, hHs/hTc (recursor type), hroot, F = the root field's ctx entry
  (hF), hprop, ⊢ Γ₀, HB = strong typing of the codomain `Bmaj` in the recursor telescope. It is
  sort uniqueness for the rule (true under unique typing), and nothing weaker suffices.
- `T.pat_leaf_iota` now takes facts A and B as hypotheses (`hGA`, `hGB`): sorry-free.
  `T.pat_leaf_1a` (pinned) supplies them from `T.gap_major_levels` / `T.gap_prop_root_sort`.
- New `T.pat_leaf_1a_restricted` (sorry-free): the pinned statement under two candidate Params
  fields RA (no recursor major domain is `symb`-classified) and RB (no iota RHS is a bare
  constructor-field variable).
- Duplication: `T.retype` is now `LR.Adequate.mono_r` at the identity substitution
  (`T.substWF_self`, `T.substWF_len` moved to Basic). `T.rhs_lower2` drops E6a's main conjunct
  (unused by E6) and the unused `hm`; it re-runs E6a's wrapper around `T.rhs_lower_core`.
- Lints: removed unused `hm` (rhs_lower2, rhs_adequate), unused `ha` (compat_indTy_le);
  `omit [Params] in` for the two Forall₂ helpers. Only the two sorry warnings remain.
- Check.lean rerun: exit 0, output in check_out.txt. Tracer: pinned lemma reaches exactly the two
  fact helpers; pat_leaf_iota, pat_leaf_delta, pat_leaf_1a_restricted reach 0 sorry. Scan of all
  186 E6 constants: sorry only in the two fact helpers; no axiom/opaque/unsafe/partial.
