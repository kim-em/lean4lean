import Lean4Lean.Theory.Typing.Strengthening.StructureReconstruction

/-! # Constructor parameter typing from indexed projection families

Family and constructor parameter annotations may be convertible rather than
identical. Declaration parameter agreement transports actual family arguments
to the constructor's syntactic telescope without restricting its indices.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- Typed arguments along a syntactic telescope give the direct constructor
parameter walk used by projection typing. -/
theorem argsTyped_of_telescope
    (hlen : args.length = doms.length)
    (ha : ∀ j (hj : j < args.length) (hd : j < doms.length),
      env.HasType U Γ args[j] (doms[j].instOuter (args.take j))) :
    ArgsTyped env U Γ (wrapForalls doms result) args (result.instOuter args) := by
  induction args generalizing doms result with
  | nil =>
    obtain rfl : doms = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact .nil
  | cons a args ih =>
    cases doms with
    | nil => simp at hlen
    | cons d doms =>
      have ha₀ := ha 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero, List.take_zero, instOuter_nil] at ha₀
      have hlen' : args.length = doms.length := by simpa using hlen
      have htail := ih (doms := instDomains doms a 0) (result := result.inst a doms.length)
        (by simpa using hlen') (by
          intro j hj hd
          have H := ha (j+1) (by simpa using hj) (by simpa using hd)
          simp only [List.getElem_cons_succ, List.take_succ_cons, instOuter_cons,
            List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] at H
          simpa [instDomains_getElem doms a 0 j (by simpa using hd)] using H)
      have H : ArgsTyped env U Γ (.forallE d (wrapForalls doms result)) (a :: args)
          ((result.inst a doms.length).instOuter args) :=
        .cons ha₀ (by simpa only [wrapForalls_inst, Nat.zero_add] using htail)
      simpa only [wrapForalls, List.foldr_cons, instOuter_cons, hlen'] using H

/-- A recovered indexed family typing supplies the constructor's parameter
walk. The declaration aligns its own parameter telescope with the family's. -/
theorem projection_parameters_typed (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hinfo : env.projections name info)
    (hp : params.length = info.nparams)
    (H : env.HasType U Γ major (mkApps (.const name levels) (params ++ indices))) :
    ∃ tail, ArgsTyped env U Γ (info.ctorType.instL levels) params tail := by
  obtain ⟨decl, family, ctor, hfamily, hctorMem, hname, hctorUvars, huvars,
    hnparams, hindices, hlevel, hctorName, hctorType, hlookup, hwf,
    ⟨common, Hshape, Hparams⟩, Hraw, hnodup⟩ := henv.ordered.projectionShape hinfo
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := Hraw.forallArity
  have hdomle : info.nparams ≤ doms.length := by omega
  have hresultWF := hwf
  rw [hshape] at hresultWF
  obtain ⟨hdomctx, _, hresult⟩ := IsType.wrapForalls_inv henv (by trivial) hresultWF
  have hresultShape : result = mkApps (.const family.name (VLevel.params decl.uvars))
      result.getAppFnArgs.2 := by
    rw [← hhead]
    exact (VExpr.mkApps_getAppFnArgs_eq result).symm
  have hresult' := hresult
  rw [hresultShape] at hresult'
  obtain ⟨_, hfamilyHead⟩ := VExpr.WF.of_mkApps henv hdomctx ⟨_, hresult'⟩
  obtain ⟨ci, hci, _, hcount⟩ := HasType.const_inv henv hdomctx hfamilyHead
  rw [hname, hlookup] at hci
  cases Option.some.inj hci
  have hfamilyUvars : family.uvars = decl.uvars := by simpa using hcount.symm
  obtain ⟨normalized, ownParams, afterParams, indices, result', exprType,
    hnorm, hown, hidx, HownP, hres⟩ := Hshape
  obtain ⟨ctorParams, tail, hctorParams, HctorP⟩ := Hparams
  have hownLen : ownParams.length = info.nparams :=
    (VExpr.takeForalls_domains_length hown).trans hnparams
  have hnormEq : normalized = wrapForalls ownParams afterParams :=
    VExpr.eq_wrapForalls_of_takeForalls hown
  have hctorParamsEq : ctorParams = doms.take info.nparams := by
    have h1 := VExpr.takeForalls_wrapForalls (doms.take info.nparams)
      (wrapForalls (doms.drop info.nparams) result)
    have hsplit : wrapForalls doms result = wrapForalls (doms.take info.nparams)
        (wrapForalls (doms.drop info.nparams) result) := by
      rw [← wrapForalls_append, List.take_append_drop]
    have h2 := hctorParams
    rw [hshape, hnparams, hsplit] at h2
    simp only [List.length_take, Nat.min_eq_left hdomle] at h1
    exact (Prod.mk.inj (Option.some.inj (h2.symm.trans h1))).1
  have hctx : env.IsDefEqCtx decl.uvars [] ownParams.reverse (doms.take info.nparams).reverse := by
    rw [← hctorParamsEq]
    exact IsDefEqCtx.trans_empty henv (HownP.symm henv.ordered) HctorP
  have htypeWF : env.IsType decl.uvars [] family.type := by
    have ht := henv.ordered.constWF hlookup
    change env.IsType family.uvars [] family.type at ht
    rwa [hfamilyUvars] at ht
  have hnormWF : env.IsType decl.uvars [] normalized :=
    let ⟨u, h⟩ := htypeWF
    ⟨u, h.defeqU_l henv (by trivial) ⟨_, hnorm⟩⟩
  rw [hnormEq] at hnormWF
  have hΓtel := (IsType.wrapForalls_inv henv (by trivial) hnormWF).1
  simp only [List.append_nil] at hΓtel
  obtain ⟨u, hsort⟩ := H.isType henv.ordered hΓ
  obtain ⟨_, hcw⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hsort⟩
  obtain ⟨ci', hci', hlsw, hlen'⟩ := HasType.const_inv henv hΓ hcw
  rw [hlookup] at hci'
  cases Option.some.inj hci'
  have hlevels : levels.length = info.uvars := by
    exact hlen'.trans (hfamilyUvars.trans huvars)
  have hc := HasType.const (Γ := Γ) hlookup hlsw hlen'
  have hdef : env.IsDefEqU U Γ (family.type.instL levels) (normalized.instL levels) :=
    ⟨_, (hnorm.instL hlsw).weak0 henv.ordered⟩
  have hc' := hc.defeqU_r henv hΓ hdef
  rw [hnormEq, instL_wrapForalls] at hc'
  have hprefix : VExpr.WF env U Γ (mkApps (.const name levels) params) := by
    rw [mkApps_append] at hsort
    exact VExpr.WF.of_mkApps henv hΓ ⟨_, hsort⟩
  obtain ⟨hargsT, _⟩ := HasType.mkApps_wrapForalls henv hΓ hc' hprefix
    (by simp only [List.length_map]; omega)
  have hparams : ∀ k (hk : k < params.length) (hk' : k < doms.length),
      env.HasType U Γ params[k] ((doms[k].instL levels).instOuter (params.take k)) := by
    intro k hk hk'
    have hkown : k < ownParams.length := by omega
    obtain ⟨u, hdk⟩ := hctx.reverse_getElem k hkown (by simp; omega)
    simp only [List.getElem_take] at hdk
    have hΔ₀ : OnCtx (ownParams.take k).reverse (env.IsType decl.uvars) := by
      have he : ownParams.reverse = (ownParams.drop k).reverse ++ (ownParams.take k).reverse := by
        rw [← List.reverse_append, List.take_append_drop]
      rw [he] at hΓtel
      exact hΓtel.of_append
    have hconv := IsDefEqU.closed_telescope_instOuter henv hΔ₀ ⟨_, hdk⟩ hlsw
      (args := params.take k) (by simp; omega) (by
        intro j hj hj'
        simp only [List.length_take] at hj
        have ht := hargsT j (by omega) (by simp; omega)
        simp only [List.reverse_reverse, List.getElem_map, List.getElem_take,
          List.take_take, Nat.min_eq_left (Nat.le_of_lt (show j < k by omega))] at ht ⊢
        exact ht)
    have harg := hargsT k hk (by simpa using hkown)
    simp only [List.getElem_map] at harg
    exact harg.defeqU_r henv hΓ hconv
  have ht := argsTyped_of_telescope (env := env) (U := U) (Γ := Γ)
    (doms := (doms.take info.nparams).map (·.instL levels))
    (result := (wrapForalls (doms.drop info.nparams) result).instL levels)
    (args := params) (by simp only [List.length_map, List.length_take, hp,
      Nat.min_eq_left hdomle]) (by
      intro j hj hd
      simpa only [List.getElem_map, List.getElem_take] using hparams j hj (by omega))
  refine ⟨((wrapForalls (doms.drop info.nparams) result).instL levels).instOuter params, ?_⟩
  have hs : info.ctorType = wrapForalls (doms.take info.nparams)
      (wrapForalls (doms.drop info.nparams) result) := by
    rw [← hctorType, hshape, ← wrapForalls_append, List.take_append_drop]
  rw [hs, instL_wrapForalls]
  exact ht

end Lean4Lean.VEnv.Strengthening
