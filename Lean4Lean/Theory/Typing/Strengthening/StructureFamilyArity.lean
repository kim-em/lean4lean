import Lean4Lean.Theory.Typing.Strengthening.StructureReconstruction
import Lean4Lean.Theory.Typing.SignatureArity

/-! # Exact arity of registered structure families

The normalized family header determines how many arguments a typed family
application supplies. This recovers parameter length for a generic unindexed
recursor major without guessing its parameter expressions.
-/
namespace Lean4Lean.VEnv.Strengthening.StructureReplay
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- A registered family has a normalized telescope ending in a sort, uniformly
in every well-formed context at the levels of a known family instance. -/
theorem family_head_telescope (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections name info)
    (H : env.IsType U Γ (mkApps (.const name levels) args)) :
    ∃ doms w, doms.length = info.nparams + info.nindices ∧
      ∀ {Δ}, OnCtx Δ (env.IsType U) →
        env.HasType U Δ (.const name levels) (wrapForalls doms (.sort w)) := by
  obtain ⟨decl, family, ctor, _, _, hname, _, huvars, hnparams, hindices, _, _, hctorType,
    hlookup, hwf, ⟨common, Hshape, _⟩, Hraw, _⟩ := henv.ordered.projectionShape hinfo
  obtain ⟨doms, result, hshape, _, _, hhead, _⟩ := Hraw.forallArity
  have hresultWF := hwf
  rw [hshape] at hresultWF
  obtain ⟨hdomctx, _, hresult⟩ := IsType.wrapForalls_inv henv (by trivial) hresultWF
  have hresultShape : result = mkApps (.const family.name (VLevel.params decl.uvars))
      result.getAppFnArgs.2 := by
    rw [← hhead]
    exact (mkApps_getAppFnArgs_eq result).symm
  rw [hresultShape] at hresult
  obtain ⟨_, hfamilyHead⟩ := VExpr.WF.of_mkApps henv hdomctx ⟨_, hresult⟩
  obtain ⟨ci, hci, _, hcount⟩ := HasType.const_inv henv hdomctx hfamilyHead
  rw [hname, hlookup] at hci
  cases Option.some.inj hci
  have hfamilyUvars : family.uvars = decl.uvars := by simpa using hcount.symm
  obtain ⟨normalized, ownParams, afterParams, indices, result', exprType,
    hnorm, hown, hidx, _, hres⟩ := Hshape
  have hnormEq : normalized = wrapForalls (ownParams ++ indices) result' := by
    rw [eq_wrapForalls_of_takeForalls hown, eq_wrapForalls_of_takeForalls hidx, wrapForalls_append]
  rw [hnormEq] at hnorm
  have htypeWF : env.IsType decl.uvars [] family.type := by
    have ht := henv.ordered.constWF hlookup
    change env.IsType family.uvars [] family.type at ht
    rwa [hfamilyUvars] at ht
  have hheader := IsDefEq.close_sort_header henv htypeWF hnorm
    (by simpa only [List.reverse_append] using hres)
  obtain ⟨u, H⟩ := H
  obtain ⟨_, hheadTyped⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, H⟩
  obtain ⟨ci, hci, hlevels, hlen⟩ := HasType.const_inv henv hΓ hheadTyped
  rw [hlookup] at hci
  cases Option.some.inj hci
  refine ⟨(ownParams ++ indices).map (·.instL levels), family.resultLevel.inst levels, ?_, ?_⟩
  · have hp := takeForalls_domains_length hown
    have hi := takeForalls_domains_length hidx
    simp only [List.length_map, List.length_append]
    omega
  · intro Δ hΔ
    have hconst := HasType.const (Γ := Δ) hlookup hlevels hlen
    have he := (hheader.instL hlevels).weak0 henv.ordered (Γ := Δ)
    have hc := hconst.defeqU_r henv hΔ he
    simpa only [instL_wrapForalls, instL] using hc

/-- A registered family used as a type is fully saturated at its parameter and
index count, even when the original stored header needs conversion to expose it. -/
theorem family_arity (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections name info)
    (H : env.IsType U Γ (mkApps (.const name levels) args)) :
    args.length = info.nparams + info.nindices := by
  obtain ⟨doms, w, hlen, hhead⟩ := family_head_telescope henv hΓ hinfo H
  obtain ⟨_, ht⟩ := H
  exact (HasType.mkApps_sort_arity henv hΓ (hhead hΓ) ht).trans hlen

end Lean4Lean.VEnv.Strengthening.StructureReplay
