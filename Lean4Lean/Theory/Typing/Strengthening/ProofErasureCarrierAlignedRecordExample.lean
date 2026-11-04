import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecordApplication

/-! # Two nested records with a varied dependent family parameter

The outer structure has a beta-expanded field type Inner (Sort u). Inner has one type parameter and
one field of that type. Changing u from max 0 0 to
0 changes both the inner family's universe and the parameter's sort annotation.
Carrier beta computation exposes the inner record. Only the deepest projections
carry an ordinary comparison premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

private theorem positive_field_not_proof
    (hshape : info.ctorType = wrapForalls ds result)
    (hlen : ds.length = info.nparams + info.numFields)
    (hj : info.nparams + j < ds.length)
    (hctx : OnCtx ((ds.map (instL ls)).take (info.nparams + j)).reverse (env.IsType univs))
    (hdom : env.HasType univs ((ds.map (instL ls)).take (info.nparams + j)).reverse
      (ds[info.nparams + j].instL ls) (.sort (.succ u))) :
    ¬ StructureReplay.ProofField env univs info ls j := by
  rintro ⟨ds', r', hj', Hshape, Hlen, Hprop⟩
  obtain ⟨rfl, _⟩ := VExpr.wrapForalls_inj_of_length (hlen.trans Hlen.symm) (hshape.symm.trans Hshape)
  have Hzero := (hdom.uniqU henv hctx Hprop).sort_inv henv hctx
  simp [VLevel.equiv_def, VLevel.eval] at Hzero

/-- Two recursive record levels retain their deepest endpoint check across
nonjoining outer universes. The inner parameter changes from Sort (max 0 0)
to Sort 0 after beta exposure; its field template is that parameter. Both
source fields are proved non-proof, so neither recursive check is omitted. Actual source
endpoints, projection registrations and both admissibility certificates are
inputs, rather than assumptions of recovery or carrier-conversion completeness. -/
theorem carrier_aligned_nested_record_parameter_variants
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hinner : env.projections inner innerInfo) (hpi : innerInfo.nparams = 1)
    (hxi : innerInfo.nindices = 0) (hfi : innerInfo.numFields = 1)
    (hshape : info.ctorType = .forallE
      (.app (.lam (.sort (.succ (.param 0))) (.bvar 0))
        (.app (.const inner [.succ (.param 0)]) (.sort (.param 0)))) (.const family [.param 0]))
    (hshapeInner : innerInfo.ctorType = .forallE (.sort (.param 0))
      (.forallE (.bvar 0) (.app (.const inner [.param 0]) (.bvar 1))))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family [.max .zero .zero]) (.sort u))
    (hS' : env.HasType univs Γ (.const family [.zero]) (.sort v))
    (ha : env.HasType univs Γ a (.const family [.max .zero .zero]))
    (hb : env.HasType univs Γ b (.const family [.max .zero .zero]))
    (hadm : (info.resultLevel.inst [.max .zero .zero]).IsNeverZero ∨
      StructureReplay.ProofFields env univs info [.max .zero .zero])
    (hadmInner : (innerInfo.resultLevel.inst [.succ (.max .zero .zero)]).IsNeverZero ∨
      StructureReplay.ProofFields env univs innerInfo [.succ (.max .zero .zero)])
    (Hfield : ComputedJointCompare Step (proofEraseCtx Γ) true
      (.proj inner 0 (.proj family 0 (proofErase Γ a)))
      (.proj inner 0 (.proj family 0 (proofErase Γ b)))) :
    (¬ StructureReplay.ProofField env univs info [.max .zero .zero] 0) ∧
    (¬ StructureReplay.ProofField env univs innerInfo [.succ (.max .zero .zero)] 0) ∧
    RecordCarrierGuard Step (proofEraseCtx Γ) (.const family [.max .zero .zero])
      (proofErase Γ a) (proofErase Γ b) ∧
    RecordCarrierGuard Step (proofEraseCtx Γ) (.const family [.zero])
      (proofErase Γ a) (proofErase Γ b) ∧
    (¬ ∃ out, ScopedCompute Step (proofEraseCtx Γ) (.const family [.max .zero .zero]) out ∧
      ScopedCompute Step (proofEraseCtx Γ) (.const family [.zero]) out) := by
  have hw : ∀ l ∈ [VLevel.max .zero .zero], l.WF univs := by simp; trivial
  have Hctor := henv.ordered.constWF (henv.ordered.projectionConstructor hi)
  have HT := ProjTele.of (U := univs) (S := family) henv (info := info)
    (doms := [.app (.lam (.sort (.succ (.param 0))) (.bvar 0))
      (.app (.const inner [.succ (.param 0)]) (.sort (.param 0)))])
    (c := family) (lsR := [.param 0]) (args := []) hshape Hctor hw
  obtain ⟨ids, ir, HTi⟩ := projection_telescope_exists hinner
    (show ∀ l ∈ [VLevel.succ (.max .zero .zero)], l.WF univs from by simp; trivial)
  obtain ⟨w, hF⟩ := HT.doms 0 (by simp)
  have hF' : env.HasType univs []
      (.app (.lam (.sort (.succ (.max .zero .zero))) (.bvar 0))
        (.app (.const inner [.succ (.max .zero .zero)]) (.sort (.max .zero .zero)))) (.sort w) := by
    simpa [instL, VLevel.inst] using hF
  have Ractual : VExpr.BetaRed
      (.app (.lam (.sort (.succ (.max .zero .zero))) (.bvar 0))
        (.app (.const inner [.succ (.max .zero .zero)]) (.sort (.max .zero .zero))))
      (.app (.const inner [.succ (.max .zero .zero)]) (.sort (.max .zero .zero))) := by
    simpa [VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN] using
      (VExpr.BetaRed.beta (A := .sort (.succ (.max .zero .zero))) (b := .bvar 0)
        (a := .app (.const inner [.succ (.max .zero .zero)]) (.sort (.max .zero .zero))))
  have hInner := (Ractual.simAt henv.orderedStrong henv.betaSubjectReduction (by trivial) _ hF').hasType.2
  have Rfield := proofErase_beta_forward (Γ := []) (by trivial) hF' Ractual
  have EF : proofErase [] (.app (.const inner [.succ (.max .zero .zero)]) (.sort (.max .zero .zero))) =
      .app (.const inner [.succ (.max .zero .zero)]) (.sort (.max .zero .zero)) := by
    have H := proofErase_const_spine (Γ := []) (args := [.sort (.max .zero .zero)])
      (by trivial) hInner (not_isProof_of_sort (Γ := []) (by trivial) hInner)
    have ES : proofErase [] (.sort (.max .zero .zero)) = .sort (.max .zero .zero) :=
      if_neg (not_isProof_of_sort (Γ := []) (by trivial)
        (HasType.sort (env := env) (U := univs) (l := .max .zero .zero) (by trivial)))
    simpa only [List.map_cons, List.map_nil, ES, ProofShape.mkApps, VExpr.mkApps, List.foldl_cons, List.foldl_nil] using H
  have hDom : env.HasType univs [] (.sort (.succ (.max .zero .zero)))
      (.sort (.succ (.succ (.max .zero .zero)))) := .sort (by trivial)
  have hBody : env.HasType univs [.sort (.succ (.max .zero .zero))]
      (.bvar 0) (.sort (.succ (.max .zero .zero))) := .bvar .zero
  have hFn := HasType.lam hDom hBody
  obtain ⟨_, _, hFn', hArg⟩ := hF'.app_inv henv (by trivial)
  have hArg' := argument_at_displayed_domain (Γ := []) (by trivial) hFn' hFn hArg
  have hPositive := hFn.app hArg'
  have HnotOuter : ¬ StructureReplay.ProofField env univs info [.max .zero .zero] 0 := by
    apply positive_field_not_proof
      (ds := [.app (.lam (.sort (.succ (.param 0))) (.bvar 0))
        (.app (.const inner [.succ (.param 0)]) (.sort (.param 0)))])
      hshape (by simp [hp, hf]) (by simp [hp])
    · simp only [hp, Nat.zero_add, List.take_zero, List.reverse_nil]; trivial
    · simpa [hp, instL, VLevel.inst, VExpr.inst] using hPositive
  have HnotInner : ¬ StructureReplay.ProofField env univs innerInfo [.succ (.max .zero .zero)] 0 := by
    apply positive_field_not_proof (ds := [.sort (.param 0), .bvar 0]) hshapeInner
      (by simp [hpi, hfi]) (by simp [hpi])
    · simpa [hpi, instL, VLevel.inst] using (show OnCtx [.sort (.succ (.max .zero .zero))]
        (env.IsType univs) from ⟨trivial, _, hDom⟩)
    · simpa [hpi, instL, VLevel.inst] using hBody
  have HG : RecordCarrierGuard Step (proofEraseCtx Γ) (.const family [.max .zero .zero])
      (proofErase Γ a) (proofErase Γ b) := by
    apply RecordCarrierGuard.nested hi hx (ps := []) hp.symm hadm HT
    intro i hj _
    have E : i = 0 := by omega
    subst i
    simp only [projectionType, hp, Nat.zero_add, List.take_zero, List.reverse_nil,
      List.getElem_cons_zero, instL, VLevel.inst, List.map_cons, List.map_nil,
      List.getD_cons_zero, projectionArgs, List.take_nil, List.range_zero,
      List.nil_append, ProofShape.instOuter]
    have Eid : ProofShape.Subst.ofList [] = ProofShape.Subst.id := by
      funext k
      simp [ProofShape.Subst.ofList, ProofShape.Subst.id]
    rw [Eid, ProofShape.subst_id]
    apply RecordCarrierGuard.beta Rfield
    rw [EF]
    apply RecordCarrierGuard.nested hinner hxi (ps := [.sort (.max .zero .zero)])
      (by simp [hpi]) hadmInner HTi
    intro j hji _
    have Ej : j = 0 := by omega
    subst j
    exact .checked Hfield
  have ES : proofErase Γ (.const family [.max .zero .zero]) = .const family [.max .zero .zero] :=
    if_neg (not_isProof_of_sort hΓ hS)
  have ES' : proofErase Γ (.const family [.zero]) = .const family [.zero] :=
    if_neg (not_isProof_of_sort hΓ hS')
  have V : StructuralVariant (proofErase Γ (.const family [.max .zero .zero]))
      (proofErase Γ (.const family [.zero])) := by
    rw [ES, ES']
    exact .const (.cons (by simp [VLevel.equiv_def, VLevel.eval]) .nil)
  refine ⟨HnotOuter, HnotInner, HG, ?_, ?_⟩
  · simpa only [ES'] using proofErase_carrier_aligned_record_variant hstep hΓ ha hb hS' V
      (by simpa only [ES] using HG)
  · rintro ⟨out, RA, RB⟩
    have EA := scoped_normal_fixed RA (fun _ => ⟨fun _ H => hn H, trivial⟩)
    have EB := scoped_normal_fixed RB (fun _ => ⟨fun _ H => hn H, trivial⟩)
    cases EA.symm.trans EB

end Lean4Lean.VEnv.Strengthening
