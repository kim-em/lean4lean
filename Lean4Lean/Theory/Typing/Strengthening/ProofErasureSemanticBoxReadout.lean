import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSemanticSortReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureBox

/-! # Semantic carrier readout is closed under Box

The field readout is an explicit local property of the target parameter.
Rigid-head injectivity identifies an arbitrary exposed source Box and its
actually equal parameter. Recursive field checking then uses that parameter
property; source carrier computation is handled by forward typed replay.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private BoxCarrierAlignment.projection_recipe BoxCarrierAlignment.family_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment
variable [Params]

/-- At this target and actual context, every carrier guard at an equal typed
source can be read at the target. No endpoint typings or source type-comparison
certificates are assumed. This definition is a local closure property, not a
coverage assertion for arbitrary targets. -/
def CarrierReadoutAt (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ : List VExpr) (C : VExpr) : Prop :=
  ∀ {A u a b}, env.HasType univs Γ A (.sort u) → env.IsDefEqU univs Γ A C →
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) a b →
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ C) a b

/-- Actual equality to a sort supplies its local readout property. -/
theorem CarrierReadoutAt.sort
    (hstep : ErasedScopedPrimitiveDescent Step) (hΓ : OnCtx Γ (env.IsType univs)) :
    CarrierReadoutAt Step Γ (.sort v) :=
  fun hA HE H => .carrierChecked (proofErase_joint_carrier_semantic_sort hstep hΓ hA HE H)

/-- A typed closed rigid constant supplies its local readout property. -/
theorem CarrierReadoutAt.closed
    (hstep : ErasedScopedPrimitiveDescent Step) (hr : env.Rigid family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ (.const family []) (.sort v)) :
    CarrierReadoutAt Step Γ (.const family []) := by
  intro A u a b hA HE H
  rw [show proofErase Γ (.const family []) = .const family [] from
    if_neg (not_isProof_of_sort hΓ hC)]
  exact proofErase_joint_carrier_to_closed_rigid hstep hr hΓ hA HE H

private theorem box_source_parameter
    (hi : env.projections family info) (hi' : env.projections source info')
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.app (.const family []) C))
    (EA : proofErase Γ A = ProofShape.mkApps (.const source ls) ps) :
    source = family ∧ ls = [] ∧ ∃ B, ps = [proofErase Γ B] ∧
      env.HasType univs Γ B (.sort (.succ .zero)) ∧ env.IsDefEqU univs Γ B C := by
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv EA
  obtain ⟨rfl, HL, HA⟩ := henv.headInversion.rigid_rigid (args' := [C]) hΓ
    (henv.projectionRigid hi') (henv.projectionRigid hi) (HE.typeChain henv hΓ hA)
  cases HL
  cases HA with
  | cons HB Hnil =>
    cases Hnil
    obtain ⟨_, _, hfn, hB⟩ := hA.app_inv henv hΓ
    have hBT := argument_at_displayed_domain hΓ hfn (BoxCarrierAlignment.family_typed hc) hB
    exact ⟨rfl, rfl, _, Eargs, hBT, HB⟩

private theorem box_readout_raw
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) (HC : CarrierReadoutAt Step Γ C)
    (H : JointCheck Step Δ kind a b)
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.app (.const family []) C))
    (EΓ : proofEraseCtx Γ = Δ)
    (E : JointCheckKind.carrier (proofErase Γ A) = kind) :
    JointCarrierGuard Step Δ (.app (.const family []) (proofErase Γ C)) a b := by
  induction H generalizing A u with
  | carrierChecked H => exact .carrierChecked H
  | carrierFunction =>
    obtain ⟨D, B, rfl, _, _, _⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
    exact (henv.headInversion.forallE_rigid (args := [C]) hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ hA)).elim
  | carrierSubsingleton HS =>
    cases HS with
    | unit hi' hz' hf' hp' =>
      obtain ⟨rfl, _, _⟩ := box_source_parameter hi hi' hc hΓ hA HE (JointCheckKind.carrier.inj E)
      cases henv.ordered.projections_unique hi hi'
      omega
    | forallE HS =>
      obtain ⟨D, B, rfl, _, _, _⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
      exact (henv.headInversion.forallE_rigid (args := [C]) hΓ (henv.projectionRigid hi)
        (HE.typeChain henv hΓ hA)).elim
  | carrierSymm H ih => exact .carrierSymm (ih hA HE EΓ E)
  | carrierReduce RA RB H ih => exact .carrierReduce RA RB (ih hA HE EΓ E)
  | carrierCompute R H ih =>
    obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ
      (JointCheckKind.carrier.inj E) R
    exact ih HA.hasType.2 (HA.symm.toU.trans henv hΓ HE) EΓ (congrArg JointCheckKind.carrier EA)
  | carrierIntro hi' hz' hp' hadm' HF =>
    obtain ⟨rfl, rfl, B, rfl, hB, HBC⟩ :=
      box_source_parameter hi hi' hc hΓ hA HE (JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    exact .carrierIntro hi hz (ps := [proofErase Γ C]) (by simp [hp]) (.inl hadm) HF
  | carrierNested hi' hz' hp' hadm' HT HF =>
    obtain ⟨rfl, rfl, B, rfl, hB, HBC⟩ :=
      box_source_parameter hi hi' hc hΓ hA HE (JointCheckKind.carrier.inj E)
    cases henv.ordered.projections_unique hi hi'
    apply JointCheck.carrierNested hi hz (ps := [proofErase Γ C]) (by simp [hp]) (.inl hadm) HT
    intro i hj hn
    have hi0 : i = 0 := by omega
    subst i
    have HG := HF 0 (by omega) hn
    rw [BoxCarrierAlignment.projection_recipe hp hf hshape HT] at HG ⊢
    rw [← EΓ] at HG ⊢
    exact HC hB HBC HG
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- Local semantic readout of the parameter supplies readout of Box itself.
The source may have arbitrary carrier computation prefixes and a different
actual parameter. Its recursive field guard is transported by the supplied
parameter property; no common comparison of its value fields is required. -/
theorem CarrierReadoutAt.box
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ C (.sort (.succ .zero))) (HC : CarrierReadoutAt Step Γ C) :
    CarrierReadoutAt Step Γ (.app (.const family []) C) := by
  intro A u a b hA HE H
  have hfn := BoxCarrierAlignment.family_typed (Γ := Γ) hc
  have EC : proofErase Γ (.app (.const family []) C) = .app (.const family []) (proofErase Γ C) := by
    rw [show proofErase Γ (.app (.const family []) C) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ (hfn.app hC)),
      show proofErase Γ (.const family []) = .const family [] from
        if_neg (not_isProof_function_to_sort hΓ hfn)]
  rw [EC]
  exact box_readout_raw hstep hi hp hf hz hadm hshape hc hΓ HC H hA HE rfl rfl

end Lean4Lean.VEnv.Strengthening
