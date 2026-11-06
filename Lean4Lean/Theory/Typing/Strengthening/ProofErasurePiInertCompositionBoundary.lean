import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEvidence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredUnitImages

/-! # Pi-inert comparison is not a complete strong-derivation predicate

Actual commonly typed empty-structure variables expose a boundary that survives
all future substitutions and full-core residuals. Two retained comparisons
through the constructor exist, but no Pi-inert stage compares the variables.
This refutes comparison composition for this predicate, not strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : Definitions}

/-- Pi-inert primitives cannot rewrite a variable root; the permitted sort
roots do not affect this property. -/
theorem pi_inert_stage_no_bvar (H : PiInertStage D n Δ (.bvar i) out) : False := by
  rcases H.2 with H | ⟨u, H⟩
  · exact H
  · cases H

/-- Compatible Pi-inert computation leaves each bare variable fixed. -/
theorem ProofShape.ScopedCompute.pi_inert_bvar_fixed
    (R : ScopedCompute (PiInertStage D n) Δ (.bvar i) out) : out = .bvar i :=
  scoped_normal_fixed R (fun _ => ⟨fun _ H => pi_inert_stage_no_bvar H, trivial⟩)

/-- Neither comparison mode can equate distinct variables at any Pi-inert
stage, even though raw carrier checking can express their unit-like equality. -/
theorem ProofShape.ComputedJointCompare.pi_inert_bvar_injective
    (H : ComputedJointCompare (PiInertStage D n) Δ mode (.bvar i) (.bvar j)) : i = j := by
  generalize EA : ProofShape.bvar i = a at H
  generalize EB : ProofShape.bvar j = b at H
  change ComputedJointCheck (PiInertStage D n) Δ (.compare mode) a b at H
  generalize hk : JointCheckKind.compare mode = kind at H
  induction H generalizing mode i j with
  | leaf H =>
    cases H with
    | refl => exact ProofShape.bvar.inj (EA.trans EB.symm)
    | sort | const => cases EA
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.trans E
  | compute RA RB H ih =>
    exact ih ((EA ▸ RA).pi_inert_bvar_fixed).symm ((EB ▸ RB).pi_inert_bvar_fixed).symm hk
  | symm H ih => exact (ih EB EA hk).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EA
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | etaBodyR => cases EB
  | app | appCarrier | appComputed | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EA
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- A nullary empty-structure constructor compares with every raw shape after
all core computations. Its rigid head survives; universes may change. -/
theorem pi_inert_unit_constructor_interpret
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs) :
    PiInertInterpret D n (.compare true) Δ (.const info.ctorName ls) a := by
  intro left right RL _
  have hroot : ConstantRootLevels (fun _ => ErasedLevelCore D) info.ctorName := by
    intro Δ levels out R
    rcases R with R | R
    · exact (erased_iota_primitive_no_rigid (henv.projectionCtorRigid hi) hD R rfl).elim
    · cases R with
      | const HL _ => exact ⟨_, rfl, HL⟩
  obtain ⟨ls', rfl, _⟩ := (RL.scoped (Δ := Δ) (fun R => .base R)).const_levels_inv @hroot
  exact .structFields hi hx (ps := []) hp.symm (fields := []) hf.symm
    (.inr (StructureReplay.ProofFields.of_no_fields hf)) (by intro i h; simp at h)

/-- The constructor bridge retains every typed substitution, including ones
that expose new computation in the other endpoint. -/
theorem pi_inert_unit_constructor_evidence
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs) :
    PiInertEvidence D n (.compare true) Δ (.const info.ctorName ls) a := by
  refine ⟨pi_inert_unit_constructor_interpret hi hp hx hf hD, ?_⟩
  intro Δ' τ _ left right RL RR
  exact pi_inert_unit_constructor_interpret hi hp hx hf hD RL RR

/-- An actual commonly typed constructor is a bridge of hereditary interpreted
comparisons between distinct unit variables. The endpoints are strongly equal,
but their composite has no Pi-inert comparison at any finite stage or mode.
Thus actual middle typing and future stability do not suffice for composition. -/
theorem pi_inert_unit_typed_composition_failure
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    env.IsDefEqStrong univs Γ (.bvar i) (.bvar j) (.const family ls) ∧
    ∃ m, env.HasType univs Γ m (.const family ls) ∧
      PiInertEvidence D 0 (.compare true) (proofEraseCtx Γ)
        (proofErase Γ (.bvar i)) (proofErase Γ m) ∧
      PiInertEvidence D 0 (.compare true) (proofEraseCtx Γ)
        (proofErase Γ m) (proofErase Γ (.bvar j)) ∧
      ∀ n mode, ¬ PiInertEvidence D n (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
  have hm : env.HasType univs Γ (.const info.ctorName ls) (.const family ls) :=
    hiT.unitLike_constructor henv hΓ hi (params := []) hp.symm hx hf
  have Em : proofErase Γ (.const info.ctorName ls) = .const info.ctorName ls :=
    if_neg (not_proof_at_positive_type hΓ hS hm)
  refine ⟨(IsDefEq.unitLike hi (params := []) hp.symm hx hf hiT hjT).strong henv.orderedStrong hΓ,
    _, hm, ?_, ?_, ?_⟩
  · rw [Em]
    exact (pi_inert_unit_constructor_evidence hi hp hx hf hD).symm
  · rw [Em]
    exact pi_inert_unit_constructor_evidence hi hp hx hf hD
  · intro n mode H
    have HC := H.base .refl .refl
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg (not_proof_at_positive_type hΓ hS hiT),
      show proofErase Γ (.bvar j) = .bvar j from if_neg (not_proof_at_positive_type hΓ hS hjT)] at HC
    exact hne HC.pi_inert_bvar_injective

/-- The ambient stage already contains the missing operation: native empty
structure expansion can change a bare variable into its constructor. Both
variables join after one stage when their exact family is in the context. -/
theorem static_stage_unit_variables_compare
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (Hi : contextOracle Δ i = .const family ls)
    (Hj : contextOracle Δ j = .const family ls) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 1) Δ mode (.bvar i) (.bvar j) := by
  have expand {k} (Hk : contextOracle Δ k = .const family ls) :
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ (.bvar k) (.const info.ctorName ls) := by
    have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ
        (.bvar k) (.const family ls) := Hk ▸ .bvar
    have R : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D 0) Δ
        (.bvar k) (nativeStructureOutput family info ls [] (.bvar k)) :=
      .intro hi hx (.inr (StructureReplay.ProofFields.of_no_fields hf)) hp.symm RN
    have R' : ErasedStaticStructureEtaExpansionStage D 1 Δ
        (.bvar k) (nativeStructureOutput family info ls [] (.bvar k)) :=
      .inr (.inr (.inr (.inr (.inr R))))
    simpa only [nativeStructureOutput, hf, List.range_zero, List.map_nil, List.append_nil, ProofShape.mkApps] using
      (ScopedCompute.base R')
  exact .compute (expand Hi) (expand Hj) (.leaf .refl)

/-- A closed positive empty structure provides an actual context witnessing
failure of the proposed strong-transitivity induction predicate. Both links
retain every future typed substitution and full-core residual. No Pi-inert
output stage works, while the ambient stage compares the endpoints at one. -/
theorem pi_inert_unit_composition_context
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ a m b A, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ a A ∧ env.HasType univs Γ m A ∧ env.HasType univs Γ b A ∧
      env.IsDefEqStrong univs Γ a b A ∧
      PiInertEvidence D 0 (.compare true) (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ m) ∧
      PiInertEvidence D 0 (.compare true) (proofEraseCtx Γ) (proofErase Γ m) (proofErase Γ b) ∧
      (∀ n mode, ¬ PiInertEvidence D n (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ a) (proofErase Γ b)) ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) true
        (proofErase Γ a) (proofErase Γ b) := by
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hSΓ : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have h₀ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  obtain ⟨HE, m, hm, HL, HR, HN⟩ := pi_inert_unit_typed_composition_failure
    hi hp hx hf hD hΓ hSΓ h₀ h₁ (by decide)
  refine ⟨Γ, .bvar 0, m, .bvar 1, S, hΓ, h₀, hm, h₁, HE, HL, HR, HN, ?_⟩
  have E : proofErase Γ S = .const family ls := if_neg (not_isProof_of_sort hΓ hSΓ)
  have H₀ : contextOracle (proofEraseCtx Γ) 0 = .const family ls := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ (show Lookup Γ 0 S from .zero), E]
  have H₁ : contextOracle (proofEraseCtx Γ) 1 = .const family ls := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ (show Lookup Γ 1 S from .succ .zero), E]
  rw [show proofErase Γ (.bvar 0) = .bvar 0 from if_neg (not_proof_at_positive_type hΓ hSΓ h₀),
    show proofErase Γ (.bvar 1) = .bvar 1 from if_neg (not_proof_at_positive_type hΓ hSΓ h₁)]
  exact static_stage_unit_variables_compare hi hp hx hf H₀ H₁

end Lean4Lean.VEnv.Strengthening
