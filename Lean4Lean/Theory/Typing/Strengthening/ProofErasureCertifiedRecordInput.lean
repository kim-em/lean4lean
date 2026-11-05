import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedRecordEvidence

/-! # Native joins from actual alias-bearing record oracles

The input is an ordinary context lookup whose annotation is a full computational
descendant of a stored family alias. All joint observations, oracle valuations
and native readout obligations are derived from those concrete inputs.
-/
namespace Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier ObservedInput)
variable [Params] {evidence : FamilyEvidence}
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF
local notation "D₀" => PureObservation.Definitions.ofEnv env univs henv

/-- Independent family evidence at an actual lookup initializes an unknown
record value and its exact native oracle. No value observation is assumed. -/
theorem independent_record_input
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A)
    (HE : TypeEquality (proofEraseCtx Γ) (proofErase Γ A) (.atom RT))
    (HR : evidence.holds (proofEraseCtx Γ) (proofErase Γ A)) :
    (ObservedInput i .record).Typed U RT (proofEraseCtx Γ) ∧
      Valuation evidence U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) ∧
      Obs evidence U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) (.bvar i) .record := by
  have HT := HE.lookup_control hΓ hl
  refine ⟨?_, ?_, .var HT (by simp [Key.Valid]) ⟨rfl, rfl⟩⟩
  · rintro j k ⟨rfl, rfl⟩; exact HT
  · rintro j k ⟨rfl, rfl⟩
    have E := erasedTypeOracle_valid hΓ hl
    rw [← proofEraseCtx_oracle] at E
    exact E ▸ Obs.record_type HE HR

/-- An actual stored alias and the annotation's computational provenance
supply the record's value/oracle observations. The parameter is ordinarily typed;
no native recovery for that parameter or for the unknown record is requested. -/
theorem stored_alias_record_input
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A)
    (hp : env.HasType univs Γ p (Q.control U).expr)
    (HD : (D₀).unfolds name [] (.app (.const t []) p))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ)
      (proofErase Γ (.const name [])) (proofErase Γ A)) :
    (ObservedInput i .record).Typed U RT (proofEraseCtx Γ) ∧
      Valuation (aliasEvidence t) U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) ∧
      Obs (aliasEvidence t) U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) (.bvar i) .record := by
  obtain ⟨HE, HR⟩ := AliasDemandProfile.stored_family_evidence hi hS Q hTag hF hΓ hp HD
  exact independent_record_input hi hS Q hTag hF hΓ hl
    (HE.compute (erased_static_structure_eta_expansion_union_descent heq
      (PureObservation.Definitions.ofEnv_sound henv)) RP)
    (alias_family_preserves heq hcon (henv.projectionRigid hTag) RP HR)

/-- The earlier joint grammar cannot admit a stored alias as a record-family
annotation. This is a grammar boundary, not a failure of ordinary conversion. -/
theorem stored_alias_not_dependent_record_observation
    (hrig : env.Rigid family)
    (HD : (D₀).unfolds name [] rhs) :
    ¬ DependentRecordDemand.Obs unit record parameter uc ctor family Δ S (.const name []) (.type .record) := by
  intro H
  cases H with
  | record_type _ HR => exact AliasDemandProfile.stored_alias_not_rigid_observation hrig HD HR

include hTag hF in
/-- An unknown record with an actual alias-derived lookup annotation has a
canonical native/assigned join after arbitrary term computation, selected native
recovery, native conversion, and raw substitution. All observer, valuation,
family-preservation and target-native premises are discharged concretely. -/
theorem stored_alias_record_native_assigned_join
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A)
    (hp : env.HasType univs Γ p (Q.control U).expr)
    (HD : (D₀).unfolds name [] (.app (.const t []) p))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ)
      (proofErase Γ (.const name [])) (proofErase Γ A))
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort u))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ) (.bvar i) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ) T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) := by
  obtain ⟨HS, HV, H⟩ := stored_alias_record_input hi hS Q hTag hF heq hcon hΓ hl hp HD RP
  exact program_alias_native_assigned_join hi hS Q hTag hF heq hcon hcf hU hT H HS HV
    (by rintro j k ⟨rfl, rfl⟩; trivial) hΓ' hAssigned RE RN RA RB

end Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
