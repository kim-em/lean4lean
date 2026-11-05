import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePolyAliasNative
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionAliasFormation

/-! # Native joins from applied function aliases

An actual record annotation may descend from an applied registered lambda.
The lambda computes its family parameter from an arbitrarily typed argument,
including a proof. All parameter observations come from registry typing.
-/
namespace Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier ObservedInput)
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF
local notation "D₀" => PureObservation.Definitions.ofEnv env univs henv

/-- An applied registered lambda and the annotation's computational provenance
supply the record's observations. The supplied argument needs ordinary typing;
the dependent family parameter needs no additional certificate. -/
theorem environment_function_alias_record_input
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A)
    (hreg : env.definitionRegistry name = some value) (hname : value.name = name)
    (hbody : value.value = .lam Dom (.app (.const t []) p))
    (hw : ∀ l ∈ levels, l.WF univs) (hlv : levels.length = value.uvars)
    (hx : env.HasType univs Γ x (Dom.instL levels))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const name levels) x)) (proofErase Γ A)) :
    (ObservedInput i .record).Typed U RT (proofEraseCtx Γ) ∧
      Valuation (polyAliasEvidence t) U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) ∧
      Obs (polyAliasEvidence t) U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) (.bvar i) .record := by
  obtain ⟨HE, HR⟩ := PolyAliasDemandProfile.registered_function_application_evidence hi hS Q hTag hF hreg hname hbody hw hlv hΓ hx
  exact independent_record_input hi hS Q hTag hF hΓ hl
    (HE.compute (erased_static_structure_eta_expansion_union_descent heq
      EnvironmentCore.sound) RP)
    (environment_poly_alias_family_preserves heq hcon (henv.projectionRigid hTag) RP HR)

include hTag hF in
/-- An unknown record with an actual alias-derived lookup annotation has a
canonical native/assigned join after arbitrary term computation, selected native
recovery, native conversion, and raw substitution. All observer, valuation,
family-preservation and target-native premises are discharged concretely. -/
theorem environment_function_alias_record_native_assigned_join
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A)
    (hreg : env.definitionRegistry name = some value) (hname : value.name = name)
    (hbody : value.value = .lam Dom (.app (.const t []) p))
    (hw : ∀ l ∈ levels, l.WF univs) (hlv : levels.length = value.uvars)
    (hx : env.HasType univs Γ x (Dom.instL levels))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const name levels) x)) (proofErase Γ A))
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort u))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) (.bvar i) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) := by
  obtain ⟨HS, HV, H⟩ := environment_function_alias_record_input hi hS Q hTag hF heq hcon hΓ hl hreg hname hbody hw hlv hx RP
  exact program_environment_poly_alias_native_assigned_join hi hS Q hTag hF heq hcon hcf hU hT H HS HV
    (by rintro j k ⟨rfl, rfl⟩; trivial) hΓ' hAssigned RE RN RA RB

end Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
