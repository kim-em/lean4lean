import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePolyAliasFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedRecordInput

/-! # Alias-native joins in the full environment computation collection

Independent alias preservation now includes selected structure equations and
optional quotient repair. The generic joint native induction is reused unchanged.
Readout still needs only actual stored equations, which embed in the target core.
-/
namespace Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier HeadFree)
variable [Params]

/-- Universe-indexed stored observations implement the generic joint interface. -/
def polyAliasEvidence (family : Name) : FamilyEvidence where
  holds Δ e := PolyAliasDemandProfile.Obs family 1 Δ (fun _ _ _ => False) e .sort .pi
  subst H W := H.subst W (by intro i t k h; cases h)
  beta H := H.beta_forward (by intro i t k h; cases h)

/-- The family-evidence interface is preserved by every sound collection that
agrees with stored alias bodies and does not unfold the designated rigid family. -/
theorem coherent_poly_alias_family_preserves
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hag : StoredAgreement D)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid family) (hD : ∀ ls rhs, ¬ D.unfolds family ls rhs) :
    FamilyPreserves (ErasedStaticStructureEtaExpansionUnion D) (polyAliasEvidence family) :=
  fun R H => H.coherent_union heq hs hag hcon hc hD R (fun _ _ _ h => h.elim)

/-- Actual environment metadata discharges all extra collection assumptions. -/
theorem environment_poly_alias_family_preserves
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid family) :
    FamilyPreserves (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (polyAliasEvidence family) :=
  coherent_poly_alias_family_preserves heq EnvironmentCore.sound EnvironmentCore.storedAgreement
    hcon hc (EnvironmentCore.no_rigid hc)

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF
local notation "D₀" => PureObservation.Definitions.ofEnv env univs henv

/-- Every full term/native/type history from an alias-certified program exposes
its native family after arbitrary raw substitution. Independent evidence
laws follow from stored-body agreement; readout uses the actual stored core. -/
theorem program_coherent_poly_alias_native_head_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hag : StoredAgreement D)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (H : Obs (polyAliasEvidence t) U RT (Q.control U) uc c t Δ S source .record)
    (HS : S.Typed U RT Δ) (HV : Valuation (polyAliasEvidence t) U RT (Q.control U) uc c t Δ S)
    (HF : ∀ i key, S i key → HeadFree key)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ T out) :
    ∃ a, Compute (ErasedIotaPrimitive D₀) (out.subst σ) (.app (.const t []) a) := by
  apply program_native_readout hi hS Q hTag hF
    (P := fun e => ∃ a, Compute (ErasedIotaPrimitive D₀) e (.app (.const t []) a))
    (σ := σ) heq hs
    (coherent_poly_alias_family_preserves heq hs hag hcon (henv.projectionRigid hTag) hf)
    (fun R HH => by obtain ⟨a, HA⟩ := HH; exact ⟨a, (Compute.beta R).trans HA⟩)
    (fun a => ⟨a, .refl⟩)
    (fun HE HR => PolyAliasDemandProfile.family_head hi hS Q hTag hF HE HR)
    huc hc hf
    H HS HV HF RE RN RA

/-- Actual target declaration data joins substituted native histories with
independent assigned-family computation. The source's alias evidence survives
term computation, native selection and the entire native conversion tail. -/
theorem program_environment_poly_alias_native_assigned_join
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (H : Obs (polyAliasEvidence t) U RT (Q.control U) uc c t Δ S source .record)
    (HS : S.Typed U RT Δ) (HV : Valuation (polyAliasEvidence t) U RT (Q.control U) uc c t Δ S)
    (HF : ∀ i key, S i key → HeadFree key)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort u))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) Δ source image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) Δ image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) Δ T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) := by
  obtain ⟨a, HA⟩ := program_coherent_poly_alias_native_head_readout hi hS Q hTag hF (σ := σ)
    heq EnvironmentCore.sound EnvironmentCore.storedAgreement hcon
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hTag))
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag)) H HS HV HF RE RN RA
  have HN := Q.stored_family_native (D := EnvironmentCore.definitions) hi hS hΓ' hcf hU hT
  have HC := Q.caller_telescope hi hS heq EnvironmentCore.sound hΓ' (B := proofErase ((Q.control U).expr :: Γ') B) .nil
  refine ⟨(HA.scoped (fun R => .base ⟨0, .inl (.inl (EnvironmentCore.stored_primitive R))⟩)).trans (HC.compute (args := [a]) HN rfl), ?_⟩
  exact Q.environment_stored_family_return hi hS heq hTag rfl hcf hU hT hΓ' hAssigned RB

end Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
