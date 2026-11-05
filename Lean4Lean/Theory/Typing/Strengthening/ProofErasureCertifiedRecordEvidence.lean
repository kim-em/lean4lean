import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedRecordReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasDemandReturn

/-! # Concrete independent evidence for the joint native observer

Both the earlier rigid observer and the stored-alias observer implement the
structural interface. Their computation laws are established independently of
joint native induction; the alias instance uses actual stored definitions.
-/
namespace Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier HeadFree)
variable [Params] {evidence : FamilyEvidence} {family : Name}

/-- The earlier dependent rigid observer implements the structural interface. -/
def rigidEvidence (family : Name) : FamilyEvidence where
  holds Δ e := RigidDemandProfile.Obs family 1 Δ (fun _ _ _ => False) e .sort .pi
  subst H W := H.subst W (by intro i t k h; cases h)
  beta H := H.beta_forward (by intro i t k h; cases h)

/-- Finite stored alias chains implement the same structural interface. -/
def aliasEvidence (family : Name) : FamilyEvidence where
  holds Δ e := AliasDemandProfile.Obs family 1 Δ (fun _ _ _ => False) e .sort .pi
  subst H W := H.subst W (by intro i t k h; cases h)
  beta H := H.beta_forward (by intro i t k h; cases h)

/-- Previous joint observations embed whenever their rigid family evidence
embeds. All annotation and value demands remain unchanged. -/
theorem Obs.of_dependent
    (hfamily : ∀ {Δ e}, RigidDemandProfile.Obs family 1 Δ (fun _ _ _ => False) e .sort .pi → evidence.holds Δ e)
    (H : DependentRecordDemand.Obs unit record parameter uc ctor family Δ S e key) :
    Obs evidence unit record parameter uc ctor family Δ S e key := by
  induction H with
  | var HT HK hi => exact .var HT HK hi
  | unit_ctor HT => exact .unit_ctor HT
  | record_ctor HT => exact .record_ctor HT
  | family HT => exact .family HT
  | family_type HE => exact .family_type HE
  | record_type HE HR => exact .record_type HE (hfamily HR)
  | unit_type HE => exact .unit_type HE
  | univ HK HE => exact .univ HK HE
  | app HT _ _ ihf iha => exact .app HT ihf iha
  | lam HT HE HK _ _ ihA ihb => exact .lam HT HE HK ihA ihb
  | pi HT HE HK _ _ ihA ihb => exact .pi HT HE HK ihA ihb

/-- Specializing the interface to rigid evidence gives exactly the earlier
joint grammar, including every dependent annotation demand. -/
theorem Obs.to_dependent
    (H : Obs (rigidEvidence family) unit record parameter uc ctor family Δ S e key) :
    DependentRecordDemand.Obs unit record parameter uc ctor family Δ S e key := by
  induction H with
  | var HT HK hi => exact .var HT HK hi
  | unit_ctor HT => exact .unit_ctor HT
  | record_ctor HT => exact .record_ctor HT
  | family HT => exact .family HT
  | family_type HE => exact .family_type HE
  | record_type HE HR => exact .record_type HE HR
  | unit_type HE => exact .unit_type HE
  | univ HK HE => exact .univ HK HE
  | app HT _ _ ihf iha => exact .app HT ihf iha
  | lam HT HE HK _ _ ihA ihb => exact .lam HT HE HK ihA ihb
  | pi HT HE HK _ _ ihA ihb => exact .pi HT HE HK ihA ihb

/-- The reusable interface conservatively generalizes the previous observer. -/
theorem rigid_observation_iff :
    Obs (rigidEvidence family) unit record parameter uc ctor family Δ S e key ↔
      DependentRecordDemand.Obs unit record parameter uc ctor family Δ S e key :=
  ⟨Obs.to_dependent, Obs.of_dependent (fun H => H)⟩

/-- Rigid evidence preserves the earlier arbitrary-sound-collection behavior. -/
theorem rigid_family_preserves
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid family) (hD : ∀ ls rhs, ¬ D.unfolds family ls rhs) :
    FamilyPreserves (ErasedStaticStructureEtaExpansionUnion D) (rigidEvidence family) :=
  fun R H => H.static_structure_union heq hs hc hD R (fun _ _ _ h => h.elim)

/-- Actual stored aliases have full independent preservation. There is no
joint-observer or native-induction assumption in this implementation. -/
theorem alias_family_preserves
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid family) :
    FamilyPreserves (ErasedStaticStructureEtaExpansionUnion
      (PureObservation.Definitions.ofEnv env univs henv)) (aliasEvidence family) :=
  fun R H => H.static_structure_union heq hcon hc R (fun _ _ _ h => h.elim)

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF
local notation "D₀" => PureObservation.Definitions.ofEnv env univs henv

/-- Every full term/native/type history from an alias-certified program exposes
its native family after arbitrary raw substitution. All independent evidence
laws and rigid-head exclusions are discharged by the actual environment. -/
theorem program_alias_native_head_readout
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : Obs (aliasEvidence t) U RT (Q.control U) uc c t Δ S source .record)
    (HS : S.Typed U RT Δ) (HV : Valuation (aliasEvidence t) U RT (Q.control U) uc c t Δ S)
    (HF : ∀ i key, S i key → HeadFree key)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) Δ source image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D₀) Δ image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) Δ T out) :
    ∃ a, Compute (ErasedIotaPrimitive D₀) (out.subst σ) (.app (.const t []) a) := by
  have hsound : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  apply program_native_readout hi hS Q hTag hF
    (P := fun e => ∃ a, Compute (ErasedIotaPrimitive D₀) e (.app (.const t []) a))
    (σ := σ) heq hsound
    (alias_family_preserves heq hcon (henv.projectionRigid hTag))
    (fun R HH => by obtain ⟨a, HA⟩ := HH; exact ⟨a, (Compute.beta R).trans HA⟩)
    (fun a => ⟨a, .refl⟩)
    (fun HE HR => AliasDemandProfile.family_head hi hS Q hTag hF HE HR)
    (fun _ _ => PureObservation.Definitions.ofEnv_no_rigid henv (henv.projectionCtorRigid hi))
    (fun _ _ => PureObservation.Definitions.ofEnv_no_rigid henv (henv.projectionCtorRigid hTag))
    (fun _ _ => PureObservation.Definitions.ofEnv_no_rigid henv (henv.projectionRigid hTag))
    H HS HV HF RE RN RA

/-- Actual target declaration data joins substituted native histories with
independent assigned-family computation. The source's alias evidence survives
term computation, native selection and the entire native conversion tail. -/
theorem program_alias_native_assigned_join
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (H : Obs (aliasEvidence t) U RT (Q.control U) uc c t Δ S source .record)
    (HS : S.Typed U RT Δ) (HV : Valuation (aliasEvidence t) U RT (Q.control U) uc c t Δ S)
    (HF : ∀ i key, S i key → HeadFree key)
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort u))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) Δ source image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D₀) Δ image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) Δ T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D₀) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) := by
  have hsound : (D₀).Sound env univs := PureObservation.Definitions.ofEnv_sound henv
  obtain ⟨a, HA⟩ := program_alias_native_head_readout hi hS Q hTag hF (σ := σ) heq hcon H HS HV HF RE RN RA
  have HN := Q.stored_family_native (D := D₀) hi hS hΓ' hcf hU hT
  have HC := Q.caller_telescope hi hS heq hsound hΓ' (B := proofErase ((Q.control U).expr :: Γ') B) .nil
  refine ⟨(HA.scoped (fun R => .base ⟨0, .inl (.inl R)⟩)).trans (HC.compute (args := [a]) HN rfl), ?_⟩
  simpa only [ProofShape.subst_id] using Q.family_substitution_return hi hS (σ := Subst.id)
    heq hsound hsound hTag rfl
    (fun _ _ => PureObservation.Definitions.ofEnv_no_rigid henv (henv.projectionRigid hTag))
    hΓ' hΓ' hAssigned HN RB

end Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
