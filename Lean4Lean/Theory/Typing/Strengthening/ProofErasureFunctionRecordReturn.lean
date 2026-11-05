import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionRecordCanonical

/-! # Whole-constructor native return with retained function parameters

The constructor term may compute arbitrarily before native recovery. Joint
value/type preservation covers beta, structure, eta, identity and changed
annotations; computational readout returns every future native result to one
family instance. No constructor-head ancestry restriction remains.
-/
namespace Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets unitCarrier)
variable [Params] {D : PureObservation.Definitions}
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0
  [.forallE (.const s []) (.const s [])] t c))
variable (hF : env.HasType univs [] (.const t [])
  (.forallE (.forallE (.const s []) (.const s [])) (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS hTag hF

/-- The free program input is a unit endofunction with no demanded input value. -/
def FunctionSets (unit : AtomicControl.Atom) (i : Nat) : Sets :=
  fun j key => j = i ∧ key = .fn (.atom unit) [] .unit

/-- Actual lookup and registered constructor typing initialize both valuations
and the constructor observation. The fresh oracle is an ordinary unit-function
type equality, while the constructor's dependent family parameter stays observed. -/
theorem initial_observation
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s []))) :
    (FunctionSets U i).Typed U RT (proofEraseCtx Γ) ∧
    Valuation U RT uc c t (proofEraseCtx Γ) (FunctionSets U i) ∧
    Obs U RT uc c t (proofEraseCtx Γ) (FunctionSets U i) (.app (.const c []) (.bvar i)) .record := by
  have hx : env.HasType univs Γ (.bvar i)
      (HeterogeneousControl.ControlType.arrow (.atom U) (.atom U)).expr := .bvar hl
  have EX : proofErase Γ (.bvar i) = .bvar i := if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hx)
  have HX : HeterogeneousControl.ControlTyping (proofEraseCtx Γ) (.bvar i) (.arrow (.atom U) (.atom U)) :=
    ⟨Γ, _, hΓ, rfl, hx, EX⟩
  have hf : env.HasType univs Γ (.const c [])
      (HeterogeneousControl.ControlType.arrow (.arrow (.atom U) (.atom U)) (.atom RT)).expr :=
    (constructor_simple_arrow hi hS hTag hF).weak0 henv.ordered
  have he : env.HasType univs Γ (.app (.const c []) (.bvar i)) (HeterogeneousControl.ControlType.atom RT).expr := .app hf hx
  have EC : proofErase Γ (.const c []) = .const c [] := if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hf)
  have EE : proofErase Γ (.app (.const c []) (.bvar i)) = .app (.const c []) (.bvar i) := by
    rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg (HeterogeneousControl.ControlType.not_isProof hΓ he), EC, EX]
  refine ⟨?_, ?_, .app ⟨Γ, _, hΓ, rfl, he, EE⟩ (.record_ctor ⟨Γ, _, hΓ, rfl, hf, EC⟩) ?_⟩
  · rintro j key ⟨rfl, rfl⟩; exact HX
  · rintro j key ⟨rfl, rfl⟩
    have E := erasedTypeOracle_valid hΓ hl
    rw [← proofEraseCtx_oracle] at E
    have hQ : env.HasType univs Γ (.forallE (.const s []) (.const s [])) (.sort (.imax (.succ .zero) (.succ .zero))) :=
      .forallE (hS.weak0 henv.ordered) (hS.weak0 henv.ordered)
    exact .function_type ⟨Γ, _, hΓ, rfl, hQ, E.symm⟩
  · intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact .var HX (by simp [Key.Valid]) ⟨rfl, rfl⟩

/-- Actual lookup realizes the free demand, and one closed native family
exposure fixes the target for every observed native-family result. -/
theorem Obs.canonical_world
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const t [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (H : Obs U RT uc c t (proofEraseCtx Γ) (FunctionSets U i) out key) :
    WorldComputes U RT (ErasedStaticStructureEtaExpansionUnion D) (canonical s uc c t A)
      (proofEraseCtx Γ) out key := by
  letI := U
  obtain ⟨_, HA⟩ := RigidFunctionObservation.closed_selected_header heq hs hF RF
  obtain ⟨_, _, RN⟩ := RigidFunctionObservation.function_lookup (c := uc) (r := t) (v := VLevel.succ .zero)
    (Step := ErasedStaticStructureEtaExpansionUnion D) rfl hS hΓ hl
  have HR := H.world_computes (RigidFunctionObservation.union_world_rename heq hs)
    (fun key τ => canonical_subst HA key) (target := canonical s uc c t A) rfl
    (fun HT => constructor_world hi hS hTag hF HT) (fun HT => family_world hi hS hTag hF heq hs RF HT)
    ContextRenaming.identity.interpretation (σ := Subst.id) (by
      rintro j key ⟨rfl, rfl⟩
      exact native_function_world hi hS hTag hF heq hs RN)
  simpa only [ProofShape.subst_id] using HR

include hi hS hTag hF

/-- Every arbitrary whole-constructor continuation returns to its canonical
constant-function instance. No root-only head development is assumed. -/
theorem canonical_term_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const t [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (.bvar i)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const c []) (.lam (.const s []) (.const uc []))) := by
  obtain ⟨HS, HV, H⟩ := initial_observation hi hS hTag hF hΓ hl
  have HE := H.full_compute hi hS hTag hF heq hs huc hc hf HS HV RE
  simpa only [WorldComputes, canonical] using HE.canonical_world hi hS hTag hF heq hs RF hΓ hl

/-- Any native selection after arbitrary whole-term computation, and every
later type continuation, returns to the family at one selected function domain.
All beta/structure/eta interleavings and changed annotations are included. -/
theorem canonical_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const t [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (.bvar i)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const t []) (.lam A (.const uc []))) := by
  obtain ⟨HS, HV, H⟩ := initial_observation hi hS hTag hF hΓ hl
  have HE := H.full_compute hi hS hTag hF heq hs huc hc hf HS HV RE
  have HN := HE.full_native hi hS hTag hF heq hs huc hc hf HS HV RN
  have HA := HN.full_compute hi hS hTag hF heq hs huc hc hf HS HV RA
  simpa only [WorldComputes, canonical] using HA.canonical_world hi hS hTag hF heq hs RF hΓ hl

/-- Future native types of an arbitrarily computed constructor join an
independently evolved assigned family at any other unit-function lookup. -/
theorem native_assigned_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) [] (.const t [])
      (.forallE (.forallE A B) C))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hli : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (hlj : Lookup Γ j (.forallE (.const s []) (.const s [])))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (.bvar i)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const t []) (.bvar j)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.const t []) (.lam A (.const uc []))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.const t []) (.lam A (.const uc []))) :=
  ⟨canonical_native_return hi hS hTag hF heq hs huc hc hf RF hΓ hli RE RN RA,
    RigidFunctionObservation.family_return_selected heq hs hi rfl rfl rfl huc hS
      (henv.projectionRigid hTag) hf hF RF hΓ hlj RB⟩

/-- Concrete declaration data removes the native-exposure and unfolding
premises. The selected family domain may be merely convertible to Unit; all
term and type histories use the full actual-environment computation union. -/
theorem environment_stored_native_return
    (heq : env.HasCanonicalEq)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hStored : ci.type.instL [] = .forallE (.forallE A0 B0) C0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ i (.forallE (.const s []) (.const s [])))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (.app (.const c []) (.bvar i)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      out (.app (.const t []) (.lam (proofErase [] A0) (.const uc []))) :=
  canonical_native_return hi hS hTag hF heq EnvironmentCore.sound
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hTag))
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag))
    (RigidFunctionObservation.nested_stored_family_native hcf hU hStored) hΓ hl RE RN RA

end Lean4Lean.VEnv.Strengthening.FunctionRecordDemand
