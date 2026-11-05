import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidUnitReturn

/-! # Full constructor and native-type return for a registered unit parameter

The whole constructor term may compute arbitrarily before native recovery.
Every selected native output, and every later type computation, returns to the
canonical unit-family instance. No term-provenance, header observation or
primitive-preservation premise remains in these concrete theorems.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [.const s []] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (.const s []) (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hTag hF

/-- Actual lookup and registered declaration typing initialize both valuations
and the saturated constructor observation. The caller supplies no observation. -/
theorem initial_observation (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.const s [])) :
    (UnitSets i).Typed U RT (proofEraseCtx Γ) ∧ Valuation U RT uc c t (proofEraseCtx Γ) (UnitSets i) ∧
      Obs U RT uc c t (proofEraseCtx Γ) (UnitSets i) (.app (.const c []) (.bvar i)) .record := by
  have hx : env.HasType univs Γ (.bvar i) (HeterogeneousControl.ControlType.atom U).expr := .bvar hl
  have EX : proofErase Γ (.bvar i) = .bvar i := if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hx)
  have HX : HeterogeneousControl.ControlTyping (proofEraseCtx Γ) (.bvar i) (.atom U) := ⟨Γ, _, hΓ, rfl, hx, EX⟩
  have hf : env.HasType univs Γ (.const c []) (HeterogeneousControl.ControlType.arrow (.atom U) (.atom RT)).expr :=
    (registered_unit_constructor_simple_arrow hi hS hTag hF).weak0 henv.ordered
  have he : env.HasType univs Γ (.app (.const c []) (.bvar i)) (HeterogeneousControl.ControlType.atom RT).expr := .app hf hx
  have EC : proofErase Γ (.const c []) = .const c [] := if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hf)
  have EE : proofErase Γ (.app (.const c []) (.bvar i)) = .app (.const c []) (.bvar i) := by
    rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg (HeterogeneousControl.ControlType.not_isProof hΓ he), EC, EX]
  refine ⟨?_, ?_, .app ⟨Γ, _, hΓ, rfl, he, EE⟩ (.record_ctor ⟨Γ, _, hΓ, rfl, hf, EC⟩) ?_⟩
  · rintro j key ⟨rfl, rfl⟩; exact HX
  · rintro j key ⟨rfl, rfl⟩
    have E := erasedTypeOracle_valid hΓ hl
    rw [← proofEraseCtx_oracle] at E
    exact .unit_type ⟨Γ, .const s [], hΓ, rfl, hS.weak0 henv.ordered, E.symm⟩
  · intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact .var HX (by simp only [Key.Valid]) ⟨rfl, rfl⟩

include hi hS hTag hF

/-- Every full-union continuation of the saturated constructor returns to its
canonical unit instance. All term-level structure and beta interleavings are
included, along with changed annotations and computed function prefixes. -/
theorem canonical_term_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.const s []))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (.bvar i)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const c []) (.const uc [])) := by
  obtain ⟨HS, HV, H⟩ := initial_observation hi hS hTag hF hΓ hl
  rcases (H.full_compute hi hS hTag hF heq hs huc hc hf HS HV R).record_readout with HB | HB
  · exact (ScopedCompute.beta HB).trans (.app .refl (static_structure_unit_lookup_compute hi rfl rfl rfl hS hΓ hl))
  · exact .beta HB

/-- Every native output after arbitrary whole-term computation, followed by
arbitrary further type computation, returns to the canonical family type.
There is no computed family-header, exact-argument-recovery or history premise. -/
theorem canonical_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.const s []))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (.bvar i)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image A)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) A out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const t []) (.const uc [])) := by
  obtain ⟨HS, HV, H⟩ := initial_observation hi hS hTag hF hΓ hl
  have HE := H.full_compute hi hS hTag hF heq hs huc hc hf HS HV RE
  have HN := HE.full_native hi hS hTag hF heq hs huc hc hf HS HV RN
  rcases (HN.full_compute hi hS hTag hF heq hs huc hc hf HS HV RA).family_readout with HB | HB
  · exact (ScopedCompute.beta HB).trans (.app .refl (static_structure_unit_lookup_compute hi rfl rfl rfl hS hΓ hl))
  · exact .beta HB

/-- Future native types of the constructor and an independently assigned family
at another unit variable join explicitly. Both whole-term and type histories
are unrestricted; the assigned type need never be recovered exactly. -/
theorem native_assigned_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hli : Lookup Γ i (.const s [])) (hlj : Lookup Γ j (.const s []))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (.bvar i)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image A)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) A left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const t []) (.bvar j))) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        left (.app (.const t []) (.const uc [])) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        right (.app (.const t []) (.const uc [])) :=
  ⟨canonical_native_return hi hS hTag hF heq hs huc hc hf hΓ hli RE RN RA,
    static_structure_rigid_unit_family_return heq hs hi rfl rfl rfl huc hS
      (henv.projectionRigid hTag) hf hΓ (hF.weak0 henv.ordered) hlj RB⟩

/-- The actual environment definitions discharge all three unfolding exclusions.
Only registered metadata, ordinary typings, and the actual histories remain. -/
theorem environment_canonical_native_return
    (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i (.const s []))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (.app (.const c []) (.bvar i)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image A)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) A out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      out (.app (.const t []) (.const uc [])) :=
  canonical_native_return hi hS hTag hF heq EnvironmentCore.sound
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hTag))
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag)) hΓ hl RE RN RA

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
