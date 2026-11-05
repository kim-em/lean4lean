import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandProgramReturn

/-! # Arbitrary typed inputs to a unit-valued free function

The selected free function needs no observation of its argument: its literal
lookup header already returns the registered unit. The argument may therefore
be any ordinary typed term at the closed control domain, including terms not
admitted by the finite-demand grammar. Whole-term and native-type continuations
remain unrestricted. This does not establish arbitrary family-type coverage.
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

/-- The free function's result is demanded, but its argument is not. -/
def IgnoredInput (f : Nat) (domain : HeterogeneousControl.ControlType) : Sets :=
  fun i key => i = f ∧ key = .fn domain [] .unit

/-- Literal lookup at a unit-valued arrow supplies all observer and semantic
valuations while leaving the argument completely undemanded. -/
theorem ignored_input_initial (domain : HeterogeneousControl.ControlType)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ f (.forallE domain.expr (.const s [])))
    (hx : env.HasType univs Γ x domain.expr) :
    (IgnoredInput f domain).Typed U RT (proofEraseCtx Γ) ∧
      Valuation U RT uc c t (proofEraseCtx Γ) (IgnoredInput f domain) ∧
      (∀ i key, IgnoredInput f domain i key →
        Computes (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) uc c t (.bvar i) key) ∧
      Obs U RT uc c t (proofEraseCtx Γ) (IgnoredInput f domain)
        (.app (.const c []) (.app (.bvar f) (proofErase Γ x))) .record := by
  have hW : domain.WF univs := (HeterogeneousControl.ControlTyping.of_typed hΓ hx).wf
  have hA : env.HasType univs Γ domain.expr (.sort domain.level) :=
    HeterogeneousControl.ControlType.typed hW
  have hΓA : OnCtx (domain.expr :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hSΓ : env.HasType univs Γ (.const s []) (.sort (.succ .zero)) := hS.weak0 henv.ordered
  have hSA : env.HasType univs (domain.expr :: Γ) (.const s []) (.sort (.succ .zero)) := hS.weak0 henv.ordered
  have ES : proofErase (domain.expr :: Γ) (.const s []) = .const s [] :=
    if_neg (not_isProof_of_sort hΓA hSA)
  have hpi := HasType.forallE hA hSA
  have EP : proofErase Γ (.forallE domain.expr (.const s [])) =
      .forallE (proofErase Γ domain.expr) (.const s []) := by
    rw [show proofErase Γ (.forallE _ _) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hpi), ES]
  have HE : TypeEquality (proofEraseCtx Γ) (proofErase Γ domain.expr) domain := ⟨Γ, _, hΓ, rfl, hA, rfl⟩
  have EΓA : proofEraseCtx (domain.expr :: Γ) = proofErase Γ domain.expr :: proofEraseCtx Γ := rfl
  have HO : Obs U RT uc c t (proofEraseCtx Γ) (IgnoredInput f domain)
      (.forallE (proofErase Γ domain.expr) (.const s [])) (.type (.fn domain [] .unit)) := by
    refine .pi ⟨Γ, _, hΓ, rfl, hpi, EP⟩ HE ?_ ?_ ?_
    · intro key hk; cases hk
    · intro key hk; cases hk
    · exact .unit_type ⟨domain.expr :: Γ, _, hΓA, EΓA, hSA, ES⟩
  have hf : env.HasType univs Γ (.bvar f) (HeterogeneousControl.ControlType.arrow domain (.atom U)).expr := .bvar hl
  have EF : proofErase Γ (.bvar f) = .bvar f := if_neg (HeterogeneousControl.ControlType.not_isProof hΓ hf)
  have HF : HeterogeneousControl.ControlTyping (proofEraseCtx Γ) (.bvar f) (.arrow domain (.atom U)) :=
    ⟨Γ, _, hΓ, rfl, hf, EF⟩
  have E := erasedTypeOracle_valid hΓ hl
  rw [← proofEraseCtx_oracle, EP] at E
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar f) (.forallE (proofErase Γ domain.expr) (.const s [])) := E ▸ ScopedTypeRecovery.bvar
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro i key ⟨rfl, rfl⟩; exact HF
  · rintro i key ⟨rfl, rfl⟩; exact E ▸ HO
  · rintro i key ⟨rfl, rfl⟩
    simp only [Computes]
    intro a _
    have RA : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.app (.bvar i) a) (.const s []) := .app RN
    have RU : NativeUnitExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.app (.bvar i) a) (.const uc []) := .intro (ps := []) hi rfl rfl rfl RA
    exact .base (erased_static_structure_eta_expansion_union_structure RU.maskedStructure)
  · apply Obs.construct hi hS hTag hF
    have he : env.HasType univs Γ (.app (.bvar f) x) (HeterogeneousControl.ControlType.atom U).expr := .app hf hx
    have EE : proofErase Γ (.app (.bvar f) x) = .app (.bvar f) (proofErase Γ x) := by
      rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg (HeterogeneousControl.ControlType.not_isProof hΓ he), EF]
    refine .app ⟨Γ, _, hΓ, rfl, he, EE⟩ (domain := domain) (keys := []) ?_ ?_
    · exact .var HF (by simp [Key.Valid]) ⟨rfl, rfl⟩
    · intro key hk; cases hk

include hi hS hTag hF in
/-- An arbitrary typed input can occur in a complete constructor/native
history. No observation, native certificate, terminating history or equality
completeness premise is required of that input. Its assigned domain is any
closed control type; the free function's literal lookup returns the unit. -/
theorem ignored_input_native_return (domain : HeterogeneousControl.ControlType)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ f (.forallE domain.expr (.const s [])))
    (hx : env.HasType univs Γ x domain.expr)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.const c []) (.app (.bvar f) (proofErase Γ x))) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) image B)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) B out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const t []) (.const uc [])) := by
  obtain ⟨HS, HV, HC, H⟩ := ignored_input_initial hi hS hTag hF (D := D) domain hΓ hl hx
  have HE := H.full_compute hi hS hTag hF heq hs huc hc hf HS HV RE
  have HN := HE.full_native hi hS hTag hF heq hs huc hc hf HS HV RN
  have HR := (HN.full_compute hi hS hTag hF heq hs huc hc hf HS HV RB).computes (σ := Subst.id) HC
  simpa only [ProofShape.subst_id, Computes] using HR

include hi hS hTag hF in
/-- Actual environment definitions discharge every rigid unfolding exclusion
for the arbitrary-input constructor/native return. -/
theorem environment_ignored_input_native_return (domain : HeterogeneousControl.ControlType)
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (hl : Lookup Γ f (.forallE domain.expr (.const s [])))
    (hx : env.HasType univs Γ x domain.expr)
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (.app (.const c []) (.app (.bvar f) (proofErase Γ x))) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image B)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) B out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      out (.app (.const t []) (.const uc [])) :=
  ignored_input_native_return hi hS hTag hF domain heq EnvironmentCore.sound
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hTag))
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag)) hΓ hl hx RE RN RB

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
