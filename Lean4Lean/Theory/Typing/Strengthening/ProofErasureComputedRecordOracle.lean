import Lean4Lean.Theory.Typing.Strengthening.ProofErasureObservedOracle
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHeterogeneousControlWorlds

/-! # Computed family annotations as actual native oracles

The actual lookup annotation need not visibly be a family or a Pi. A forward
computation from a typed family-ending annotation supplies independent evidence
for the exact oracle. Arbitrary ordinary equality is not substituted for that
computational provenance.
-/
namespace Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key Sets TypeEquality unitCarrier UnitArrows)
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))
local notation "U" => unitCarrier hi hS
local notation "RT" => recordCarrier hi hS Q hTag hF

/-- A typed literal family is an independently checked record annotation. -/
theorem family_annotation_seed (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (Q.control U).expr) :
    AnnotationSeed U RT (Q.control U) uc c t (proofEraseCtx Γ)
      (proofErase Γ (.app (.const t []) p)) .record :=
  ⟨⟨Γ, _, hΓ, rfl, IsDefEq.appDF (hF.weak0 henv.ordered) (Q.value_equal hi hS hp), rfl⟩,
    family_observation hi hS Q hTag hF hΓ hp⟩

/-- A dependent family-ending Pi supplies an annotation seed with no demanded
argument value. Its family parameter may depend on the displayed argument. -/
theorem family_function_annotation_seed (domain : HeterogeneousControl.ControlType)
    (hΓ : OnCtx Γ (env.IsType univs)) (hW : domain.WF univs)
    (hp : env.HasType univs (domain.expr :: Γ) p (Q.control U).expr) :
    AnnotationSeed U RT (Q.control U) uc c t (proofEraseCtx Γ)
      (proofErase Γ (.forallE domain.expr (.app (.const t []) p))) (.fn domain [] .record) := by
  have hA : env.HasType univs Γ domain.expr (.sort domain.level) := HeterogeneousControl.ControlType.typed hW
  have hΓA : OnCtx (domain.expr :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hFamily := hF.weak0 (Γ := domain.expr :: Γ) henv.ordered
  have hB := hFamily.app hp
  have HE := IsDefEq.forallEDF hA (IsDefEq.appDF hFamily (Q.value_equal hi hS hp))
  have hPi := HasType.forallE hA hB
  have EP : proofErase Γ (.forallE domain.expr (.app (.const t []) p)) =
      .forallE (proofErase Γ domain.expr) (proofErase (domain.expr :: Γ) (.app (.const t []) p)) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  refine ⟨⟨Γ, _, hΓ, rfl, HE, rfl⟩, ?_⟩
  rw [EP]
  exact .pi ⟨Γ, _, hΓ, rfl, hPi, EP⟩ ⟨Γ, _, hΓ, rfl, hA, rfl⟩ (by simp) (by simp)
    (family_observation hi hS Q hTag hF hΓA hp)

include hi hS Q hTag hF

/-- A full forward history from a family to the actual lookup annotation
initializes an unknown record. Both valuations follow from the history; there
is no assumed observation, native coverage, or ordinary conversion premise. -/
theorem computed_record_input_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A)
    (hp : env.HasType univs Γ p (Q.control U).expr)
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const t []) p)) (proofErase Γ A)) :
    (ObservedInput i .record).Typed U RT (proofEraseCtx Γ) ∧
      Valuation U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) ∧
      Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput i .record) (.bvar i) .record :=
  ((family_annotation_seed hi hS Q hTag hF hΓ hp).full_compute hi hS Q hTag hF
    heq hs huc hc hf RP).lookup hΓ hl

/-- The unknown function's actual annotation may be any full computational
descendant of a typed family-ending Pi. The caller argument is ordinarily typed
only, even when the actual lookup annotation no longer has a visible Pi head. -/
theorem computed_record_function_input_observation (domain : HeterogeneousControl.ControlType)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (huc : ∀ ls rhs, ¬ D.unfolds uc ls rhs)
    (hc : ∀ ls rhs, ¬ D.unfolds c ls rhs) (hf : ∀ ls rhs, ¬ D.unfolds t ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ f A)
    (hx : env.HasType univs Γ x domain.expr)
    (hp : env.HasType univs (domain.expr :: Γ) p (Q.control U).expr)
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE domain.expr (.app (.const t []) p))) (proofErase Γ A)) :
    (ObservedInput f (.fn domain [] .record)).Typed U RT (proofEraseCtx Γ) ∧
      Valuation U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput f (.fn domain [] .record)) ∧
      Obs U RT (Q.control U) uc c t (proofEraseCtx Γ) (ObservedInput f (.fn domain [] .record))
        (.app (.bvar f) (proofErase Γ x)) .record := by
  have HX := HeterogeneousControl.ControlTyping.of_typed hΓ hx
  have HA := (family_function_annotation_seed hi hS Q hTag hF domain hΓ HX.wf hp).full_compute
    hi hS Q hTag hF heq hs huc hc hf RP
  obtain ⟨HS, HV, H⟩ := HA.lookup hΓ hl
  exact ⟨HS, HV, .app (HeterogeneousControl.ControlTyping.apply H.typing HX) H (by simp)⟩

/-- Computed record annotations support the full native/assigned join after
arbitrary raw substitution. Actual stored target data discharges the canonical
telescope, and the source provenance discharges the native oracle evidence. -/
theorem computed_record_environment_native_assigned_join
    (heq : env.HasCanonicalEq)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i A)
    (hp : env.HasType univs Γ p (Q.control U).expr)
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (.app (.const t []) p)) (proofErase Γ A))
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
  obtain ⟨HS, HV, H⟩ := computed_record_input_observation hi hS Q hTag hF heq EnvironmentCore.sound
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hTag))
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag)) hΓ hl hp RP
  exact program_environment_native_assigned_join hi hS Q hTag hF heq hcf hU hT H HS HV
    (by rintro j key ⟨rfl, rfl⟩; trivial) hΓ' hAssigned RE RN RA RB

/-- Even a computed, nonliteral function oracle supports the full
native/assigned join. The source function and its supplied argument need no
terminating value history; only the annotation's forward provenance is required. -/
theorem computed_record_function_environment_native_assigned_join (domain : HeterogeneousControl.ControlType)
    (heq : env.HasCanonicalEq)
    (hcf : env.constants t = some ci) (hU : ci.uvars = 0)
    (hT : ci.type.instL [] = .forallE (Q.control U).expr B)
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ f A)
    (hx : env.HasType univs Γ x domain.expr)
    (hp : env.HasType univs (domain.expr :: Γ) p (Q.control U).expr)
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (proofErase Γ (.forallE domain.expr (.app (.const t []) p))) (proofErase Γ A))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (hAssigned : env.HasType univs Γ' (VExpr.mkApps (.const t []) args) (.sort u))
    (RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ)
      (.app (.bvar f) (proofErase Γ x)) image)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) image T)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ) T left)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
      (proofErase Γ' (VExpr.mkApps (.const t []) args)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        (left.subst σ) (.app (.const t []) (Q.canonical s uc)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) (proofEraseCtx Γ')
        right (.app (.const t []) (Q.canonical s uc)) := by
  obtain ⟨HS, HV, H⟩ := computed_record_function_input_observation hi hS Q hTag hF domain heq EnvironmentCore.sound
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hi))
    (EnvironmentCore.no_rigid (henv.projectionCtorRigid hTag))
    (EnvironmentCore.no_rigid (henv.projectionRigid hTag)) hΓ hl hx hp RP
  exact program_environment_native_assigned_join hi hS Q hTag hF heq hcf hU hT H HS HV
    (by rintro j key ⟨rfl, rfl⟩; trivial) hΓ' hAssigned RE RN RA RB

end Lean4Lean.VEnv.Strengthening.IgnoredRecordDemand
