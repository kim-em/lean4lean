import Lean4Lean.Theory.Typing.Strengthening.ProofErasureApplicationStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedResynthesisUnion

/-! # The least relation closed under the application-stage guards

The union of the finite stages is closed under guards using that very union.
Conversely, every relation containing core steps and closed under the three
guarded prefix constructors contains the union. No infinitary certificate,
substitution closure, or comparison completeness is introduced.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- All finite application stages, allowing independent bounds per primitive. -/
def ErasedApplicationUnion (D : PureObservation.Definitions) :=
  ScopedStageUnion (ErasedApplicationStage D)

/-- Typed general singleton guards over a monotone union have a finite bound.
The existential source realization is independent of this bound. -/
theorem ProofShape.ScopedTypedSingletonPrimitive.finite_stage
    (hmono : ScopedStagesMonotone Stages)
    (H : ScopedTypedSingletonPrimitive (ScopedStageUnion Stages) Δ a b) :
    ∃ stage, ScopedTypedSingletonPrimitive (Stages stage) Δ a b := by
  obtain ⟨HT, H⟩ := H
  cases H with
  | intro V ha hcalc HG =>
    obtain ⟨stage, HG⟩ := ScopedCompare.finite_stage hmono HG
    exact ⟨stage, HT, .intro V ha hcalc HG⟩

/-- The union is a fixed point of the guarded-prefix rules. In particular,
guards over the union require no stage beyond all finite stages. -/
theorem erased_application_union_iff :
    ErasedApplicationUnion D Δ a b ↔
      ErasedIotaPrimitive D a b ∨
      ScopedTypedSingletonPrimitive (ErasedApplicationUnion D) Δ a b ∨
      ScopedStructurePrefixPrimitive (ErasedApplicationUnion D) Δ a b ∨
      ApplicationPrefixPrimitive (ErasedApplicationUnion D) Δ a b := by
  constructor
  · rintro ⟨stage, H⟩
    induction stage with
    | zero => exact .inl H
    | succ stage ih =>
      rcases H with H | H | H | H
      · exact ih H
      · exact .inr (.inl (H.mono (fun H => ⟨stage, H⟩)))
      · exact .inr (.inr (.inl (H.mono (fun H => ⟨stage, H⟩))))
      · exact .inr (.inr (.inr (H.mono (fun H => ⟨stage, H⟩))))
  · intro H
    rcases H with H | H | H | H
    · exact ⟨0, H⟩
    · obtain ⟨stage, H⟩ := H.finite_stage erased_application_stage_mono
      exact ⟨stage + 1, .inr (.inl H)⟩
    · cases H with
      | intro HC =>
        obtain ⟨stage, HC⟩ := HC.finite_stage erased_application_stage_mono
        exact ⟨stage + 1, .inr (.inr (.inl (.intro HC)))⟩
    · cases H with
      | intro HC =>
        obtain ⟨stage, HC⟩ := HC.finite_stage erased_application_stage_mono
        exact ⟨stage + 1, .inr (.inr (.inr (.intro HC)))⟩

/-- Any relation containing core computation and closed under the guarded
rules contains every finite stage. The fixed point above is therefore least. -/
theorem erased_application_union_least
    (hcore : ∀ {Δ a b}, ErasedIotaPrimitive D a b → Step Δ a b)
    (hsingle : ∀ {Δ a b}, ScopedTypedSingletonPrimitive Step Δ a b → Step Δ a b)
    (hstructure : ∀ {Δ a b}, ScopedStructurePrefixPrimitive Step Δ a b → Step Δ a b)
    (happlication : ∀ {Δ a b}, ApplicationPrefixPrimitive Step Δ a b → Step Δ a b)
    (H : ErasedApplicationUnion D Δ a b) : Step Δ a b := by
  obtain ⟨stage, H⟩ := H
  induction stage generalizing Δ a b with
  | zero => exact hcore H
  | succ stage ih =>
    rcases H with H | H | H | H
    · exact ih H
    · exact hsingle (H.mono ih)
    · exact hstructure (H.mono ih)
    · exact happlication (H.mono ih)

/-- The closed union retains arbitrary-block source-typed descent. -/
theorem erased_application_union_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ErasedApplicationUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨stage, H⟩ := H
  exact erased_application_stage_descent heq hs stage hΓ hΓ' W ht H

/-- Union computation still acts only at constant/projection-headed primitives.
Closing the stage hierarchy does not repair the old carrier grammar. -/
theorem erased_application_union_head (H : ErasedApplicationUnion D Δ a b) : PrimitiveHead a := by
  obtain ⟨stage, H⟩ := H
  exact erased_application_stage_head stage H

/-- Each union primitive replays as an original registered prefix computation. -/
theorem erased_application_union_replay (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ErasedScopedPrefixReplay D (ErasedApplicationUnion D) := by
  intro Γ e T out hΓ ht H
  obtain ⟨stage, H⟩ := H
  exact erased_application_stage_replay heq hs hregistry stage hΓ ht H

/-- For this concrete family, proving joint re-synthesis at the closed union
is exactly the finite-stage task. This removes bound management, not the open
semantic requirement to choose a compatible recovered domain and guard. -/
theorem application_finite_resynthesis_iff_union :
    ScopedFiniteCarrierDomainResynthesis (ErasedApplicationStage D) (ErasedApplicationStage D) ↔
      ScopedCarrierDomainResynthesis (ErasedApplicationUnion D) (ErasedApplicationUnion D) :=
  scoped_finite_resynthesis_iff_union erased_application_stage_mono erased_application_stage_mono

end Lean4Lean.VEnv.Strengthening
