import Lean4Lean.Theory.Typing.Strengthening.QuotLevelCompatibility
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreExpansionConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreConfluence

/-! # A universe-compatible core for every actual environment

Use the existing optional quotient collection and add the registry-selected
structure programs. This retains the repaired quotient prefix whenever one is
present, without imposing quotient registration on the environment. Ordinary
and universe-core confluence hold for this same collection.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]
namespace EnvironmentCore

/-- Actual stored definitions, selected structure programs, and the closed
proposition-source quotient equation when its primitives are registered. -/
noncomputable def definitions : Definitions :=
  RegisteredStructure.definitions (FullHead.quotDefinitions env univs henv)

/-- In a quotient environment this is exactly the previously repaired core. -/
theorem definitions_of_quot (hq : QuotRegistered env) :
    definitions = ErasedQuotCore.definitions hq := by
  simp only [definitions, FullHead.quotDefinitions, dif_pos hq, ErasedQuotCore.definitions]

/-- In the absence of quotient registration only stored and selected structure
programs are included. No primitive equation is invented for a missing Quot. -/
theorem definitions_of_no_quot (hq : ¬ QuotRegistered env) :
    definitions = ErasedCore.definitions := by
  simp only [definitions, FullHead.quotDefinitions, dif_neg hq, ErasedCore.definitions]

/-- Every included closed equation is sound at its actual universe arguments. -/
theorem sound : definitions.Sound env univs :=
  RegisteredStructure.definitions_sound (FullHead.quot_sound henv)

/-- The optional quotient branch and selected structure programs both preserve
the syntactic universe-compatibility interface. -/
theorem levelCompatible (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    definitions.LevelCompatible univs := by
  have H : (FullHead.quotDefinitions env univs henv).LevelCompatible univs := by
    unfold FullHead.quotDefinitions
    split
    · exact ClosedQuot.definitions_levelCompatible henv _
    · exact Definitions.ofEnv_levelCompatible henv
  intro c ls ls' rhs HD hw he
  exact RegisteredStructure.definitions_levelCompatible H hcon HD hw he

/-- No registered rigid constructor or type head unfolds in the total core. -/
theorem no_rigid (hrig : env.Rigid c) : ∀ ls rhs, ¬ definitions.unfolds c ls rhs := by
  classical
  by_cases hq : QuotRegistered env
  · rw [definitions_of_quot hq]
    exact ErasedQuotCore.no_rigid hq hrig
  · rw [definitions_of_no_quot hq]
    exact fun _ _ => RegisteredStructure.definitions_ofEnv_no_rigid hrig

/-- Every former stored/structure equation remains available, independently of
whether quotient primitives are registered. -/
theorem includes_core (H : ErasedCore.definitions.unfolds c ls rhs) :
    definitions.unfolds c ls rhs := by
  rcases H with H | H
  · exact .inl (FullHead.quot_base henv _ _ _ H)
  · exact .inr H

/-- The same total collection has ordinary typed-source erased confluence. -/
theorem typed_core_confluence (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    TypedCoreConfluence (ErasedIotaPrimitive definitions) := by
  classical
  by_cases hq : QuotRegistered env
  · rw [definitions_of_quot hq]
    exact ErasedQuotCore.typed_core_confluence hq hcon
  · rw [definitions_of_no_quot hq]
    exact fun hΓ ht RA RB => ErasedCore.confluent hcon hΓ ht RA RB

/-- Explicit universe changes can interleave ordinary computation, including
the repaired quotient equation, without losing typed-source confluence. -/
theorem typed_level_core_confluence (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    TypedCoreConfluence (ErasedLevelCore definitions) :=
  proofErase_level_core_confluent sound (levelCompatible hcon) hcon (typed_core_confluence hcon)

/-- Every actual proposition-source quotient prefix computes in this core.
Registration follows from the actual prefix certificate rather than appearing
as a global hypothesis. The erased endpoint is exact. -/
theorem quotient_prefix_forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (mkApps (.const ``Quot.lift levels) args) T)
    (H : QuotPrefixUnfold env univs Γ levels args rhs) :
    ProofShape.Compute (ErasedIotaPrimitive definitions)
      (proofErase Γ (mkApps (.const ``Quot.lift levels) args)) (proofErase Γ rhs) := by
  rw [definitions_of_quot H.registered]
  exact (ErasedQuotCore.quotient_prefix_forward H.registered hcon hΓ ht H).core_forget

end EnvironmentCore

omit [Params] in
/-- Every well-formed actual environment has the enlarged universe-core
confluence theorem, without abstract declaration or pattern hypotheses. -/
theorem proofErase_environment_augmented_core_confluence {E : VEnv} (hE : E.WF) (U : Nat) :
    @TypedCoreConfluence (hE.params U)
      (@ErasedLevelCore (hE.params U) (@EnvironmentCore.definitions (hE.params U))) := by
  letI := hE.params U
  exact @EnvironmentCore.typed_level_core_confluence (hE.params U) (fun H => H)

end Lean4Lean.VEnv.Strengthening
