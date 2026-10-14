import Lean4Lean.Theory.Typing.Strengthening.SeparatedPatternRoots

/-! # A computation presentation with disjoint declaration and pattern heads

Every typed path in the original ordinary-pattern computation relation has a
path in this presentation over the actual stored/selected-structure collection.
Overlapping roots have already been simulated by beta/delta/projection paths.
The new presentation retains exactly the other pattern roots; confluence for
those roots and coverage of actual singleton prefixes remain to be proved.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Ordinary pattern computation in which a root's head has no declaration
unfolding at its universe instance. Beta/delta/projection paths remain available. -/
inductive SeparatedPatternCompute (D : Definitions) : VExpr → VExpr → Prop where
  | base : ProjectionCompute D e out → SeparatedPatternCompute D e out
  | trans : SeparatedPatternCompute D a b → SeparatedPatternCompute D b c → SeparatedPatternCompute D a c
  | pattern {p : Pattern} {r : p.RHS × p.Check} {levels : List VLevel}
      {captures : p.Path → VExpr} :
      Pat p r → p.Matches e levels captures → CheckFromTyping env univs p r levels →
      (∀ rhs, ¬ D.unfolds p.headConst levels rhs) →
      SeparatedPatternCompute D e (r.1.apply levels captures)
  | app : SeparatedPatternCompute D f f' → SeparatedPatternCompute D a a' →
      SeparatedPatternCompute D (.app f a) (.app f' a')
  | lam : SeparatedPatternCompute D A A' → SeparatedPatternCompute D b b' →
      SeparatedPatternCompute D (.lam A b) (.lam A' b')
  | forallE : SeparatedPatternCompute D A A' → SeparatedPatternCompute D B B' →
      SeparatedPatternCompute D (.forallE A B) (.forallE A' B')
  | proj : SeparatedPatternCompute D m m' → SeparatedPatternCompute D (.proj s i m) (.proj s i m')

variable {D : Definitions}

/-- Forgetting the head-separation certificate recovers an ordinary path. -/
theorem SeparatedPatternCompute.toPattern (R : SeparatedPatternCompute D e out) :
    PatternCompute D e out := by
  induction R with
  | base R => exact .base R
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | pattern hp hm hc _ => exact .pattern hp hm hc
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- The separated presentation retains source-typed replay. -/
theorem SeparatedPatternCompute.simAt (R : SeparatedPatternCompute D e out)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out :=
  R.toPattern.simAt hs hΓ

/-- Head separation is unchanged by arbitrary raw substitution. -/
theorem SeparatedPatternCompute.subst (R : SeparatedPatternCompute D e out) :
    SeparatedPatternCompute D (e.subst σ) (out.subst σ) := by
  induction R generalizing σ with
  | base R => exact .base R.subst
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | pattern hp hm hc hn =>
    rw [Pattern.RHS.subst_apply]
    exact .pattern hp (Pattern.matches_subst hm) hc hn
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Removing every overlapping pattern root loses no typed finite ordinary
computation. Intermediate typings are replayed from the original source. -/
theorem PatternCompute.toSeparated
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) e out := by
  have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  induction R generalizing Γ with
  | base R => exact .base R
  | trans R1 _ ih1 ih2 =>
    obtain ⟨T, ht⟩ := ht
    exact (ih1 hΓ ⟨_, ht⟩).trans (ih2 hΓ ⟨_, (R1.simAt hs hΓ T ht).hasType.2⟩)
  | pattern hp hm hc =>
    obtain ⟨T, ht⟩ := ht
    rcases pattern_projection_or_separated hcon hΓ hp hm ht with H | H
    · exact .base H
    · exact .pattern hp hm hc H
  | app _ _ ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ ⟨_, hf⟩) (iha hΓ ⟨_, ha⟩)
  | @lam A A' b b' _ _ ihA ihb =>
    obtain ⟨hA, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA hΓ (hA.elim fun _ h => ⟨_, h⟩)) (ihb (Γ := A :: Γ) ⟨hΓ, hA⟩ hb)
  | @forallE A A' B B' _ _ ihA ihB =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨hA, hB⟩ := HasType.forallE_inv henv.ordered ht
    exact .forallE (ihA hΓ (hA.elim fun _ h => ⟨_, h⟩))
      (ihB (Γ := A :: Γ) ⟨hΓ, hA⟩ (hB.elim fun _ h => ⟨_, h⟩))
  | proj _ ihm =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := HasType.proj_inv henv hΓ ht
    exact .proj (ihm hΓ ⟨_, hm.hasType.2⟩)

/-- Raw confluence of the separated presentation suffices for typed confluence
of the original augmented ordinary-pattern computation. The premise is not
proved here; its remaining peaks involve the retained ordinary pattern roots. -/
theorem PatternCompute.confluent_of_separated
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hjoin : ∀ {a b c},
      SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a b →
      SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a c →
      ∃ out, SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) b out ∧
        SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) c out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ a)
    (R1 : PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a b)
    (R2 : PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a c) :
    ∃ out, PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) b out ∧
      PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) c out := by
  obtain ⟨out, HB, HC⟩ := hjoin (R1.toSeparated hcon hΓ ht) (R2.toSeparated hcon hΓ ht)
  exact ⟨out, HB.toPattern, HC.toPattern⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
