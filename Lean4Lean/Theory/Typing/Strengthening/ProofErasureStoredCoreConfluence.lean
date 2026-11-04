import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreConfluence
import Lean4Lean.Theory.Typing.Strengthening.SeparatedConfluence
import Lean4Lean.Theory.Typing.Strengthening.DeclarationLevelCompatibility
import Lean4Lean.Theory.Typing.Confluence.Params

/-! # Confluence for the actual stored-definition core

Stored definitions and retained iota patterns have disjoint heads. This gives
ordinary and universe-extended erased confluence for every well-formed actual
environment. No quotient registration or extra selected-structure declaration
collection is needed for these core results.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]
namespace StoredCore

/-- A typed stored-definition path has a separated presentation: definition
patterns unfold their stored body, while iota heads have no stored definition. -/
theorem toSeparated
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : PatternCompute (Definitions.ofEnv env univs henv) e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    SeparatedPatternCompute (Definitions.ofEnv env univs henv) e out := by
  have hs := Definitions.ofEnv_sound (U := univs) henv
  induction R generalizing Γ with
  | base R => exact .base R
  | trans R1 _ ih1 ih2 =>
    obtain ⟨T, ht⟩ := ht
    exact (ih1 hΓ ⟨_, ht⟩).trans (ih2 hΓ ⟨_, (R1.simAt hs hΓ T ht).hasType.2⟩)
  | pattern hp hm hc =>
    obtain ⟨T, ht⟩ := ht
    obtain ⟨sp, rfl⟩ := pat_simple hp
    cases sp with
    | defn c => exact .base (.base (definition_compute henv hΓ (hcon hp) hm ⟨_, ht⟩))
    | iota rc mr cc kc =>
      exact .pattern hp hm hc (fun _ H => iota_no_stored_definition hp
        (by simpa only [SimplePattern.iota_headConst] using H))
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

/-- Ordinary typed computation is confluent using only actual stored definitions
and the concrete pattern rules already present in the source relation. -/
theorem pattern_confluent
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ e)
    (RA : PatternCompute (Definitions.ofEnv env univs henv) e a)
    (RB : PatternCompute (Definitions.ofEnv env univs henv) e b) :
    ∃ out, PatternCompute (Definitions.ofEnv env univs henv) a out ∧
      PatternCompute (Definitions.ofEnv env univs henv) b out := by
  obtain ⟨out, HA, HB⟩ := (toSeparated hcon RA hΓ ht).confluent
    (fun H1 H2 => Definitions.ofEnv_unique henv H1 H2)
    (fun hr _ _ => Definitions.ofEnv_no_rigid henv hr) (toSeparated hcon RB hΓ ht)
  exact ⟨out, HA.toPattern, HB.toPattern⟩

/-- Typed-source confluence of the erased actual stored-definition core. -/
theorem typed_core_confluence
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    TypedCoreConfluence (ErasedIotaPrimitive (Definitions.ofEnv env univs henv)) := by
  intro Γ e T a b hΓ ht RA RB
  have hs := Definitions.ofEnv_sound (U := univs) henv
  obtain ⟨a₀, HA, rfl⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ ht RA
  obtain ⟨b₀, HB, rfl⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ ht RB
  obtain ⟨out, RA, RB⟩ := pattern_confluent hcon hΓ ⟨_, ht⟩ HA HB
  exact ⟨proofErase Γ out,
    proofErase_pattern_compute_forward hs hcon hΓ (HA.simAt hs hΓ _ ht).hasType.2 RA,
    proofErase_pattern_compute_forward hs hcon hΓ (HB.simAt hs hΓ _ ht).hasType.2 RB⟩

/-- Universe conversion preserves confluence of the actual stored core; its
universe compatibility follows from the registered definition bodies. -/
theorem typed_level_core_confluence
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    TypedCoreConfluence (ErasedLevelCore (Definitions.ofEnv env univs henv)) :=
  proofErase_level_core_confluent (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) hcon (typed_core_confluence hcon)

end StoredCore

omit [Params] in
/-- Actual well-formed environments discharge every compatibility hypothesis of
the universe-extended ordinary core confluence theorem. -/
theorem proofErase_environment_level_core_confluence {E : VEnv} (hE : E.WF) (U : Nat) :
    @TypedCoreConfluence (hE.params U)
      (@ErasedLevelCore (hE.params U) (Definitions.ofEnv E U hE)) := by
  letI := hE.params U
  exact @StoredCore.typed_level_core_confluence (hE.params U) (fun H => H)

end Lean4Lean.VEnv.Strengthening
