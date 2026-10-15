import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointQuotRepair
import Lean4Lean.Theory.Typing.Strengthening.SeparatedConfluence

/-! # Confluence after restoring proposition-source quotient unfolding

The new closed equation and ordinary quotient iota have incompatible universe
checks. This preserves separation and typed-source confluence of the ordinary
core. No confluence or re-synthesis claim for singleton joint stages is made.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]
namespace ErasedQuotCore
open private core_no_quot from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointQuotBoundary

private theorem split_definition (hq : QuotRegistered env)
    (H : (definitions hq).unfolds c ls rhs) :
    ErasedCore.definitions.unfolds c ls rhs ∨
      (c = ``Quot.lift ∧ ∃ u v, ls = [u,v] ∧ u.WF univs ∧ v.WF univs ∧
        u ≈ .zero ∧ rhs = ClosedQuot.value u v) := by
  rcases H with (H | H) | H
  · exact .inl (.inl H)
  · exact .inr H
  · exact .inl (.inr H)

/-- The quotient-enriched declaration collection remains deterministic at fixed
universe syntax. Its added head has no previous declaration. -/
theorem deterministic (hq : QuotRegistered env) : (definitions hq).Deterministic := by
  intro c ls a b HA HB
  rcases split_definition hq HA with HA | ⟨rfl, u, v, rfl, _, _, _, rfl⟩
  · rcases split_definition hq HB with HB | ⟨rfl, _⟩
    · exact RegisteredStructure.definitions_ofEnv_unique HA HB
    · exact (core_no_quot hq HA).elim
  · rcases split_definition hq HB with HB | ⟨_, u', v', E, _, _, _, rfl⟩
    · exact (core_no_quot hq HB).elim
    · cases E
      rfl

/-- Every rigid head stays disjoint from all quotient-enriched declarations. -/
theorem no_rigid (hq : QuotRegistered env) (hrig : env.Rigid c) :
    ∀ ls rhs, ¬ (definitions hq).unfolds c ls rhs := by
  intro ls rhs H
  rcases split_definition hq H with H | ⟨rfl, _⟩
  · exact RegisteredStructure.definitions_ofEnv_no_rigid hrig H
  · exact hrig.defeqs quotDefEq hq.equation [.param 0, .param 1] rfl

private theorem pattern_no_closed_quot (hq : QuotRegistered env)
    (hp : Pat p r) (hm : p.Matches source [u,v] captures)
    (hc : CheckFromTyping env univs p r [u,v])
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ source T)
    (hh : p.headConst = ``Quot.lift) (hz : u ≈ .zero) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  cases sp with
  | defn c =>
    change c = ``Quot.lift at hh
    subst c
    exact (pat_const_not_unfolding hp).2 hq rfl
  | iota c major ctor fields =>
    rw [SimplePattern.iota_headConst] at hh
    subst c
    rcases pat_recursor hp with ⟨data, _, _, _, hl, _⟩ | ⟨_, _, _, _, _, rest, hr⟩
    · rw [recursorData_quot hq] at hl
      cases hl
    · have H := hc hΓ hm ht
      rw [hr] at H
      exact H.1 hz

/-- Every typed path in the enlarged ordinary core has a separated path. The
added zero-source equation cannot overlap an enabled ordinary quotient rule. -/
theorem toSeparated (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : PatternCompute (definitions hq) e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    SeparatedPatternCompute (definitions hq) e out := by
  have hs := sound hq
  induction R generalizing Γ with
  | base R => exact .base R
  | trans R1 _ ih1 ih2 =>
    obtain ⟨T, ht⟩ := ht
    exact (ih1 hΓ ⟨_, ht⟩).trans (ih2 hΓ ⟨_, (R1.simAt hs hΓ T ht).hasType.2⟩)
  | pattern hp hm hc =>
    obtain ⟨T, ht⟩ := ht
    rcases pattern_projection_or_separated hcon hΓ hp hm ht with H | H
    · exact .base (H.of_inclusion (fun _ _ _ H => includes_core hq H))
    · refine .pattern hp hm hc ?_
      intro rhs HD
      rcases split_definition hq HD with HD | ⟨hh, u, v, rfl, _, _, hz, _⟩
      · exact H rhs HD
      · exact pattern_no_closed_quot hq hp hm hc hΓ ht hh hz
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

/-- Original ordinary computation remains confluent after adding the closed
proposition-source quotient equation. Typing is required only at the source. -/
theorem pattern_confluent (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ e)
    (RA : PatternCompute (definitions hq) e a)
    (RB : PatternCompute (definitions hq) e b) :
    ∃ out, PatternCompute (definitions hq) a out ∧ PatternCompute (definitions hq) b out := by
  obtain ⟨out, HA, HB⟩ := (toSeparated hq hcon RA hΓ ht).confluent
    (deterministic hq) (no_rigid hq) (toSeparated hq hcon RB hΓ ht)
  exact ⟨out, HA.toPattern, HB.toPattern⟩

/-- The repaired ordinary erased core. -/
abbrev Step (hq : QuotRegistered env) := ErasedIotaPrimitive (definitions hq)

/-- A finite repaired erased path replays to an original typed path with exactly
its erased endpoint; no recovery or strengthening hypothesis is required. -/
theorem replay (hq : QuotRegistered env)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.Compute (Step hq) (proofErase Γ e) out) :
    ∃ e', PatternCompute (definitions hq) e e' ∧ env.HasType univs Γ e' T ∧
      proofErase Γ e' = out := by
  obtain ⟨e', H, E⟩ := proofErase_compute_replay (sound hq)
    (erased_iota_replay (sound hq)) hΓ ht R
  exact ⟨e', H, (H.simAt (sound hq) hΓ _ ht).hasType.2, E⟩

/-- Exact typed-source confluence of the quotient-enriched erased ordinary core.
This does not assert confluence of the additional singleton joint-stage rules. -/
theorem confluent (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (RA : ProofShape.Compute (Step hq) (proofErase Γ e) a)
    (RB : ProofShape.Compute (Step hq) (proofErase Γ e) b) :
    ∃ out, ProofShape.Compute (Step hq) a out ∧ ProofShape.Compute (Step hq) b out := by
  obtain ⟨a₀, HA, ha, rfl⟩ := replay hq hΓ ht RA
  obtain ⟨b₀, HB, hb, rfl⟩ := replay hq hΓ ht RB
  obtain ⟨out, RA, RB⟩ := pattern_confluent hq hcon hΓ ⟨_, ht⟩ HA HB
  exact ⟨proofErase Γ out, proofErase_pattern_compute_forward (sound hq) hcon hΓ ha RA,
    proofErase_pattern_compute_forward (sound hq) hcon hΓ hb RB⟩

end ErasedQuotCore
end Lean4Lean.VEnv.Strengthening
