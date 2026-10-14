import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreForward
import Lean4Lean.Theory.Typing.Strengthening.SeparatedConfluence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawChecking

/-! # Exact confluence of ordinary computation from typed erasures

Replay and forward erasure transfer the checked original ordinary-computation
confluence theorem. The source must have a typed original; intermediate raw
shapes need no independently supplied typing or representatives.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]

namespace ErasedCore
/-- All stored definitions and the selected closed structure programs. -/
noncomputable def definitions : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

/-- Ordinary erased beta/delta/projection and concrete pattern computation. -/
abbrev Step := ErasedIotaPrimitive definitions

private theorem sound : definitions.Sound env univs :=
  RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)

/-- Every finite ordinary erased path has an exactly matching original path. -/
theorem replay (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.Compute Step (proofErase Γ e) out) :
    ∃ e', PatternCompute definitions e e' ∧ env.HasType univs Γ e' T ∧
      proofErase Γ e' = out := by
  obtain ⟨e', H, E⟩ := proofErase_compute_replay sound (erased_iota_replay sound) hΓ ht R
  exact ⟨e', H, (H.simAt sound hΓ _ ht).hasType.2, E⟩

/-- Typed-source confluence of ordinary erased computation, including recursive
stored definitions and selected structure equations, with literal endpoints. -/
theorem confluent (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R1 : ProofShape.Compute Step (proofErase Γ e) a)
    (R2 : ProofShape.Compute Step (proofErase Γ e) b) :
    ∃ out, ProofShape.Compute Step a out ∧ ProofShape.Compute Step b out := by
  obtain ⟨a₀, HA, ha, rfl⟩ := replay hΓ ht R1
  obtain ⟨b₀, HB, hb, rfl⟩ := replay hΓ ht R2
  obtain ⟨out, RA, RB⟩ := PatternCompute.registeredStructure_confluent hcon hΓ ⟨_, ht⟩ HA HB
  exact ⟨proofErase Γ out, proofErase_pattern_compute_forward sound hcon hΓ ha RA,
    proofErase_pattern_compute_forward sound hcon hΓ hb RB⟩

/-- Finite reducts of a typed erasure remain valid sources for exact confluence.
Replay supplies their representatives automatically. -/
theorem confluent_after (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.Compute Step (proofErase Γ e) mid)
    (R1 : ProofShape.Compute Step mid a) (R2 : ProofShape.Compute Step mid b) :
    ∃ out, ProofShape.Compute Step a out ∧ ProofShape.Compute Step b out := by
  obtain ⟨mid₀, _, hm, rfl⟩ := replay hΓ ht R
  exact confluent hcon hΓ hm R1 R2

/-- A literal common-reduct guard survives arbitrary ordinary computation of
both typed endpoints. Common endpoint types are not needed for this diagram. -/
theorem join_forward (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
    (hb : env.HasType univs Γ b B)
    (HA : ProofShape.Compute Step (proofErase Γ a) shared)
    (HB : ProofShape.Compute Step (proofErase Γ b) shared)
    (RA : ProofShape.Compute Step (proofErase Γ a) a')
    (RB : ProofShape.Compute Step (proofErase Γ b) b') :
    ∃ out, ProofShape.Compute Step a' out ∧ ProofShape.Compute Step b' out := by
  obtain ⟨left, HL, HS⟩ := confluent hcon hΓ ha RA HA
  obtain ⟨right, HR, HT⟩ := confluent hcon hΓ hb RB HB
  obtain ⟨out, RL, RR⟩ := confluent_after hcon hΓ ha HA HS HT
  exact ⟨out, HL.trans RL, HR.trans RR⟩

/-- The transported literal join is an endpoint checking guard in either mode.
This proves transport for common-reduct guards, not for all raw comparisons. -/
theorem join_guard_forward (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
    (hb : env.HasType univs Γ b B)
    (HA : ProofShape.Compute Step (proofErase Γ a) shared)
    (HB : ProofShape.Compute Step (proofErase Γ b) shared)
    (RA : ProofShape.Compute Step (proofErase Γ a) a')
    (RB : ProofShape.Compute Step (proofErase Γ b) b') :
    ProofShape.RawCheckedCompare Step mode a' b' := by
  obtain ⟨out, HL, HR⟩ := join_forward hcon hΓ ha hb HA HB RA RB
  exact .compute HL HR (.base .refl)

end ErasedCore
end Lean4Lean.VEnv.Strengthening
