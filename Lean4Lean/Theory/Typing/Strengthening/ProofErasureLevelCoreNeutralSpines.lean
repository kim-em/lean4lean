import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure

/-! # Neutral application spines in the universe-extended core

Universe roots include sorts, so the ordinary primitive-head theorem alone
does not cover this core. Direct root exclusion still preserves variable heads
and exposes independent paths for all arguments, without normality assumptions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private variableHead variableHead_mkApps bvar_spine_app bvar_spine_not_primitive
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
variable [Params]

/-- No ordinary or explicit universe root consumes a variable-headed spine. -/
theorem erased_level_core_no_bvar_spine
    (H : ErasedLevelCore D (ProofShape.mkApps (.bvar i) args) out) : False := by
  rcases H with H | H
  · exact bvar_spine_not_primitive args (erased_iota_primitive_head H)
  · generalize E : ProofShape.mkApps (.bvar i) args = source at H
    cases H <;>
      have HH := congrArg variableHead E <;>
      simp only [variableHead_mkApps, variableHead] at HH <;> cases HH

/-- A full level-core path from a variable application spine retains its head
and arity and computes each argument independently. Arguments may contain
arbitrary beta, recursive definition, pattern and universe computation. -/
theorem ProofShape.Compute.level_core_bvar_spine
    (R : ProofShape.Compute (ErasedLevelCore D) (ProofShape.mkApps (.bvar i) args) out) :
    ∃ args', out = ProofShape.mkApps (.bvar i) args' ∧
      List.Forall₂ (ProofShape.Compute (ErasedLevelCore D)) args args' := by
  generalize E : ProofShape.mkApps (.bvar i) args = source at R
  induction R generalizing args with
  | base H => exact (erased_level_core_no_bvar_spine (E ▸ H)).elim
  | beta H =>
    cases E
    obtain ⟨args', HE, HA⟩ := H.bvar_spine
    exact ⟨_, HE, HA.imp (fun _ _ H => .beta H)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨args₁, rfl, H₁⟩ := ih₁ E
    obtain ⟨args₂, HE, H₂⟩ := ih₂ rfl
    exact ⟨_, HE, Lean4Lean.List.Forall₂.trans (fun _ _ _ H H' => H.trans H') H₁ H₂⟩
  | app Rf Ra ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := bvar_spine_app E
    obtain ⟨args', rfl, H⟩ := ihf rfl
    exact ⟨args' ++ [_], mkApps_snoc.symm, H.append' (.cons Ra .nil)⟩
  | proj | lam | forallE =>
    have H := congrArg variableHead E
    simp only [variableHead_mkApps, variableHead] at H
    cases H

/-- One neutral argument exposes its own full level-core path. -/
theorem ProofShape.Compute.level_core_bvar_app_inv
    (R : ProofShape.Compute (ErasedLevelCore D) (.app (.bvar i) a) out) :
    ∃ a', out = .app (.bvar i) a' ∧ ProofShape.Compute (ErasedLevelCore D) a a' := by
  obtain ⟨args, E, HA⟩ := R.level_core_bvar_spine (args := [a])
  cases HA with
  | cons H Hnil => cases Hnil; exact ⟨_, E, H⟩

/-- Explicit universe conversion also leaves a bare variable fixed. -/
theorem ProofShape.Compute.level_core_bvar_fixed
    (R : ProofShape.Compute (ErasedLevelCore D) (.bvar i) out) : out = .bvar i := by
  obtain ⟨args, E, HA⟩ := R.level_core_bvar_spine (args := [])
  cases HA
  exact E

end Lean4Lean.VEnv.Strengthening
