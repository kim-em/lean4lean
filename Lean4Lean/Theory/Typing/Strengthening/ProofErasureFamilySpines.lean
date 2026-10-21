import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinFamily

/-! # Future family certificates inside constant-headed applications

Beta cannot replace a constant spine's head. Independent future argument
reductions can therefore be compared using their individual certificates,
including certificates that relate eta endpoints without computational joins.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Reverse all current and future joint comparisons in a family certificate. -/
theorem BetaStableFamily.joint_symm
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ a b) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ b a :=
  ⟨fun R S => (H.1 S R).symm, fun W R S => (H.2 W S R).symm⟩

private theorem compare_args
    (H : List.Forall₂ (BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ) args other)
    (RA : List.Forall₂ ProofShape.BetaRed args left)
    (RB : List.Forall₂ ProofShape.BetaRed other right)
    (HF : ∀ mode, JointCompare Step Δ mode f g) :
    JointCompare Step Δ mode (ProofShape.mkApps f left) (ProofShape.mkApps g right) := by
  induction H generalizing left right f g with
  | nil => cases RA; cases RB; exact HF mode
  | cons H HT ih =>
    cases RA with
    | cons R RT =>
      cases RB with
      | cons S ST =>
        exact ih (left := _) (right := _) (f := .app f _) (g := .app g _)
          RT ST (fun _ => .app (HF false) (H.1 R S))

private theorem spine_beta
    (H : List.Forall₂ (BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ) args other)
    (RA : ProofShape.BetaRed (ProofShape.mkApps (.const c ls) args) left)
    (RB : ProofShape.BetaRed (ProofShape.mkApps (.const c ls) other) right) :
    JointCompare Step Δ mode left right := by
  obtain ⟨leftArgs, rfl, HA⟩ := RA.const_spine
  obtain ⟨rightArgs, rfl, HB⟩ := RB.const_spine
  exact compare_args H HA HB (fun _ => .leaf .refl)

/-- Individual future argument certificates combine under any fixed constant
head. No head rigidity for primitive computation is required: the future paths
in a family certificate are beta paths, which preserve every constant head. -/
theorem BetaStableFamily.const_spine
    (H : List.Forall₂ (BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ) args other) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      (ProofShape.mkApps (.const c ls) args) (ProofShape.mkApps (.const c ls) other) := by
  refine ⟨fun RA RB => spine_beta H RA RB, ?_⟩
  intro Δ' τ p q W RA RB
  have HT : List.Forall₂ (BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ')
      (args.map (·.subst τ)) (other.map (·.subst τ)) := by
    clear RA RB
    induction H with
    | nil => exact .nil
    | cons H HT ih => exact .cons (H.subst W) ih
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at RA RB
  exact spine_beta HT RA RB

end Lean4Lean.VEnv.Strengthening
