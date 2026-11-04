import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelExposure

/-! # Rigid application spines with universe-changing roots

A primitive may change a rigid head's universe arguments but not its term
arguments. Compatible computation consequently preserves the family and arity,
retaining both universe equivalence and every argument's computation path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
open private const_spine_app
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines
open private ProofShape.const_spine_const
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidExposure
namespace ProofShape

/-- Primitive roots at this family only change its universe arguments. -/
def SpineRootLevels (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (family : Name) : Prop :=
  ∀ {Δ ls args out}, Step Δ (mkApps (.const family ls) args) out →
    ∃ ls', out = mkApps (.const family ls') args ∧ List.Forall₂ (· ≈ ·) ls ls'

/-- Finite scoped computation retains every argument path and pointwise
universe equivalence at a stable rigid family spine. -/
theorem ScopedCompute.const_spine_levels
    (hn : SpineRootLevels Step family)
    (R : ScopedCompute Step Δ (mkApps (.const family ls) args) out) :
    ∃ ls' args', out = mkApps (.const family ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (ScopedCompute Step Δ) args args' := by
  generalize E : mkApps (.const family ls) args = source at R
  induction R generalizing ls args with
  | base H =>
    obtain ⟨ls', HE, HL⟩ := hn (E ▸ H)
    exact ⟨ls', args, HE, HL, .rfl (fun _ _ => .refl)⟩
  | beta H =>
    cases E
    obtain ⟨args', HE, HA⟩ := H.const_spine
    exact ⟨ls, args', HE, .rfl (fun _ _ => by rfl), HA.imp (fun _ _ H => .beta H)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨ls₁, args₁, rfl, HL₁, HA₁⟩ := ih₁ E
    obtain ⟨ls₂, args₂, HE, HL₂, HA₂⟩ := ih₂ rfl
    exact ⟨ls₂, args₂, HE, HL₁.trans (fun _ _ _ H K => H.trans K) HL₂,
      HA₁.trans (fun _ _ _ H K => H.trans K) HA₂⟩
  | app Rf Ra ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
    obtain ⟨ls', args', rfl, HL, HA⟩ := ihf rfl
    exact ⟨ls', args' ++ [_], mkApps_snoc.symm, HL, HA.append' (.cons Ra .nil)⟩
  | proj | lam | forallE =>
    have H := congrArg constHead E
    simp only [constHead_mkApps, constHead] at H
    cases H

end ProofShape
variable [Params]

/-- All finite level-extended stages preserve rigid families at primitive
spines, including arbitrary numbers of supplied parameters. -/
theorem erased_level_recovered_stage_spine_levels (heq : env.HasCanonicalEq)
    (hc : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) (stage : Nat) :
    SpineRootLevels (ErasedLevelRecoveredStage D stage) family := by
  intro Δ ls args out H
  have H := erased_level_recovered_stage_rigid_root heq hc hD stage H (constHead_mkApps _ _)
  generalize E : mkApps (.const family ls) args = source at H
  cases H with
  | sort =>
    have HE := congrArg constHead E
    simp only [constHead_mkApps, constHead] at HE
    cases HE
  | const HL hw =>
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_const E
    exact ⟨_, rfl, HL⟩

/-- Rigid spine universe stability holds in the closed union. -/
theorem erased_level_recovered_union_spine_levels (heq : env.HasCanonicalEq)
    (hc : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    SpineRootLevels (ErasedLevelRecoveredUnion D) family := by
  rintro Δ ls args out ⟨stage, H⟩
  exact erased_level_recovered_stage_spine_levels heq hc hD stage H

end Lean4Lean.VEnv.Strengthening
