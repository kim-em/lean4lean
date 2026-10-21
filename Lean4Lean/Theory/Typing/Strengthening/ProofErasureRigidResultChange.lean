import Lean4Lean.Theory.Typing.Strengthening.ProofErasureClosedBoxCarriers
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFunctionAlignment

/-! # Recovery result changes with fixed Pi domains

Replacing an oracle type by an equal closed rigid constant can change recovered
terminal results. Pi domains remain fixed. The raw relation allows a terminal
replacement at any source syntax; actual typing excludes replacements of a
visible Pi, sort or registered record by an incompatible rigid constant.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params]
namespace ProofShape

/-- A recovery result may retain its syntax, replace its terminal type by a
closed rigid constant, or retain a Pi domain and recursively change its result.
Actual source/target type equality is required separately for typed use. -/
inductive RigidResultChange : ProofShape → ProofShape → Prop where
  | refl : RigidResultChange A A
  | closed (hr : env.Rigid family) : RigidResultChange A (.const family [])
  | forallE : RigidResultChange B B' → RigidResultChange (.forallE A B) (.forallE A B')

/-- The relation survives insertion of any block of variables. -/
theorem RigidResultChange.liftN (H : RigidResultChange A B) :
    RigidResultChange (A.liftN n k) (B.liftN n k) := by
  induction H generalizing k with
  | refl => exact .refl
  | closed hr => exact .closed hr
  | forallE _ ih => exact .forallE ih

/-- Application may instantiate the changed result with any raw argument. -/
theorem RigidResultChange.inst (H : RigidResultChange A B) :
    RigidResultChange (A.inst x k) (B.inst x k) := by
  induction H generalizing k with
  | refl => exact .refl
  | closed hr => exact .closed hr
  | forallE _ ih => exact .forallE ih

/-- Every source beta path can be mirrored while retaining the result relation. -/
theorem RigidResultChange.beta (H : RigidResultChange A B) (R : BetaRed A out) :
    ∃ out', BetaRed B out' ∧ RigidResultChange out out' := by
  induction H generalizing out with
  | refl => exact ⟨_, R, .refl⟩
  | closed hr => exact ⟨_, .refl, .closed hr⟩
  | forallE H ih =>
    obtain ⟨A', B', rfl, RA, RB⟩ := ProofShape.beta_forallE_parts R
    obtain ⟨out', R', H'⟩ := ih RB
    exact ⟨_, .forallE RA R', .forallE H'⟩

/-- Arbitrary scoped source computation has a related target computation,
provided primitives cannot fire at a Pi head. No confluence or primitive
substitution is used in this fixed-context statement. -/
theorem RigidResultChange.compute
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : RigidResultChange A B) (R : ScopedCompute Step Δ A out) :
    ∃ out', ScopedCompute Step Δ B out' ∧ RigidResultChange out out' := by
  induction R generalizing B with
  | base R =>
    cases H with
    | refl => exact ⟨_, .base R, .refl⟩
    | closed hr => exact ⟨_, .refl, .closed hr⟩
    | forallE => exact (hhead R).elim
  | beta R =>
    obtain ⟨out', R', H'⟩ := H.beta R
    exact ⟨out', .beta R', H'⟩
  | trans R S ihR ihS =>
    obtain ⟨mid, RM, HM⟩ := ihR H
    obtain ⟨out', RO, HO⟩ := ihS HM
    exact ⟨out', RM.trans RO, HO⟩
  | forallE RA RB ihA ihB =>
    cases H with
    | refl => exact ⟨_, .forallE RA RB, .refl⟩
    | closed hr => exact ⟨_, .refl, .closed hr⟩
    | forallE HB =>
      obtain ⟨out', R', H'⟩ := ihB HB
      exact ⟨_, .forallE RA R', .forallE H'⟩
  | app RA RB =>
    cases H with
    | refl => exact ⟨_, .app RA RB, .refl⟩
    | closed hr => exact ⟨_, .refl, .closed hr⟩
  | proj R =>
    cases H with
    | refl => exact ⟨_, .proj R, .refl⟩
    | closed hr => exact ⟨_, .refl, .closed hr⟩
  | lam RA RB =>
    cases H with
    | refl => exact ⟨_, .lam RA RB, .refl⟩
    | closed hr => exact ⟨_, .refl, .closed hr⟩

end ProofShape

/-- For actually equal typed results, a source Pi keeps its exact erased
domain. Typed head separation excludes the raw closed-replacement alternative. -/
theorem rigid_result_typed_pi
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (HE : env.IsDefEqU univs Γ X Y)
    (EX : proofErase Γ X = .forallE A B) (EY : proofErase Γ Y = out)
    (H : RigidResultChange (.forallE A B) out) :
    ∃ B', out = .forallE A B' ∧ RigidResultChange B B' := by
  cases H with
  | refl => exact ⟨_, rfl, .refl⟩
  | forallE HB => exact ⟨_, rfl, HB⟩
  | closed hr =>
    obtain ⟨D, C, rfl, _, _, _⟩ := erase_forallE_inv EX
    obtain rfl := erase_const_inv EY
    exact (henv.headInversion.forallE_rigid (args := []) hΓ hr (HE.typeChain henv hΓ hX)).elim

/-- Actually equal universe results keep their exact erased level. -/
theorem rigid_result_typed_sort
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (HE : env.IsDefEqU univs Γ X Y)
    (EX : proofErase Γ X = .sort v) (EY : proofErase Γ Y = out)
    (H : RigidResultChange (.sort v) out) : out = .sort v := by
  cases H with
  | refl => rfl
  | closed hr =>
    obtain rfl := erase_sort_inv EX
    obtain rfl := erase_const_inv EY
    exact (henv.headInversion.sort_rigid (args := []) hΓ hr (HE.typeChain henv hΓ hX)).elim

/-- Actually equal registered-record results remain exactly the same erased
carrier. A possible closed replacement forces the original universe and term
argument lists to be empty by rigid-head injectivity. -/
theorem rigid_result_typed_record
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (HE : env.IsDefEqU univs Γ X Y)
    (EX : proofErase Γ X = ProofShape.mkApps (.const family ls) ps)
    (EY : proofErase Γ Y = out)
    (H : RigidResultChange (ProofShape.mkApps (.const family ls) ps) out) :
    out = ProofShape.mkApps (.const family ls) ps := by
  generalize ES : ProofShape.mkApps (.const family ls) ps = source at H
  cases H with
  | refl => rfl
  | forallE HB =>
    have Ehead := congrArg ProofShape.constHead ES
    simp only [constHead_mkApps, ProofShape.constHead] at Ehead
    cases Ehead
  | closed hr =>
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv EX
    obtain rfl := erase_const_inv EY
    obtain ⟨rfl, HL, HA⟩ := henv.headInversion.rigid_rigid (args' := []) hΓ
      (henv.projectionRigid hi) hr (HE.typeChain henv hΓ hX)
    cases HL
    cases HA
    simp only [List.map_nil] at Eargs
    subst ps
    exact ES

end Lean4Lean.VEnv.Strengthening
