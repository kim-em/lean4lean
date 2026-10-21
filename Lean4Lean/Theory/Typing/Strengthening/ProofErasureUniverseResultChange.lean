import Lean4Lean.Theory.Typing.Strengthening.ProofErasureClosedBoxCarriers
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFunctionAlignment

/-! # Recovery results when a binder changes to a universe

A recovered terminal may become a sort, including a different universe level.
Pi domains remain exact, while typed head separation excludes replacing an
actually equal Pi or registered record by a sort.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
namespace ProofShape

/-- A recovery result may retain its syntax, become a literal sort, or retain
a Pi domain and recursively change its result.
Actual source/target type equality is required separately for typed use. -/
inductive UniverseResultChange : ProofShape → ProofShape → Prop where
  | refl : UniverseResultChange A A
  | toSort : UniverseResultChange A (.sort v)
  | forallE : UniverseResultChange B B' → UniverseResultChange (.forallE A B) (.forallE A B')

/-- The relation survives insertion of any block of variables. -/
theorem UniverseResultChange.liftN (H : UniverseResultChange A B) :
    UniverseResultChange (A.liftN n k) (B.liftN n k) := by
  induction H generalizing k with
  | refl => exact .refl
  | toSort => exact .toSort
  | forallE _ ih => exact .forallE ih

/-- Application may instantiate the changed result with any raw argument. -/
theorem UniverseResultChange.inst (H : UniverseResultChange A B) :
    UniverseResultChange (A.inst x k) (B.inst x k) := by
  induction H generalizing k with
  | refl => exact .refl
  | toSort => exact .toSort
  | forallE _ ih => exact .forallE ih

/-- Every source beta path can be mirrored while retaining the result relation. -/
theorem UniverseResultChange.beta (H : UniverseResultChange A B) (R : BetaRed A out) :
    ∃ out', BetaRed B out' ∧ UniverseResultChange out out' := by
  induction H generalizing out with
  | refl => exact ⟨_, R, .refl⟩
  | toSort => exact ⟨_, .refl, .toSort⟩
  | forallE H ih =>
    obtain ⟨A', B', rfl, RA, RB⟩ := ProofShape.beta_forallE_parts R
    obtain ⟨out', R', H'⟩ := ih RB
    exact ⟨_, .forallE RA R', .forallE H'⟩

/-- Arbitrary scoped source computation has a related target computation,
provided primitives cannot fire at a Pi head. No confluence or primitive
substitution is used in this fixed-context statement. -/
theorem UniverseResultChange.compute
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : UniverseResultChange A B) (R : ScopedCompute Step Δ A out) :
    ∃ out', ScopedCompute Step Δ B out' ∧ UniverseResultChange out out' := by
  induction R generalizing B with
  | base R =>
    cases H with
    | refl => exact ⟨_, .base R, .refl⟩
    | toSort => exact ⟨_, .refl, .toSort⟩
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
    | toSort => exact ⟨_, .refl, .toSort⟩
    | forallE HB =>
      obtain ⟨out', R', H'⟩ := ihB HB
      exact ⟨_, .forallE RA R', .forallE H'⟩
  | app RA RB =>
    cases H with
    | refl => exact ⟨_, .app RA RB, .refl⟩
    | toSort => exact ⟨_, .refl, .toSort⟩
  | proj R =>
    cases H with
    | refl => exact ⟨_, .proj R, .refl⟩
    | toSort => exact ⟨_, .refl, .toSort⟩
  | lam RA RB =>
    cases H with
    | refl => exact ⟨_, .lam RA RB, .refl⟩
    | toSort => exact ⟨_, .refl, .toSort⟩

/-- A recovered sort remains a sort; its syntactic universe level may change. -/
theorem UniverseResultChange.sort_inv (H : UniverseResultChange (.sort u) out) :
    ∃ v, out = .sort v := by
  cases H with
  | refl => exact ⟨_, rfl⟩
  | toSort => exact ⟨_, rfl⟩

end ProofShape
variable [Params]

/-- For actually equal typed results, a source Pi keeps its exact erased
domain. Typed head separation excludes the raw universe-replacement alternative. -/
theorem universe_result_typed_pi
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (HE : env.IsDefEqU univs Γ X Y)
    (EX : proofErase Γ X = .forallE A B) (EY : proofErase Γ Y = out)
    (H : UniverseResultChange (.forallE A B) out) :
    ∃ B', out = .forallE A B' ∧ UniverseResultChange B B' := by
  cases H with
  | refl => exact ⟨_, rfl, .refl⟩
  | forallE HB => exact ⟨_, rfl, HB⟩
  | toSort =>
    obtain ⟨D, C, rfl, _, _, _⟩ := erase_forallE_inv EX
    obtain rfl := erase_sort_inv EY
    exact (henv.headInversion.sort_forallE hΓ
      (HE.symm.typeChain henv hΓ (HE.of_l henv hΓ hX).hasType.2)).elim

/-- Actually equal registered-record results remain exact. Typed head
separation excludes replacement of a registered rigid carrier by a sort. -/
theorem universe_result_typed_record
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs)) (hX : env.HasType univs Γ X (.sort u))
    (HE : env.IsDefEqU univs Γ X Y)
    (EX : proofErase Γ X = ProofShape.mkApps (.const family ls) ps)
    (EY : proofErase Γ Y = out)
    (H : UniverseResultChange (ProofShape.mkApps (.const family ls) ps) out) :
    out = ProofShape.mkApps (.const family ls) ps := by
  generalize ES : ProofShape.mkApps (.const family ls) ps = source at H
  cases H with
  | refl => rfl
  | forallE HB =>
    have Ehead := congrArg ProofShape.constHead ES
    simp only [constHead_mkApps, ProofShape.constHead] at Ehead
    cases Ehead
  | toSort =>
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EX
    obtain rfl := erase_sort_inv EY
    exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      (HE.symm.typeChain henv hΓ (HE.of_l henv hΓ hX).hasType.2)).elim

end Lean4Lean.VEnv.Strengthening
