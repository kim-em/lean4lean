import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalSpineCut

/-! # Exact component costs before a constant spine changes head

Level-only roots and argument computation retain separate counts. This permits
replaying a surviving eta-body spine after its fresh argument is instantiated.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private const_spine_app
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines
open private const_spine_const
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidExposure

/-- Forget only the counts of a pointwise argument history. -/
theorem ScopedArgumentsCount.forget (H : ScopedArgumentsCount Step Δ cost args args') :
    List.Forall₂ (ScopedCompute Step Δ) args args' := by
  induction H with
  | nil => exact .nil
  | cons R _ ih => exact .cons R.forget ih

/-- Raising the primitive relation preserves an argument vector's exact cost. -/
theorem ScopedArgumentsCount.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (H : ScopedArgumentsCount Step Δ cost args args') : ScopedArgumentsCount Target Δ cost args args' := by
  induction H with
  | nil => exact .nil
  | cons R _ ih => exact .cons (R.mono hstep) ih

/-- Split the last argument while retaining its cost and the prefix cost. -/
theorem ScopedArgumentsCount.snoc_inv
    (H : ScopedArgumentsCount Step Δ cost (args ++ [x]) out) :
    ∃ args' x' ca cx, out = args' ++ [x'] ∧ ca+cx = cost ∧
      ScopedArgumentsCount Step Δ ca args args' ∧ ScopedComputeCount Step cx Δ x x' := by
  induction args generalizing cost out with
  | nil =>
    cases H with | cons RX HS =>
      cases HS
      exact ⟨[], _, 0, _, rfl, by omega, .nil, RX⟩
  | cons a args ih =>
    cases H with | cons RA HS =>
      obtain ⟨args', x', ca, cx, rfl, hc, RS, RX⟩ := ih HS
      exact ⟨_ :: args', x', _, cx, rfl, by omega, .cons RA RS, RX⟩

/-- Either head-level and argument paths retain the exact total cost, or a
non-level root acts on the original spine with its counted prefix and tail.
The surviving-spine branch does not discard the cost of its arguments. -/
theorem ScopedComputeCount.const_spine_components_or_cut
    (R : ScopedComputeCount Step cost Δ (ProofShape.mkApps (.const c ls) args) out) :
    (∃ ls' args' ch ca, ch+ca = cost ∧ out = ProofShape.mkApps (.const c ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      ScopedComputeCount Step ch Δ (.const c ls) (.const c ls') ∧
      ScopedArgumentsCount Step Δ ca args args') ∨
    (∃ ls' pre pending target cp ct, cp+1+ct ≤ cost ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute Step Δ) args (pre ++ pending) ∧
      ScopedComputeCount Step cp Δ (ProofShape.mkApps (.const c ls) args)
        (ProofShape.mkApps (.const c ls') (pre ++ pending)) ∧
      Step Δ (ProofShape.mkApps (.const c ls') pre) target ∧
      ¬ LevelPrimitive U (ProofShape.mkApps (.const c ls') pre) target ∧
      ScopedComputeCount Step ct Δ (ProofShape.mkApps target pending) out) := by
  classical
  generalize E : ProofShape.mkApps (.const c ls) args = source at R
  induction R generalizing ls args with
  | @base Δ₀ source out₀ H =>
    cases E
    by_cases HG : LevelPrimitive U (ProofShape.mkApps (.const c ls) args) out₀
    · generalize ES : ProofShape.mkApps (.const c ls) args = source at HG
      cases HG with
      | sort =>
        have EC := congrArg constHead ES
        simp only [constHead_mkApps, constHead] at EC
        cases EC
      | const HL _ =>
        obtain ⟨rfl, rfl, rfl⟩ := const_spine_const ES
        exact .inl ⟨_, [], 1, 0, rfl, rfl, HL, .base H, .nil⟩
    · refine .inr ⟨ls, args, [], _, 0, 0, by omega, .rfl (fun _ _ => by rfl), ?_, ?_, H, HG, .beta .refl⟩
      · simpa only [List.append_nil] using
          (show List.Forall₂ (ScopedCompute Step Δ₀) args args from .rfl (fun _ _ => .refl))
      · simp only [List.append_nil]; exact .beta .refl
  | beta H =>
    cases E
    obtain ⟨args', EO, HA⟩ := H.const_spine
    exact .inl ⟨ls, args', 0, 0, rfl, EO, .rfl (fun _ _ => by rfl), .beta .refl, .beta HA⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨ls₁, args₁, ch₁, ca₁, hc₁, rfl, HL₁, RH₁, HA₁⟩ |
      ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, H, HN, RT⟩
    · rcases ih₂ rfl with ⟨ls₂, args₂, ch₂, ca₂, hc₂, EO, HL₂, RH₂, HA₂⟩ |
        ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, H, HN, RT⟩
      · exact .inl ⟨ls₂, args₂, ch₁+ch₂, ca₁+ca₂, by omega, EO,
          HL₁.trans (fun _ _ _ H K => H.trans K) HL₂, RH₁.trans RH₂, HA₁.trans HA₂⟩
      · exact .inr ⟨ls', pre, pending, target, _, ct, by omega,
          HL₁.trans (fun _ _ _ H K => H.trans K) HL,
          HA₁.forget.trans (fun _ _ _ H K => H.trans K) HA, R₁.trans RP, H, HN, RT⟩
    · exact .inr ⟨ls', pre, pending, target, cp, _, by omega, HL, HA, RP, H, HN, RT.trans R₂⟩
  | @app c₁ Δ f f' c₂ x x' RF RX ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
    rcases ihf rfl with ⟨ls', args', ch, ca, hc, rfl, HL, RH, HA⟩ |
      ⟨ls', pre, pending, target, cp, ct, hc, HL, HA, RP, H, HN, RT⟩
    · exact .inl ⟨ls', args' ++ [x'], ch, ca+c₂, by omega, mkApps_snoc.symm, HL, RH, HA.append (.cons RX .nil)⟩
    · refine .inr ⟨ls', pre, pending ++ [x], target, cp, ct+c₂, by omega, HL, ?_, ?_, H, HN, ?_⟩
      · simpa only [List.append_assoc] using HA.append' (.cons (ScopedCompute.refl (e := x)) .nil)
      · simpa only [← List.append_assoc, mkApps_snoc, Nat.add_zero] using
          ScopedComputeCount.app RP (ScopedComputeCount.beta (BetaRed.refl (e := x)))
      · simpa only [mkApps_snoc] using ScopedComputeCount.app RT RX
  | proj | lam | forallE =>
    have H := congrArg constHead E
    simp only [constHead_mkApps, constHead] at H
    cases H


/-- Minimize outer primitive count over all finite stages. A competitor may
use a larger guard stage, so stage growth alone cannot invalidate a bypass. -/
theorem ScopedComputeCount.minimal_across_stages
    {Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop}
    (R : ScopedComputeCount (Stages stage) cost Δ source out) :
    ∃ selected best, ScopedComputeCount (Stages selected) best Δ source out ∧
      ∀ later k, ScopedComputeCount (Stages later) k Δ source out → best ≤ k := by
  classical
  have H : ∀ cost stage, ScopedComputeCount (Stages stage) cost Δ source out →
      ∃ selected best, ScopedComputeCount (Stages selected) best Δ source out ∧
        ∀ later k, ScopedComputeCount (Stages later) k Δ source out → best ≤ k := by
    intro cost
    induction cost using Nat.strongRecOn with
    | ind cost ih =>
      intro stage RC
      by_cases hx : ∃ later k, k < cost ∧ ScopedComputeCount (Stages later) k Δ source out
      · obtain ⟨later, k, hk, RK⟩ := hx
        exact ih k hk later RK
      · refine ⟨stage, cost, RC, ?_⟩
        intro later k RK
        by_contra hn
        exact hx ⟨later, k, by omega, RK⟩
  exact H cost stage R

end Lean4Lean.VEnv.Strengthening.ProofShape
