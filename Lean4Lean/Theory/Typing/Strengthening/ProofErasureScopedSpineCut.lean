import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSpineRoot
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPrimitiveCut

/-! # A constant-spine cut with its full suffix and argument ancestry

Universe-only roots can be passed without stopping. The selected root acts on
an actual prefix of the original constant spine; computations inside arguments
are retained as component paths and are never mistaken for that root. Both the
whole-source prefix and the post-root suffix are retained.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private const_spine_app
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines

/-- Splitting an argument vector exposes its head prefix and pending suffix. -/
theorem mkApps_append (f : ProofShape) (pre pending : List ProofShape) :
    mkApps f (pre ++ pending) = mkApps (mkApps f pre) pending := by
  induction pre generalizing f with
  | nil => rfl
  | cons a pre ih => exact ih (.app f a)

/-- Either the original spine survives, or a root outside the specified
universe-only fragment acts at a prefix. The cut retains every argument path,
pointwise head-universe equivalence, and the complete computation on both sides.
The fragment need not be a subrelation: it is tested only on actual Step roots. -/
theorem ScopedCompute.const_spine_or_cut
    (hgood : SpineRootLevels Good c)
    (R : ScopedCompute Step Δ (ProofShape.mkApps (.const c ls) args) out) :
    (∃ ls' args', out = ProofShape.mkApps (.const c ls') args' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (ScopedCompute Step Δ) args args') ∨
    (∃ ls' pre pending target,
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute Step Δ) args (pre ++ pending) ∧
      ScopedCompute Step Δ (ProofShape.mkApps (.const c ls) args)
        (ProofShape.mkApps (.const c ls') (pre ++ pending)) ∧
      Step Δ (ProofShape.mkApps (.const c ls') pre) target ∧
      ¬ Good Δ (ProofShape.mkApps (.const c ls') pre) target ∧
      ScopedCompute Step Δ (ProofShape.mkApps target pending) out) := by
  classical
  generalize E : ProofShape.mkApps (.const c ls) args = source at R
  induction R generalizing ls args with
  | @base Δ₀ source out₀ H =>
    cases E
    by_cases HG : Good Δ₀ (ProofShape.mkApps (.const c ls) args) out₀
    · obtain ⟨ls', EO, HL⟩ := hgood HG
      exact .inl ⟨ls', args, EO, HL, .rfl (fun _ _ => .refl)⟩
    · refine .inr ⟨ls, args, [], _, .rfl (fun _ _ => by rfl), ?_, ?_, H, HG, .refl⟩
      · simpa only [List.append_nil] using
          (show List.Forall₂ (ScopedCompute Step Δ₀) args args from .rfl (fun _ _ => .refl))
      · simp only [List.append_nil]; exact .refl
  | beta H =>
    cases E
    obtain ⟨args', EO, HA⟩ := H.const_spine
    exact .inl ⟨ls, args', EO, .rfl (fun _ _ => by rfl), HA.imp (fun _ _ H => .beta H)⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨ls₁, args₁, rfl, HL₁, HA₁⟩ | ⟨ls', pre, pending, target, HL, HA, RP, H, HN, RT⟩
    · rcases ih₂ rfl with ⟨ls₂, args₂, EO, HL₂, HA₂⟩ | ⟨ls', pre, pending, target, HL, HA, RP, H, HN, RT⟩
      · exact .inl ⟨ls₂, args₂, EO, HL₁.trans (fun _ _ _ H K => H.trans K) HL₂,
          HA₁.trans (fun _ _ _ H K => H.trans K) HA₂⟩
      · exact .inr ⟨ls', pre, pending, target,
          HL₁.trans (fun _ _ _ H K => H.trans K) HL,
          HA₁.trans (fun _ _ _ H K => H.trans K) HA, R₁.trans RP, H, HN, RT⟩
    · exact .inr ⟨ls', pre, pending, target, HL, HA, RP, H, HN, RT.trans R₂⟩
  | @app Δ f f' x x' RF RX ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
    rcases ihf rfl with ⟨ls', args', rfl, HL, HA⟩ | ⟨ls', pre, pending, target, HL, HA, RP, H, HN, RT⟩
    · exact .inl ⟨ls', args' ++ [x'], mkApps_snoc.symm, HL, HA.append' (.cons RX .nil)⟩
    · refine .inr ⟨ls', pre, pending ++ [x], target, HL, ?_, ?_, H, HN, ?_⟩
      · simpa only [List.append_assoc] using HA.append' (.cons (ScopedCompute.refl (e := x)) .nil)
      · simpa only [← List.append_assoc, mkApps_snoc] using ScopedCompute.app RP (ScopedCompute.refl (e := x))
      · simpa only [mkApps_snoc] using ScopedCompute.app RT RX
  | proj | lam | forallE =>
    have H := congrArg constHead E
    simp only [constHead_mkApps, constHead] at H
    cases H

end Lean4Lean.VEnv.Strengthening.ProofShape

namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private const_spine_const
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidExposure

/-- Universe conversion changes only the head levels of a constant spine. -/
theorem level_primitive_spine_roots (U : Nat) (c : Name) :
    SpineRootLevels (fun _ => LevelPrimitive U) c := by
  intro Δ ls args out H
  generalize E : ProofShape.mkApps (.const c ls) args = source at H
  cases H with
  | sort =>
    have HE := congrArg constHead E
    simp only [constHead_mkApps, constHead] at HE
    cases HE
  | const HL _ =>
    obtain ⟨rfl, rfl, rfl⟩ := const_spine_const E
    exact ⟨_, rfl, HL⟩

end Lean4Lean.VEnv.Strengthening.ProofShape

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem typed_spine_head : ∀ {args f},
    TypedSource Δ (ProofShape.mkApps f args) → TypedSource Δ f
  | [], _, H => H
  | a :: args, f, H =>
    (ScopedHole.appFn (.hole (Δ := Δ)) a).typed
      (typed_spine_head (f := .app f a) (args := args) H)

/-- Replaying the retained whole-source prefix supplies the actual typing of
its selected head prefix, without replaying the selected root or final suffix. -/
theorem ProofShape.ScopedCompute.spine_cut_source_typed
    (hstep : ErasedScopedPrimitiveDescent Step) (HT : TypedSource Δ source)
    (RP : ScopedCompute Step Δ source (ProofShape.mkApps (.const c ls) (pre ++ pending))) :
    TypedSource Δ (ProofShape.mkApps (.const c ls) pre) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee RP
  have HT' : TypedSource Δ (ProofShape.mkApps (.const c ls) (pre ++ pending)) :=
    ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, EE⟩
  rw [ProofShape.mkApps_append] at HT'
  exact typed_spine_head HT'

end Lean4Lean.VEnv.Strengthening
