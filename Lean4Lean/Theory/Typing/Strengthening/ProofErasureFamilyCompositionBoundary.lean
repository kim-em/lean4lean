import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilySpines
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypedCompositionBoundary

/-! # Future common certificates still do not compose at arbitrary carriers

The constructor of a positive empty structure has a future certificate against
any variable of that structure. Two such links through the same typed
constructor do not compare two distinct bare variables, even in the full union.
This concerns arbitrary carriers, not proposition-only composition.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private unit_constructor_bridge
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypedCompositionBoundary
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

omit [Params] in
private theorem beta_const_fixed (R : ProofShape.BetaRed (.const c ls) out) :
    out = .const c ls := by
  obtain ⟨args, E, H⟩ := (show ProofShape.BetaRed (ProofShape.mkApps (.const c ls) []) out from R).const_spine
  cases H
  exact E

/-- An empty structure constructor compares with every future residual of the
other endpoint. Its null field telescope needs no recursive comparisons. -/
theorem unit_constructor_family
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ (.const info.ctorName ls) a := by
  have HC {Δ a} : JointCompare Step Δ true (.const info.ctorName ls) a :=
    JointCheck.structFields (ls := ls) hi hx (ps := []) hp.symm (fields := []) hf.symm
      (.inr (StructureReplay.ProofFields.of_no_fields hf)) (by intro i h; simp at h)
  refine ⟨fun R _ => ?_, fun W R _ => ?_⟩
  · obtain rfl := beta_const_fixed R
    exact HC
  · obtain rfl := beta_const_fixed R
    exact HC

/-- Two future certificates with an actual common typed intermediate need
not compose, even though every input certificate retains arbitrary future
beta and substitutions. Bare-variable injectivity excludes the composite. -/
theorem unit_family_typed_composition_failure
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : info.nparams = 0) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    ∃ m, env.HasType univs Γ m (.const family ls) ∧
      BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
        (proofErase Γ (.bvar i)) (proofErase Γ m) ∧
      BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
        (proofErase Γ m) (proofErase Γ (.bvar j)) ∧
      ¬ BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
        (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
  obtain ⟨hm, Em, _⟩ := unit_constructor_bridge (Step := Step) hΓ hi hp hx hf hS hiT
  refine ⟨_, hm, ?_, ?_, ?_⟩
  · rw [Em]
    exact (unit_constructor_family hi hp hx hf).joint_symm
  · rw [Em]
    exact unit_constructor_family hi hp hx hf
  · intro H
    have HC := H.base
    rw [show proofErase Γ (.bvar i) = .bvar i from
      if_neg (not_proof_at_positive_type hΓ hS hiT),
      show proofErase Γ (.bvar j) = .bvar j from
      if_neg (not_proof_at_positive_type hΓ hS hjT)] at HC
    exact hne (HC.bvar_injective hhead)

/-- A closed registered positive unit gives all typings for the future-family
composition failure in the full joint union. No proposition front or equality
counterexample follows: the endpoints are already definitionally equal. -/
theorem unit_family_typed_composition_context
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ a m b A, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ a A ∧ env.HasType univs Γ m A ∧ env.HasType univs Γ b A ∧
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
        (proofErase Γ a) (proofErase Γ m) ∧
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
        (proofErase Γ m) (proofErase Γ b) ∧
      ¬ BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
        (proofErase Γ a) (proofErase Γ b) := by
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have h₀ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  obtain ⟨m, hm, H⟩ := unit_family_typed_composition_failure erased_joint_union_head
    hΓ hi hp hx hf (hS.weak0 henv.ordered) h₀ h₁ (by decide)
  exact ⟨Γ, .bvar 0, m, .bvar 1, S, hΓ, h₀, hm, h₁, H⟩

end Lean4Lean.VEnv.Strengthening
