import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextApplication

/-! # Distinct arguments in contextual application

Inferred function comparisons accept distinct common-compared arguments.
For common function comparisons the two separate application steps reduce the
problem to typed common composition, which remains an explicit hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Ambient soundness at a common original type is the zero-insertion case of
contextual descent. It is used only to align dependent application result types. -/
theorem proofErase_context_compare_reflect (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : ProofShape.ContextCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    env.IsDefEq univs Γ a b T := by
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  have HC := proofErase_context_compare_descend hstep hΓ hΓ W rfl ha hb
    (by simpa only [ProofShape.liftN_zero] using H)
  exact (HC.1 ⟨_, (ha.isType henv hΓ).choose_spec⟩).of_l henv hΓ ha

/-- Inferred function comparison accepts distinct compared arguments. Argument
soundness aligns dependent result types, including their proof classification. -/
theorem proofErase_context_apply_independent
    (hstep : ErasedPrimitiveDescent Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.ContextCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g))
    (HX : ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  classical
  have Hxy := proofErase_context_compare_reflect hstep hΓ hx hy HX
  have hfX := HasType.app hf hx
  have hgY := (IsDefEq.appDF hg Hxy).hasType.2
  by_cases hp : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 (isProof_of_common_type hΓ hfX hgY hp)]
    exact .refl
  · have hp' : ¬ IsProof Γ (.app g y) := fun h => hp (isProof_of_common_type hΓ hgY hfX h)
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app g y) = .app _ _ from if_neg hp']
    exact .app HF HX

/-- Candidate typed common-composition law for contextual certificates.
The middle original must share the endpoint type. `ContextPrefixWitness`
refutes the uniform law even for a fragment with typed descent and substitution
closure. Richer computational fragments require separate investigation; no
strict reduction from the proposition front is claimed. -/
def ContextCommonComposition (Step : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ a b c T}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a T → env.HasType univs Γ b T → env.HasType univs Γ c T →
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) →
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ b) (proofErase Γ c) →
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ c)

/-- Common function application to distinct compared arguments follows from
common composition: first change the function at x, then change x to y at g.
The intermediate g x has the common result type required by composition. -/
theorem ContextCommonComposition.apply
    (Hcomp : ContextCommonComposition Step) (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HF : ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ f) (proofErase Γ g))
    (HX : ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  have Hxy := proofErase_context_compare_reflect hstep hΓ hx hy HX
  exact Hcomp hΓ (.app hf hx) (.app hg hx) (IsDefEq.appDF hg Hxy).hasType.2
    (proofErase_context_apply_same hstep hsubst hΓ hf hg hx HF)
    (proofErase_context_apply_independent hstep hΓ hg hg hx hy .refl HX)

end Lean4Lean.VEnv.Strengthening
