import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecursiveBox
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveBoxExample

/-! # Inhabited Box binder conversion without computational joins

The earlier function-field example now supports changing the whole Box binder.
Its carrier types are outside the old Pi/neutral relation, but recovery and all
typed comparison constructors transport through the extended relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private BoxCarrierAlignment.erase_box
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveBoxGuard
variable [Params]

/-- The no-join Box example supports arbitrary certified typed body comparison
under the changed binder, as well as every certified carrier guard. This
consumes the new recovery/checking interaction rather than assuming it. The
Box registration remains explicit; no environment extension is asserted. -/
theorem recursive_box_binder_example
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' A B, OnCtx Γ' (env.IsType univs) ∧
      env.IsDefEq univs Γ' A B (.sort (.succ .zero)) ∧
      BoxTypeChange family 0 (proofErase Γ' A) (proofErase Γ' B) ∧
      ¬ NeutralTypeChange 0 (proofErase Γ' A) (proofErase Γ' B) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' A) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' B) shared) ∧
      (∃ x, env.HasType univs Γ' x A) ∧
      (∀ x y, env.HasType univs Γ' x A → env.HasType univs Γ' y A →
        (JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ')
          (proofErase Γ' A) (proofErase Γ' x) (proofErase Γ' y) ↔
        JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ')
          (proofErase Γ' B) (proofErase Γ' x) (proofErase Γ' y))) ∧
      (∀ x y T mode, env.HasType univs (A :: Γ') x T → env.HasType univs (A :: Γ') y T →
        JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ')) mode
          (proofErase (A :: Γ') x) (proofErase (A :: Γ') y) →
        JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (B :: Γ')) mode
          (proofErase (B :: Γ') x) (proofErase (B :: Γ') y)) := by
  obtain ⟨Γ', X, Y, hΓ', HXY, HT, _, Hbox, Hnot, Hjoin, Hinh, _⟩ :=
    recursive_box_function_field_example heq hs hD hi hp hf hshape hc hΓ
  have HTbox : BoxTypeChange family 0
      (proofErase Γ' (.app (.const family []) X))
      (proofErase Γ' (.app (.const family []) Y)) := by
    rw [BoxCarrierAlignment.erase_box hc hΓ' HXY.hasType.1,
      BoxCarrierAlignment.erase_box hc hΓ' HXY.hasType.2]
    exact .box HT.toBox
  refine ⟨Γ', _, _, hΓ', Hbox, HTbox, Hnot, Hjoin, Hinh, ?_, ?_⟩
  · intro x y hx hy
    exact ⟨proofErase_certified_recursive_box_carrier heq hs hi hp hf hshape hc hD
        hΓ' hx hy Hbox.toU HTbox,
      proofErase_certified_recursive_box_carrier heq hs hi hp hf hshape hc hD
        hΓ' (Hbox.defeq hx) (Hbox.defeq hy) Hbox.symm.toU HTbox.symm⟩
  · intro x y T mode hx hy H
    exact proofErase_certified_recursive_box_context heq hs hi hp hf hshape hc hD
      hΓ' Hbox HTbox hx hy H

end Lean4Lean.VEnv.Strengthening
