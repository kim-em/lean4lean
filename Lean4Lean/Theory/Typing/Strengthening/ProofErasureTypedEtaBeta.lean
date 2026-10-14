import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextApplicationSupport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortWitness

/-! # Typed erasures repair the marker eta/beta peak

Typed erasure omits every occurrence of a proof-valued variable, including in
annotations. A fresh eta argument can consequently be replaced by its proof
marker before beta without changing the residual body. For non-proof binders
the retained fresh variable gives the ordinary syntactic eta/beta identity.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Any raw substitution fixing retained variables fixes a typed erasure.
Its images at proof-valued variables are unrestricted and need no typings. -/
theorem proofErase_subst_retained (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) {τ : ProofShape.Subst}
    (H : ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) → τ i = .bvar i) :
    (proofErase Γ e).subst τ = proofErase Γ e := by
  have W := Ctx.SubstEq.id henv.ordered hΓ
  have HA : ErasedSubstAgreement Γ Γ VExpr.Subst.id τ := by
    intro i A hl hn
    simpa only [VExpr.Subst.id, proofErase, if_neg hn] using (H hl hn).symm
  simpa only [VExpr.subst_id] using (proofErase_subst_with hΓ W he HA).symm

/-- A proof binder has no retained occurrences in a typed erased body, so the
fresh eta slot may contain any raw shape when its beta redex is contracted. -/
theorem proofErase_proof_binder_eta_inst (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hb : env.HasType univs (P :: Γ) b B) (x : ProofShape) :
    ((proofErase (P :: Γ) b).liftN 1 1).inst x = proofErase (P :: Γ) b := by
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  let τ : ProofShape.Subst := fun i => match i with
    | 0 => x
    | i + 1 => .bvar (i + 1)
  have HF : (proofErase (P :: Γ) b).subst τ = proofErase (P :: Γ) b := by
    apply proofErase_subst_retained hΓP hb
    intro i A hl hn
    cases i with
    | zero => exact (hn ⟨P.lift, .bvar .zero, hP.weak henv.ordered⟩).elim
    | succ i => rfl
  rw [ProofShape.inst_eq_subst]
  change ((proofErase (P :: Γ) b).liftN 1 1).subst (ProofShape.Subst.one x) = _
  calc
    _ = (proofErase (P :: Γ) b).subst τ := by
      apply ProofShape.subst_liftN_agree
      intro i
      cases i <;> simp [τ, liftVar, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.Subst.id, Nat.add_comm]
    _ = _ := HF

namespace ProofShape
omit [Params] in
/-- Contracting a lifted lambda against the retained fresh variable restores
its raw body literally. No typing or primitive assumptions are needed. -/
theorem lift_eta_inst_bvar (b : ProofShape) : (b.liftN 1 1).inst (.bvar 0) = b := by
  rw [inst_eq_subst]
  change (b.liftN 1 1).subst (Subst.one (.bvar 0)) = b
  calc
    _ = b.subst Subst.id := by
      apply subst_liftN_agree
      intro i
      cases i <;> simp [liftVar, Subst.one, Subst.cons, Subst.id, Nat.add_comm]
    _ = b := subst_id b
end ProofShape

/-- The canonical eta argument, classified by the displayed domain's sort,
restores a typed erased body literally after beta in both proof modes. -/
theorem proofErase_eta_inst (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B) :
    ((proofErase (A :: Γ) b).liftN 1 1).inst (ProofShape.etaArgument u) =
      proofErase (A :: Γ) b := by
  classical
  unfold ProofShape.etaArgument
  split
  · rename_i hu
    have hP := (IsDefEq.sortDF (hA.sort_r henv hΓ) (by trivial) hu).defeq hA
    exact proofErase_proof_binder_eta_inst hΓ hP hb _
  · exact ProofShape.lift_eta_inst_bvar _

/-- Beta at a typed lambda's canonical eta body leaves exactly its original
erased body. The outer annotation is retained independently. -/
theorem proofErase_eta_lambda_beta (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (D : ProofShape) :
    ProofShape.BetaRed
      (.lam D (.app ((ProofShape.lam (proofErase Γ A) (proofErase (A :: Γ) b)).liftN 1)
        (ProofShape.etaArgument u))) (.lam D (proofErase (A :: Γ) b)) := by
  apply ProofShape.BetaRed.lam .refl
  simpa only [ProofShape.liftN, proofErase_eta_inst hΓ hA hb] using
    (ProofShape.BetaRed.beta (A := (proofErase Γ A).liftN 1)
      (b := (proofErase (A :: Γ) b).liftN 1 1) (a := ProofShape.etaArgument u))

/-- The root beta residual of a correctly classified lambda eta guard still
checks against the original lambda, even with a different outer annotation. -/
theorem proofErase_eta_lambda_beta_guard (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (D : ProofShape) :
    ∃ out, ProofShape.BetaRed
      (.lam D (.app ((ProofShape.lam (proofErase Γ A) (proofErase (A :: Γ) b)).liftN 1)
        (ProofShape.etaArgument u))) out ∧
      ProofShape.RawCheckedCompare Step true out
        (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) :=
  ⟨_, proofErase_eta_lambda_beta hΓ hA hb D, .lamCommon (.base .refl)⟩

end Lean4Lean.VEnv.Strengthening
