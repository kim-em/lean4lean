import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaSpine

/-! # Removing eta before the Eq probe's universe argument

The bare Eq recursor may be eta expanded before receiving Prop as its carrier.
The five pending arguments may then compute independently. Universe exposure
still gives precisely the original proposition-index comparison certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem nonproof_head
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.mkApps f args) T)
    (hn : ¬ IsProof Γ (VExpr.mkApps f args)) : ¬ IsProof Γ f := by
  induction args using List.snoc_induction generalizing T with
  | nil => exact hn
  | snoc args a ih =>
    rw [VExpr.mkApps_snoc] at ht hn
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact ih hf (not_isProof_fn hΓ hf ha hn)

/-- Eta at the bare Eq recursor before its universe argument preserves the
probe's exact comparison criterion. All six arguments and the post-beta tail
may compute; no index or motive recovery is assumed for the pending arguments. -/
theorem eqTypeProbe_initial_eta_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (.sort (.succ .zero))
        (.app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.bvar 0)))
        [.sort .zero, proofErase Γ P,
          proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))),
          .sort v, proofErase Γ Q, .proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have hS : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  have ht := eqTypeProbe_typed heq hΓ hS hP hQ hq
  have hnfull := not_isProof_of_sort hΓ ht
  have hn := nonproof_head hΓ (args := [.sort .zero, P,
    constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v)), .sort v, Q, q]) ht hnfull
  have hc := HasType.const (U := univs) (Γ := Γ) heq.2.2.1
    (ls := [.succ (.succ v), .succ .zero]) (by simp; exact ⟨hv, by trivial⟩) rfl
  have Hpi : ∃ B, env.HasType univs Γ (.const ``Eq.rec [.succ (.succ v), .succ .zero])
      (.forallE (.sort (.succ .zero)) B) := ⟨_, hc⟩
  obtain ⟨B, hf⟩ := Hpi
  have EC : proofErase Γ (.const ``Eq.rec [.succ (.succ v), .succ .zero]) =
      .const ``Eq.rec [.succ (.succ v), .succ .zero] := if_neg hn
  have ES : proofErase Γ (.sort v) = .sort v := if_neg (not_isProof_of_sort hΓ hS)
  have EQ : proofErase Γ q = .proof := proofErase_eq_proof.2
    ⟨_, hq, HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ⟩
  have EH := proofErase_mkApps hΓ (args := [P,
    constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v)), .sort v, Q, q]) ht hnfull
  simp only [List.map_cons, List.map_nil, ES, EQ] at EH
  have H := proofErase_joint_eta_sort_argument_spine_iff heq hs hΓ (w := .zero)
    (by trivial) hf hn (xs := [proofErase Γ P,
      proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))),
      .sort v, proofErase Γ Q, .proof]) (v := v)
  rw [EC, ProofShape.liftN, ← EH] at H
  exact H.trans (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec hv hΓ hP hQ hq)

/-- The initial eta detour also preserves the lower comparison criterion
across arbitrary binder insertion. The equality major is needed only above
the block, and none of the five pending arguments needs a recovery premise. -/
theorem eqTypeProbe_initial_eta_sort_below_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q
      (eqApp (.succ .zero) (.sort .zero) (P.liftN n k) (Q.liftN n k))) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
      (mkApps (.lam (.sort (.succ .zero))
        (.app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.bvar 0)))
        [.sort .zero, proofErase Γ' (P.liftN n k),
          proofErase Γ' (constantEqMotive (.succ .zero) (.sort .zero)
            (P.liftN n k) (.sort (.succ v))),
          .sort v, proofErase Γ' (Q.liftN n k), .proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have H := eqTypeProbe_initial_eta_sort_iff heq hs hregistry hEq hRec hv hΓ'
    (hP.weakN henv W) (hQ.weakN henv W) hq
  exact H.trans (by
    rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ]
    exact proofErase_joint_union_compare_lift_iff heq hs hΓ hΓ' W hP hQ)

end Lean4Lean.VEnv.Strengthening
