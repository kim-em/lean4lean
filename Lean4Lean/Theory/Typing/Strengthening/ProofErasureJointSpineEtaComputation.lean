import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPropositionEta

/-! # Finite computation with removable function-spine eta

Ordinary joint computation may interleave with function eta at any nonempty
application prefix whose consumed argument is exactly recoverable, or whose
eta function is scoped-normal. The latter includes the first proposition
index of Eq.rec without recovery of that proposition. All pending arguments
are retained. Such finite paths expose exactly the same literal universes as
ordinary joint computation. Eta inside arbitrary arguments, structure eta,
and other prefixes consuming unrecoverable arguments are not covered.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Finite interleavings of full-joint computation and certified function-spine eta.
An eta step records either recovery of its consumed argument at its original
domain, or scoped normality of the eta function. Proof arguments meet recovery
vacuously. This is a proved fragment, not an assertion that arbitrary
FullReduction paths have these certificates. -/
inductive JointSpineEtaCompute (D : PureObservation.Definitions) :
    List ProofShape → ProofShape → ProofShape → Prop where
  | compute : ScopedCompute (ErasedJointUnion D) Δ a b → JointSpineEtaCompute D Δ a b
  | eta (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
      (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
      (hp : env.HasType univs Γ p A)
      (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D)
        (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A)) :
      JointSpineEtaCompute D (proofEraseCtx Γ)
        (mkApps (proofErase Γ (.app f p)) xs)
        (mkApps (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u)))
          (proofErase Γ p :: xs))
  | normalEta (H : ScopedNormalSyntax (ErasedJointUnion D) Δ
      (.lam A (.app (f.liftN 1) (.bvar 0)))) :
      JointSpineEtaCompute D Δ (mkApps (.app f x) xs)
        (mkApps (.lam A (.app (f.liftN 1) (.bvar 0))) (x :: xs))
  | trans : JointSpineEtaCompute D Δ a b → JointSpineEtaCompute D Δ b c →
      JointSpineEtaCompute D Δ a c

/-- An arbitrary finite path of certified spine eta and computation can be
removed before a universe-exposing continuation. The exact target universe is
preserved; induction composes the unchanged tail and assumes no normalization. -/
theorem JointSpineEtaCompute.sort_continuation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : JointSpineEtaCompute D Δ a b)
    (RT : ScopedCompute (ErasedJointUnion D) Δ b (.sort v)) :
    ScopedCompute (ErasedJointUnion D) Δ a (.sort v) := by
  induction R with
  | compute R => exact R.trans RT
  | eta hΓ hA hf hn hp HR =>
    exact (proofErase_joint_eta_spine_sort_iff heq hs hΓ hA hf hn hp HR).1 RT
  | normalEta H =>
    exact (ScopedCompute.fixed_eta_spine_sort_iff erased_joint_union_head
      (fun R => R.fixed_of_scoped_normal H)).1 RT
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ RT)

/-- Allowing any finite interleaving of the two certified function-spine eta rules does
not enlarge literal-universe exposure in the full joint union. -/
theorem jointSpineEtaCompute_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    JointSpineEtaCompute D Δ a (.sort v) ↔
      ScopedCompute (ErasedJointUnion D) Δ a (.sort v) :=
  ⟨fun R => R.sort_continuation heq hs .refl, JointSpineEtaCompute.compute⟩

/-- Eta before the first proposition index belongs to the interleaving
fragment without recovery of the consumed argument. Later certified eta and
full-joint computation can therefore follow this step in any finite order. -/
theorem eqRec_prop_eta_interleaving
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs)) :
    JointSpineEtaCompute D (proofEraseCtx Γ)
      (mkApps (.app (.app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.sort .zero)) p) xs)
      (mkApps (.lam (.sort .zero)
        (.app (.app (.const ``Eq.rec [.succ (.succ v), .succ .zero]) (.sort .zero)) (.bvar 0)))
        (p :: xs)) :=
  .normalEta (eqRec_prop_eta_scoped_normal heq hs hregistry hEq hRec hv hΓ)

/-- Eq probes retain their exact lower-index criterion through arbitrary finite
interleavings in this fragment. The equality proof may exist only above the
inserted block. Recovery or normality remains local to the eta steps, not an
assumed coverage theorem for all proposition arguments or semantic reductions. -/
theorem eqTypeProbe_spine_eta_sort_below_iff
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
    JointSpineEtaCompute D (proofEraseCtx Γ')
      (proofErase Γ' (eqTypeProbe (.succ v) (.sort v) (P.liftN n k) (Q.liftN n k) q)) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  apply (jointSpineEtaCompute_sort_iff heq hs).trans
  have H := eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec hv hΓ'
    (hP.weakN henv W) (hQ.weakN henv W) hq
  rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ] at H
  exact H.trans (proofErase_joint_union_compare_lift_iff heq hs hΓ hΓ' W hP hQ)

end Lean4Lean.VEnv.Strengthening
