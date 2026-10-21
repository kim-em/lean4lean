import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqGeneral

/-! # Full-union head exposure suffices without beta-stable certification

A first primitive has a typed source. At such sources the specialized Eq rule
is an actual general singleton with the same endpoints and guard stage. This
removes the extra primitive alternative from the Eq probe argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Every actually typed primitive in the full joint union is ordinary core
or an actual general singleton with the same raw endpoints. The conversion of
specialized Eq prefixes uses registry agreement, but no beta stability. -/
theorem erased_joint_union_typed_core_singleton
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (HT : TypedSource Δ a) (H : ErasedJointUnion D Δ a b) :
    ErasedIotaPrimitive D a b ∨
      SingletonPrimitiveWith (fun Δ => JointCompare (ErasedJointUnion D) Δ true) Δ a b := by
  rcases erased_joint_union_iff.1 H with H | H | H
  · exact .inl H
  · exact .inr H.2
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  rw [← EΓ, ← Ee] at H
  have HG := proofErase_joint_prefix_as_general heq hs hregistry hΓ ht H
  exact .inr (by simpa only [EΓ, Ee] using HG.2)

/-- A single full-union computation of a lifted Eq probe to a sort descends
its original proposition endpoints. This includes the specialized Eq-prefix
alternative and does not assume a global adequacy or beta-transport law. -/
theorem proofErase_joint_union_eq_probe_compute_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN n) (Q.liftN n)))
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
      (proofErase Γ' (eqSortProbe (P.liftN n) (Q.liftN n) q)) (.sort w)) :
    env.IsDefEqU univs Γ P Q := by
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact proofErase_eq_probe_compute_descend heq (erased_joint_union_descent heq hs)
    erased_joint_union_head (erased_joint_union_descent heq hs) erased_joint_union_head
    (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
    (hregistry.trans hlookup) (hr.eqRec_target heq hn).2.1 hRec
    (erased_joint_union_typed_core_singleton heq hs hregistry) hΓ hΓ' W hP hQ hq R

/-- Sort exposure of just the Eq probe in the full joint union suffices for proposition
strengthening. Certification of future beta/substitution guards is not needed
for this sufficiency proof; semantic head adequacy itself remains unproved. -/
theorem EqProbeSortExposure.joint_union_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hheads : EqProbeSortExposure (ErasedJointUnion D)) : PropositionFront := by
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact Hheads.propositionFront_of_typed_core_singleton heq (erased_joint_union_descent heq hs)
    erased_joint_union_head (erased_joint_union_descent heq hs) erased_joint_union_head
    (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
    (hregistry.trans hlookup) (hr.eqRec_target heq hn).2.1 hRec
    (erased_joint_union_typed_core_singleton heq hs hregistry)

/-- Sort exposure in the full joint union already suffices for proposition
strengthening. Certification of future beta/substitution guards is not needed
for this sufficiency proof; semantic head adequacy itself remains unproved. -/
theorem ScopedSemanticHeadExposure.joint_union_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hheads : ScopedSemanticHeadExposure (ErasedJointUnion D)) : PropositionFront :=
  EqProbeSortExposure.joint_union_propositionFront heq hs hregistry hEq hRec (Hheads.eq_probe_sort heq)

end Lean4Lean.VEnv.Strengthening
