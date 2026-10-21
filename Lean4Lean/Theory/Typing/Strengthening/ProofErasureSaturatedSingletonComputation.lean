import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplateComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonDeterminism

/-! # Transporting a saturated singleton output through argument computation

The old guard types the fixed equation-body captures. Computing the supplied
arguments computes their selected slots and hence that body's output. No guard
at the new arguments is needed for the output path itself. A new guard remains
necessary to close a singleton/argument fork at the changed source.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape InductiveSignature
variable [Params]

private theorem open_nil (args : List ProofShape) : openPrefixArguments Δ [] args = args := by
  simp [openPrefixArguments, contextVars, ProofShape.liftN_zero]

/-- For an empty residual telescope, computing the supplied arguments gives a
direct computation of the singleton output. The old guard is reflected only
to type its captures; no guard persistence or target argument typing is assumed.
The computational relation needs only interpreted renaming. -/
theorem SingletonPrefixCode.Valid.saturated_output_compute
    {C : SingletonPrefixCode} (V : C.Valid)
    (heq : env.HasCanonicalEq) (hcmp : ErasedFamilyDescent Cmp)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : VExpr.WF env univs Γ (VExpr.mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some ([], result))
    (HG : C.guardWith Cmp (proofEraseCtx Γ) [] (args.map (proofErase Γ)))
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (args.map (proofErase Γ)) args') :
    ScopedCompute Step (proofEraseCtx Γ)
      (C.output (proofEraseCtx Γ) [] (args.map (proofErase Γ)))
      (C.output (proofEraseCtx Γ) [] args') := by
  obtain ⟨program, hg, hd, HG⟩ := V.realizeWith heq hΓ ha ht hcalc HG
  have HC := V.checkWith heq hcmp hΓ hg ht HG
  have hdom : program.domains = [] := by
    have H := congrArg List.length hd
    simp only [proofEraseDomains_length, List.length_nil] at H
    cases hd' : program.domains with
    | nil => rfl
    | cons => simp [hd'] at H
  obtain ⟨hbodyCtx, hbody⟩ := singleton_prefix_body_typed V.registered V.levels_wf hg
  have hcaps : TelInst env univs Γ
      (program.equationBody.domains.map (·.instL program.levels)) program.captures := by
    refine ⟨by simpa only [List.length_map] using HC.captures_length, ?_⟩
    intro j hj hd
    simpa only [hdom, List.reverse_nil, List.nil_append, List.getElem_map] using
      HC.captures_typed j hj (by simpa only [List.length_map] using hd)
  have EC := proofErase_singleton_prefix_captures heq hΓ V.registered V.large V.zero
    V.levels_wf V.layout_eq V.elim_eq hg HC
  dsimp only at EC
  rw [proofErase_singleton_prefix_arguments hΓ V.registered V.levels_wf hg ht] at EC
  simp only [hdom, List.reverse_nil, List.nil_append, proofEraseDomains, open_nil] at EC
  have RC : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (program.captures.map (proofErase Γ))
      (args'.take C.data.indexOffset ++ singletonSlots C.layout.slot C.layout.fields.length
        ((args'.drop C.data.indexOffset).take C.data.numIndices)) := by
    rw [EC]
    exact (Lean4Lean.List.forall₂_take RA _).append'
      (singletonSlots_compute (Lean4Lean.List.forall₂_take (Lean4Lean.List.forall₂_drop RA _) _))
  have R := proofErase_template_compute_captures hrename hΓ hbodyCtx hbody hcaps RC
  obtain ⟨hl, hb⟩ := V.program_metadata hg
  rw [EC, hl, hb] at R
  simpa only [SingletonPrefixCode.output, open_nil, ProofShape.wrapLams, List.foldr_nil] using R

/-- Saturated singleton/argument computation has a certified residual when the
new argument state supplies its own family guard and empty telescope. The old
output computes to the new primitive output. The new source typing is replayed
from the old one, rather than added as a separate assumption. -/
theorem SingletonPrefixCode.Valid.certified_saturated_residual
    {C : SingletonPrefixCode} (V : C.Valid)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const C.data.name C.levels) args) T)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const C.data.name C.levels) args))
    (hcalc : C.telescope (args.map (proofErase Γ)) = some ([], result))
    (HG : C.guardWith (BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true))
      (proofEraseCtx Γ) [] (args.map (proofErase Γ)))
    (RA : List.Forall₂ (ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) args')
    (hcalc' : C.telescope args' = some ([], result'))
    (HG' : C.guardWith (BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true))
      (proofEraseCtx Γ) [] args') :
    ErasedBetaStableJoint D (proofEraseCtx Γ) (ProofShape.mkApps (.const C.data.name C.levels) args')
        (C.output (proofEraseCtx Γ) [] args') ∧
      ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
        (C.output (proofEraseCtx Γ) [] (args.map (proofErase Γ)))
        (C.output (proofEraseCtx Γ) [] args') := by
  have Rsource := (ScopedCompute.refl (Step := ErasedBetaStableJoint D)
    (Δ := proofEraseCtx Γ) (e := ProofShape.const C.data.name C.levels)).mkApps RA
  obtain ⟨source', HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_beta_stable_joint_descent heq hs) hΓ ht rfl
    (proofErase_const_spine hΓ ht hn) Rsource
  have HT : TypedSource (proofEraseCtx Γ) (ProofShape.mkApps (.const C.data.name C.levels) args') :=
    ⟨Γ, source', T, hΓ, rfl, HE.hasType.2, EE⟩
  have ha' : args'.length = C.arity := by
    have H := RA.length_eq
    simp only [List.length_map] at H
    exact H.symm.trans ha
  refine ⟨.inr ⟨HT, .intro V ha' hcalc' HG'⟩, ?_⟩
  exact V.saturated_output_compute heq
    (beta_stable_family_descent (erased_joint_family_descent (erased_joint_union_descent heq hs)))
    (fun H W => erased_beta_stable_joint_subst heq hs H W.interpretation)
    hΓ ha ⟨_, ht⟩ hcalc HG RA

end Lean4Lean.VEnv.Strengthening
