import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointSingletonBeta

/-! # Certified singleton residuals after arbitrary argument beta reduction

The transported proposition guard certifies the new prefix. Its output is the
beta reduct of the old output, including all dependent annotations. These are
raw residuals in the existing joint grammar, not just operational replay.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open PureObservation
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private beta_congrRel from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointSingletonBeta
open private const_spine_ne_proof from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

private theorem beta_arguments_replay
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : ∀ a ∈ args, VExpr.WF env univs Γ a)
    (HA : List.Forall₂ ProofShape.BetaRed (args.map (proofErase Γ)) rawArgs) :
    ∃ args', List.Forall₂ VExpr.BetaRed args args' ∧ args'.map (proofErase Γ) = rawArgs := by
  induction args generalizing rawArgs with
  | nil => cases HA; exact ⟨[], .nil, rfl⟩
  | cons a args ih =>
    cases HA with
    | cons HR Hrest =>
      obtain ⟨T, ha⟩ := ht a (by simp)
      obtain ⟨a', Ra, Ea⟩ := proofErase_beta_replay hΓ ha HR
      obtain ⟨args', Hargs, Eargs⟩ := ih
        (fun a ha => ht a (List.mem_cons_of_mem _ ha)) Hrest
      exact ⟨a' :: args', .cons Ra Hargs, by simp only [List.map_cons, Ea, Eargs]⟩

namespace SingletonPrefixCode
variable {C : SingletonPrefixCode}

/-- Under proposition beta stability, beta reduction of supplied raw arguments
leaves an actual general joint singleton primitive. Its exact new output is a
beta reduct of the original generated output. No new guard is assumed. -/
theorem Valid.joint_beta_residual (V : C.Valid)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (HT : ProofShape.TypedSource Δ (ProofShape.mkApps (.const C.data.name C.levels) args))
    (ha : args.length = C.arity)
    (hcalc : C.telescope args = some (domains, result))
    (HG : C.guardWith (fun Δ => ProofShape.JointCompare (ErasedJointUnion D) Δ true) Δ domains args)
    (HA : List.Forall₂ ProofShape.BetaRed args args') :
    ∃ domains' result', C.telescope args' = some (domains', result') ∧
      ProofShape.BetaRed (C.output Δ domains args) (C.output Δ domains' args') ∧
      ProofShape.JointSingletonPrimitive (ErasedJointUnion D) Δ
        (ProofShape.mkApps (.const C.data.name C.levels) args') (C.output Δ domains' args') := by
  obtain ⟨Γ, source, T, hΓ, rfl, ht, Es⟩ := HT
  obtain ⟨original, rfl, Eargs⟩ := proofErase_const_spine_inv Es
  have hn : ¬ IsProof Γ (mkApps (.const C.data.name C.levels) original) := by
    intro hp
    exact const_spine_ne_proof (Es.symm.trans (proofErase_eq_proof.2 hp))
  rw [Eargs] at ha hcalc HG HA ⊢
  simp only [List.length_map] at ha
  obtain ⟨program, hg, hd, HG₀⟩ := V.realizeWith heq hΓ ha ⟨_, ht⟩ hcalc HG
  have HC := V.checkWith heq (erased_joint_family_descent (erased_joint_union_descent heq hs))
    hΓ hg ⟨_, ht⟩ HG₀
  obtain ⟨newArgs, Hargs, Enew⟩ := beta_arguments_replay hΓ
    (mkApps_arguments_wf henv hΓ ⟨_, ht⟩).2 HA
  have HP : PrefixUnfold env univs recursorData Γ C.data.name C.levels original program.rhs :=
    .intro V.lookup V.registered rfl V.large V.levels_wf V.zero hg HC
  obtain ⟨newRhs, HP', Rout⟩ := singleton_prefix_congr beta_congrRel
    (beta_congrRel.argRel (fun hΓ R ht => beta_eq hΓ ht R)) hΓ HP Hargs
  cases HP' with
  | @intro data' program' hlookup _ _ _ _ _ hg' HC' =>
    cases Option.some.inj (V.lookup.symm.trans hlookup)
    have Rsource : VExpr.BetaRed (mkApps (.const C.data.name C.levels) original)
        (mkApps (.const C.data.name C.levels) newArgs) := .mkApps .refl Hargs
    have hn' := mt (isProof_congr hΓ (beta_eq hΓ ht Rsource)).2 hn
    have hcalc' := V.telescope_eq hΓ hg' ⟨_, HC'.source_typed⟩
    rw [Enew] at hcalc'
    have HT' : ProofShape.TypedSource (proofEraseCtx Γ)
        (ProofShape.mkApps (.const C.data.name C.levels) args') := by
      refine ⟨Γ, _, _, hΓ, rfl, HC'.source_typed, ?_⟩
      rw [proofErase_const_spine hΓ HC'.source_typed hn', Enew]
    have HG' := V.joint_family_guard_beta heq hs Hbeta hΓ hg hg' ⟨_, ht⟩ Hargs HG₀
    have HG' := (V.guardWith_iff heq hΓ hg' ⟨_, HC'.source_typed⟩).2 HG'
    rw [Enew] at HG'
    have Hout := proofErase_beta_forward hΓ (HC.defeq henv hΓ).hasType.2 Rout
    rw [V.output_eq heq hΓ hg HC hn, V.output_eq heq hΓ hg' HC' hn', hd, Enew] at Hout
    refine ⟨_, _, hcalc', Hout, HT', .intro V ?_ hcalc' HG'⟩
    rw [← Enew, List.length_map, ← Hargs.length_eq]
    exact ha

end SingletonPrefixCode

/-- A general joint singleton contraction commutes with any finite raw beta
path from its source: the old output beta reduces to a shared term, and the
beta-reduced source has an actual singleton contraction to that same term.
The sole stability premise is proposition beta stability of the joint union. -/
theorem proofErase_joint_singleton_beta_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (H : ProofShape.JointSingletonPrimitive (ErasedJointUnion D) Δ source out)
    (RB : ProofShape.BetaRed source reduced) :
    ∃ shared, ProofShape.BetaRed out shared ∧
      ProofShape.JointSingletonPrimitive (ErasedJointUnion D) Δ reduced shared := by
  obtain ⟨HT, H⟩ := H
  cases H with
  | intro V ha hcalc HG =>
    obtain ⟨args', rfl, HA⟩ := RB.const_spine
    obtain ⟨_, _, _, R, H⟩ := V.joint_beta_residual heq hs Hbeta HT ha hcalc HG HA
    exact ⟨_, R, H⟩

/-- The same exact beta residual covers the specialized Eq branch at typed
sources, by its general singleton presentation. The residual uses the general
branch and retains the exact old output; no carrier decoder is needed. -/
theorem proofErase_joint_prefix_beta_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaStability (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (H : ProofShape.JointPrefixPrimitive (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out)
    (RB : ProofShape.BetaRed (proofErase Γ e) reduced) :
    ∃ shared, ProofShape.BetaRed out shared ∧
      ProofShape.JointSingletonPrimitive (ErasedJointUnion D) (proofEraseCtx Γ) reduced shared :=
  proofErase_joint_singleton_beta_residual heq hs Hbeta
    (proofErase_joint_prefix_as_general heq hs hregistry hΓ ht H) RB

end Lean4Lean.VEnv.Strengthening
