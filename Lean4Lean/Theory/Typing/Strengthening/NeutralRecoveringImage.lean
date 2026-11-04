import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedRecoverableInstantiation

/-! # Recoverable images along changing neutral-related annotations

The selected annotation is raw; the image recovers at an actual equal type.
Actual equality is obtained from the two image typings when the certificate
is consumed. Forward annotation computation preserves this criterion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- An image recovers at a type recursively neutral-related to the selected
annotation. Proof images satisfy this condition at every assigned type.
This is an explicit image certificate, not a coverage assertion. -/
def NeutralRecoveringImage (D : PureObservation.Definitions)
    (Γ : List VExpr) (p : VExpr) (annotation : ProofShape) : Prop :=
  ∃ U, env.HasType univs Γ p U ∧
    NeutralTypeChange 0 annotation (proofErase Γ U) ∧
    (¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U))

/-- Exact native recovery is the reflexive instance. -/
theorem NeutralRecoveringImage.of_recovery
    (hp : env.HasType univs Γ p A)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A)) :
    NeutralRecoveringImage D Γ p (proofErase Γ A) :=
  ⟨A, hp, .refl, HR⟩

/-- A recovered type and neutral relation give an image certificate without
exact recovery at the original annotation. The consumer supplies the image
typing at that annotation, which forces the actual type equality. -/
theorem NeutralRecoveringImage.of_converted
    (hp : env.HasType univs Γ p U)
    (HT : NeutralTypeChange 0 (proofErase Γ A) (proofErase Γ U))
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedComputedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ U)) :
    NeutralRecoveringImage D Γ p (proofErase Γ A) :=
  ⟨U, hp, HT, HR⟩

/-- Forward computation of the selected annotation preserves converted image
recovery. Simulation computes its actual recovered type in parallel, retaining
the recursive neutral relation at both outputs. -/
theorem NeutralRecoveringImage.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : NeutralRecoveringImage D Γ p (proofErase Γ A))
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (R : ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) out) : NeutralRecoveringImage D Γ p out := by
  obtain ⟨U, hpU, HT, HR⟩ := H
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have HAU := (hp.uniqU henv hΓ hpU).of_l henv hΓ hA
  have hstep : ErasedScopedPrimitiveDescent (ErasedComputedJointUnion D) :=
    erased_computed_joint_union_descent heq hs
  obtain ⟨out', RU, HT'⟩ := HT.compute_of_context hstep erased_computed_joint_union_head
    (erased_computed_joint_union_neutral_context heq hs) hΓ HAU rfl rfl rfl R
  obtain ⟨U', HUU, EU⟩ := proofErase_scoped_compute_realize hstep hΓ HAU.hasType.2 rfl rfl RU
  exact ⟨U', HUU.defeq hpU, EU.symm ▸ HT', fun hn => EU.symm ▸ (HR hn).convert RU⟩

/-- Either comparison mode instantiates at a converted recoverable image.
Only the selected binder's actual typing is needed to align the recovered type. -/
theorem NeutralRecoveringImage.compare_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : NeutralRecoveringImage D Γ p (proofErase Γ A))
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (HC : ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) mode
      ((proofErase (A :: Γ) a).inst (proofErase Γ p))
      ((proofErase (A :: Γ) b).inst (proofErase Γ p)) := by
  obtain ⟨U, hpU, HT, HR⟩ := H
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have HAU := (hp.uniqU henv hΓ hpU).of_l henv hΓ hA
  have HI := proofErase_computed_joint_union_compare_inst_converted_recoverable
    heq hs hΓ HAU HT hpU HR ha hb HC
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  rwa [proofErase_instN hΓA hp Ctx.InstN.zero ha,
    proofErase_instN hΓA hp Ctx.InstN.zero hb] at HI

/-- Exact body computation instantiates at a converted recoverable image.
The output remains the literal substitution of the supplied raw output. -/
theorem NeutralRecoveringImage.compute_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : NeutralRecoveringImage D Γ p (proofErase Γ A))
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (ha : env.HasType univs (A :: Γ) a T)
    (R : ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) a) out) :
    ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      ((proofErase (A :: Γ) a).inst (proofErase Γ p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨U, hpU, HT, HR⟩ := H
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have HAU := (hp.uniqU henv hΓ hpU).of_l henv hΓ hA
  have HI := proofErase_computed_joint_union_compute_inst_converted_recoverable
    heq hs hΓ HAU HT hpU HR ha R
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  rwa [proofErase_instN hΓA hp Ctx.InstN.zero ha] at HI

end Lean4Lean.VEnv.Strengthening
