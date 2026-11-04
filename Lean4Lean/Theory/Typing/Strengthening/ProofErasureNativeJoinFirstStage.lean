import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeJoinContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeJoinInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointFirstStageSubstitution

/-! # Singleton and Eq computations under combined native substitutions

The combined image law transports every stage-zero guard under its generated
residual telescope. The existing generic first-stage theorem therefore preserves
whole singleton and Eq-prefix paths and their exact substituted outputs. No
confluence or native recovery at higher computation stages is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {hq : QuotRegistered env} {F : List VExpr → VExpr → Prop}
variable [NativeFamilyFramework.InputLaws (definitions hq) F]

/-- The full combined checker transport supplies the generic telescope-stable
guard-substitution interface; no remaining guard callback is assumed. -/
theorem guardSubstitution
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    ComputedZeroGuardSubstitution (definitions hq) (ImageSubstitution hq F) :=
  ⟨(fun W => W.interpretation), (fun W => W.cons), (fun H => transport hcon H)⟩

/-- Exact simultaneous substitution of a first-layer path, including generated
singleton programs and specialized Eq prefixes guarded by recursive checking. -/
theorem compute_subst
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : Images hq F Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedComputedJointStage (definitions hq) 1)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedComputedJointStage (definitions hq) 1) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht ES]
  exact R.transport_firstStage_guard heq (sound hq) (guardSubstitution hcon) W.wf ht rfl rfl
    (ImageSubstitution.of_typed hΓ₀ W ES HI)

/-- A value whose assigned type computes to a finite-aligned native output
instantiates an entire first-stage path without increasing its stage. -/
theorem compute_inst
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (HR : Recovery hq F Γ p (proofErase Γ A))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage (definitions hq) 1)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage (definitions hq) 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
    compute_subst heq hcon hΓ W (erasedSubstAgreement_one hΓA hp) (Images.inst HR) ht R

/-- Whole first-stage computation paths cross the same combined binder change
as recursive comparisons, retaining the exact raw computation endpoints. -/
theorem compute_context
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HB : NativeFamilyFramework.Alignment (definitions hq) F Γ B mid)
    (RA : Compute (Step hq) (proofErase Γ A) mid)
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedComputedJointStage (definitions hq) 1)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage (definitions hq) 1)
      (proofEraseCtx (B :: Γ)) (proofErase (A :: Γ) e) out := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using
    R.transport_firstStage_guard heq (sound hq) (guardSubstitution hcon) hΓA ht rfl rfl
      (ImageSubstitution.aligned_context hΓ HAB HB RA)

/-- The combined image certificate supplies paired beta-redex comparison from
a common-typed body certificate. Arbitrary heterogeneous argument substitution
and unrestricted proposition beta stability are not claimed. -/
theorem argument_beta
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p A)
    (HR : Recovery hq F Γ p (proofErase Γ A))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ) mode
      (proofErase Γ (.app (.lam A a) p)) (proofErase Γ (.app (.lam A b) p)) := by
  obtain ⟨_, hA⟩ := hp.isType henv hΓ
  exact .compute
    (.beta (proofErase_beta_forward hΓ (HasType.app (HasType.lam hA ha) hp) .beta))
    (.beta (proofErase_beta_forward hΓ (HasType.app (HasType.lam hA hb) hp) .beta))
    (compare_inst hcon hΓ hA hp HR ha hb H)

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
