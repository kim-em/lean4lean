import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveCastConsumer
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyBinders

/-! # Recursive comparison and cast computation without endpoint joins

A single inductive grammar alternates computation and future comparison.
Typed eta and structural family rules admit comparisons without a shared reduct;
casts consume these smaller comparison certificates. Computation joins, prefixes
and typed instantiation feed their results back into the same grammar.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- False denotes computation, true denotes future common comparison. The
interpretation proves the future property; no constructor assumes that property
as an oracle. This grammar makes no completeness claim for semantic equality. -/
inductive RecursiveFamilyCast (D : Definitions) :
    Bool → List ProofShape → ProofShape → ProofShape → Prop where
  | prior : RecursiveCastCompute D Δ a b → RecursiveFamilyCast D false Δ a b
  | cast (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
      (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
      (hx : env.HasType univs Γ x X)
      (H : RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ X) (proofErase Γ Y)) :
      RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ (typeCast u X Y q x)) (proofErase Γ x)
  | trans : RecursiveFamilyCast D false Δ a b → RecursiveFamilyCast D false Δ b c →
      RecursiveFamilyCast D false Δ a c
  | app : RecursiveFamilyCast D false Δ f f' → RecursiveFamilyCast D false Δ a a' →
      RecursiveFamilyCast D false Δ (.app f a) (.app f' a')
  | proj : RecursiveFamilyCast D false Δ m m' →
      RecursiveFamilyCast D false Δ (.proj s i m) (.proj s i m')
  | lam : RecursiveFamilyCast D false Δ A A' → RecursiveFamilyCast D false (A :: Δ) b b' →
      RecursiveFamilyCast D false Δ (.lam A b) (.lam A' b')
  | forallE : RecursiveFamilyCast D false Δ A A' → RecursiveFamilyCast D false (A :: Δ) B B' →
      RecursiveFamilyCast D false Δ (.forallE A B) (.forallE A' B')
  | images (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
      (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) (W' : Ctx.SubstEq env univs Γ₀ τ τ Γ)
      (ht : env.HasType univs Γ e T)
      (R : ∀ i, RecursiveFamilyCast D false (proofEraseCtx Γ₀)
        (proofErase Γ₀ (σ i)) (proofErase Γ₀ (τ i))) :
      RecursiveFamilyCast D false (proofEraseCtx Γ₀)
        (proofErase Γ₀ (e.subst σ)) (proofErase Γ₀ (e.subst τ))
  | substCompute (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
      (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
      (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
      (R : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
      RecursiveFamilyCast D false (proofEraseCtx Γ₀)
        (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ))
  | join (hΓ : OnCtx Γ (env.IsType univs))
      (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
      (RA : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ a) shared)
      (RB : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ b) shared) :
      RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)
  | eta (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B)) :
      RecursiveFamilyCast D true (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) (proofErase Γ f)
  | eqFamily (hw : w.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hα : env.HasType univs Γ α (.sort w))
      (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
      (H : RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
      RecursiveFamilyCast D true (proofEraseCtx Γ)
        (proofErase Γ (eqApp w α a a)) (proofErase Γ (eqApp w α a b))
  | lamCommon : RecursiveFamilyCast D true (A :: Δ) b b' →
      RecursiveFamilyCast D true Δ (.lam A b) (.lam A' b')
  | forallSorted (SA : DomainSort Δ A u) (SA' : DomainSort Δ A' u)
      (SB : DomainSort (A :: Δ) B v) (SB' : DomainSort (A :: Δ) B' v)
      (HA : RecursiveFamilyCast D true Δ A A')
      (HB : RecursiveFamilyCast D true (A :: Δ) B B') :
      RecursiveFamilyCast D true Δ (.forallE A B) (.forallE A' B')
  | symm : RecursiveFamilyCast D true Δ a b → RecursiveFamilyCast D true Δ b a
  | beta (H : RecursiveFamilyCast D true Δ a b)
      (RA : ProofShape.BetaRed a a') (RB : ProofShape.BetaRed b b') :
      RecursiveFamilyCast D true Δ a' b'
  | substFamily (H : RecursiveFamilyCast D true Δ a b) (W : ContextSubstitution Δ Δ' τ) :
      RecursiveFamilyCast D true Δ' (a.subst τ) (b.subst τ)
  | prefixes (hΓ : OnCtx Γ (env.IsType univs))
      (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
      (RA : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ a) a')
      (RB : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ b) b')
      (H : RecursiveFamilyCast D true (proofEraseCtx Γ) a' b') :
      RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)
  | instJoined (hΓA : OnCtx (A :: Γ) (env.IsType univs))
      (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c C)
      (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
      (H : RecursiveFamilyCast D true (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) (proofErase (A :: Γ) c))
      (RX : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ x) shared)
      (RY : RecursiveFamilyCast D false (proofEraseCtx Γ) (proofErase Γ y) shared) :
      RecursiveFamilyCast D true (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y))

/-- Simultaneous target of the structural interpretation. Computation is the
existing certified relation; comparison retains all future beta/substitutions. -/
def RecursiveFamilyCast.Interpret (D : Definitions) (family : Bool)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  if family then BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) Δ a b
  else ScopedCompute (ErasedBetaStableJoint D) Δ a b

/-- One induction constructs every future certificate and cast computation.
The cast case consumes its smaller comparison induction hypothesis, and the
join case consumes smaller computation hypotheses; there is no coverage axiom. -/
theorem RecursiveFamilyCast.interpret
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (H : RecursiveFamilyCast D family Δ a b) : RecursiveFamilyCast.Interpret D family Δ a b := by
  induction H with
  | prior R => exact R.certified heq hs hregistry
  | cast hu hΓ hX hY hq hx _ ih => exact proofErase_typeCast_certified heq hs hregistry hu hΓ hX hY hq hx ih
  | trans _ _ ih₁ ih₂ => exact ScopedCompute.trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact ScopedCompute.app ih₁ ih₂
  | proj _ ih => exact ScopedCompute.proj ih
  | lam _ _ ih₁ ih₂ => exact ScopedCompute.lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact ScopedCompute.forallE ih₁ ih₂
  | @images Γ₀ σ Γ τ e T hΓ₀ W W' ht _ ih =>
    have ES : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
    have ET : ErasedSubstAgreement Γ Γ₀ τ (fun i => proofErase Γ₀ (τ i)) := fun _ _ => rfl
    have R := proofErase_compute_subst_images_of_renaming
      (fun H W => erased_beta_stable_joint_subst heq hs H W.interpretation) hΓ₀ W ht ES ih
    rw [← proofErase_subst_with hΓ₀ W ht ES, ← proofErase_subst_with hΓ₀ W' ht ET] at R
    exact R
  | @substCompute Γ₀ σ Γ a A b B hΓ₀ W ha hb _ ih =>
    have ES : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
    have R := ScopedCompute.subst (Step := ErasedBetaStableJoint D) (erased_beta_stable_joint_subst heq hs)
      ih (ContextSubstitution.of_typed hΓ₀ W ES)
    rw [← proofErase_subst_with hΓ₀ W ha ES, ← proofErase_subst_with hΓ₀ W hb ES] at R
    exact R
  | join hΓ ha hb _ _ ihA ihB => exact proofErase_certified_join_family heq hs hΓ ha hb ihA ihB
  | eta hΓ hf => exact proofErase_function_eta_family hΓ hf
  | eqFamily hw hΓ hα ha hb _ ih => exact proofErase_stable_eq_family heq hw hΓ hα ha hb ih
  | lamCommon _ ih => exact BetaStableFamily.lam_common ih
  | forallSorted SA SA' SB SB' _ _ ihA ihB => exact BetaStableFamily.forall_sorted SA SA' SB SB' ihA ihB
  | symm _ ih => exact BetaStableFamily.joint_symm ih
  | beta _ RA RB ih => exact BetaStableFamily.beta (Cmp := fun Δ => JointCompare (ErasedJointUnion D) Δ true) ih RA RB
  | substFamily _ W ih => exact BetaStableFamily.subst (Cmp := fun Δ => JointCompare (ErasedJointUnion D) Δ true) ih W
  | prefixes hΓ ha hb _ _ _ ihA ihB ih => exact BetaStableFamily.certified_prefixes heq hs hΓ ha hb ihA ihB ih
  | instJoined hΓA hb hc hx hy _ _ _ ih ihX ihY =>
    exact proofErase_family_inst_joined heq hs hΓA hb hc hx hy ih ihX ihY

/-- Computation readout preserves the precise source and output. -/
theorem RecursiveFamilyCast.certified
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (H : RecursiveFamilyCast D false Δ a b) : ScopedCompute (ErasedBetaStableJoint D) Δ a b :=
  H.interpret heq hs hregistry

/-- Comparison readout constructs future stability rather than assuming it. -/
theorem RecursiveFamilyCast.future
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (H : RecursiveFamilyCast D true Δ a b) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) Δ a b :=
  H.interpret heq hs hregistry

end Lean4Lean.VEnv.Strengthening
