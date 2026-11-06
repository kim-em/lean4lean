import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveAnnotationChecking

/-! # Typed checking of paired annotation variants

Marked domains carry actual sort witnesses and future comparison certificates
in one ambient context. Local binders protect those certificates while paired
beta substitution duplicates the marked lambdas. Reading the resulting relation
requires only a typed left source, not a normalization or annotation-join premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Ambient domain pairs usable as marked lambda annotations. The witnesses
are constructive certificates, and require neither a join nor completeness of
comparison for semantic equality. -/
def CertifiedAnnotationDomains (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (A C : ProofShape) : Prop :=
  ∃ u, DomainSort Δ A u ∧ DomainSort Δ C u ∧
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ A C

/-- Reversing a marked domain pair preserves its certificates. -/
theorem CertifiedAnnotationDomains.symm (H : CertifiedAnnotationDomains Step Δ A C) :
    CertifiedAnnotationDomains Step Δ C A := by
  obtain ⟨u, SA, SC, H⟩ := H
  exact ⟨u, SC, SA, H.joint_symm⟩

/-- Further beta reduction of one marked annotation retains the ambient guard. -/
theorem CertifiedAnnotationDomains.beta_left
    (H : CertifiedAnnotationDomains Step Δ A C) (R : ProofShape.BetaRed A A') :
    CertifiedAnnotationDomains Step Δ A' C := by
  obtain ⟨u, SA, SC, H⟩ := H
  exact ⟨u, SA.beta R, SC, H.beta R .refl⟩

/-- A common interpreted ambient substitution preserves domain certificates. -/
theorem CertifiedAnnotationDomains.subst
    (H : CertifiedAnnotationDomains Step Δ A C) (W : ContextSubstitution Δ Δ' τ) :
    CertifiedAnnotationDomains Step Δ' (A.subst τ) (C.subst τ) := by
  obtain ⟨u, SA, SC, H⟩ := H
  exact ⟨u, W.sort SA, W.sort SC, H.subst W⟩

omit [Params] in
private theorem subst_shift (a : ProofShape) :
    a.subst (fun i => .bvar (i + n)) = a.liftN n := by
  simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
    (subst_bvar_liftN (n := n) (k := 0) a)

private theorem ambient_cons
    (W : ContextSubstitution Δ (proofEraseCtx Γ) (fun i => .bvar (i + n)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ContextSubstitution Δ (proofEraseCtx (A :: Γ)) (fun i => .bvar (i + (n + 1))) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have R : ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx (A :: Γ))
      (fun i => .bvar (liftVar 1 i 0)) :=
    (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one).interpretation
  have H : ContextSubstitution Δ (proofEraseCtx (A :: Γ))
      (fun i => (ProofShape.bvar (i + n)).subst (fun j => .bvar (liftVar 1 j 0))) := W.comp R
  intro Γ₀ hΓ₀ EΓ₀
  simpa only [ProofShape.subst, liftVar, Nat.not_lt_zero, ↓reduceIte,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H hΓ₀ EΓ₀

/-- A paired annotation variant checks in either mode at any typed left
realization. Interpreted weakening of the ambient certificates follows every
local binder, including dependent annotations and proof-valued subterms. -/
theorem annotation_variant_check
    (V : AnnotationVariant (CertifiedAnnotationDomains Step Δ) n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextSubstitution Δ (proofEraseCtx Γ) (fun i => .bvar (i + n))) :
    JointCompare Step (proofEraseCtx Γ) mode a b := by
  induction V generalizing Γ e T mode with
  | refl => exact .leaf .refl
  | app VF VX ihf ihx =>
    obtain ⟨f, x, rfl, _, EF, EX⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EF W) (ihx hΓ hx EX W)
  | proj V ih =>
    obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ih hΓ hm.hasType.2 EM W)
  | lam VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    apply JointCheck.lam (ihA hΓ hA EA W)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    simpa only [proofEraseCtx, EA] using ihB hΓA hb EB (ambient_cons W hΓ hA)
  | forallE VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
    apply JointCheck.forallE (ihA hΓ hA EA W)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    simpa only [proofEraseCtx, EA] using ihB hΓA hb EB (ambient_cons W hΓ hA)
  | marked HG VB ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨v, SA, SC, HG⟩ := HG
    have SA' := W.sort SA
    have SC' := W.sort SC
    have HG' := (HG.subst W).base
    simp only [subst_shift] at SA' SC' HG'
    apply JointCheck.lamSorted SA' SC' HG'
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    simpa only [proofEraseCtx, EA] using ihB hΓA hb EB (ambient_cons W hΓ hA)

private theorem identity_context (hΓ : OnCtx Γ (env.IsType univs)) :
    ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ) (fun i => .bvar (i + 0)) := by
  change ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ) ProofShape.Subst.id
  exact ContextSubstitution.of_defeqCtx hΓ (IsDefEqCtx.zero (Γ₀ := Γ))

/-- Every independent pair of beta paths from typed annotation variants has
an inferred comparison. Paired simulation supplies related further reducts,
then only the left reduct is replayed for the structural checking theorem. -/
theorem annotation_variant_beta_check
    (V : AnnotationVariant (CertifiedAnnotationDomains Step (proofEraseCtx Γ)) 0 (proofErase Γ e) b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (RA : ProofShape.BetaRed (proofErase Γ e) p) (RB : ProofShape.BetaRed b q) :
    JointCompare Step (proofEraseCtx Γ) mode p q := by
  obtain ⟨p', q', RP, RQ, V'⟩ := V.beta_residuals
    (fun H => H.symm) (fun H R => H.beta_left R) RA RB
  obtain ⟨e', RE, EE⟩ := proofErase_beta_replay hΓ ht (RA.trans RP)
  have H := annotation_variant_check (mode := mode) V' hΓ (beta_eq hΓ ht RE).hasType.2 EE
    (identity_context hΓ)
  exact .compute (.beta RP) (.beta RQ) H

/-- Typed annotation variants retain comparison after arbitrary common ambient
substitution and subsequent independent beta paths. No domain joins or global
comparison-transport premise enter this future certificate. -/
theorem annotation_variant_future
    (V : AnnotationVariant (CertifiedAnnotationDomains Step (proofEraseCtx Γ)) 0 (proofErase Γ e) b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    BetaStableFamily (fun Δ => JointCompare Step Δ mode) (proofEraseCtx Γ) (proofErase Γ e) b := by
  refine ⟨fun RA RB => annotation_variant_beta_check V hΓ ht RA RB, ?_⟩
  intro Δ' τ p q W RA RB
  have V' := V.subst_ambient (Guard' := CertifiedAnnotationDomains Step Δ') (fun H => H.subst W)
  simp only [ProofShape.Subst.liftN] at V'
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS ht ES] at V'
  rw [← proofErase_subst_with hΓ₀ WS ht ES] at RA
  rw [← EΓ₀]
  exact annotation_variant_beta_check V' hΓ₀ (ht.subst henv WS) RA RB

end Lean4Lean.VEnv.Strengthening
