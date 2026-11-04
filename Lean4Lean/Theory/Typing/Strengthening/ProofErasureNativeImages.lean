import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport

/-! # Exactly recoverable images for any renaming-stable computation

The image condition is explicit and extends under typed binders. Recovery
transport uses only forward source replay and typed computation transport;
no confluence or backward recovery of a selected type is needed.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeImageTransport
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]
variable {ImageStep : List ProofShape → ProofShape → ProofShape → Prop}

/-- Every retained variable image recovers its exact substituted oracle type
using the image relation. Proof images and absent variables are excluded. -/
def Images (ImageStep : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ Γ₀ : List VExpr) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery ImageStep (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ)

/-- Exact image recovery extends under a binder in the same image relation. -/
theorem Images.cons (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort u)) (H : Images ImageStep Γ Γ₀ τ) :
    Images ImageStep (A :: Γ) (A.subst σ :: Γ₀) τ.lift := by
  intro i T hl hn
  cases hl with
  | zero =>
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
      contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using
      (ScopedTypeRecovery.bvar (Step := ImageStep)
        (Δ := proofEraseCtx (A.subst σ :: Γ₀)) (i := 0))
  | @succ _ i T _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) :=
      fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    have RL := (H hl hn₀).rename hrename
      (ContextRenaming.of_liftN hΓ₀ hΓA Ctx.LiftN.one)
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
      subst_bvar_liftN, contextOracle, TypeOracle.cons,
      ProofShape.lift_subst_lift, ProofShape.Subst.lift] using RL

/-- One exactly recoverable argument gives the required images for instantiation. -/
theorem Images.inst
    (H : ScopedTypeRecovery ImageStep (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ T)) :
    Images ImageStep (T :: Γ) Γ (ProofShape.Subst.one (proofErase Γ p)) := by
  intro i A hl _
  cases hl with
  | zero =>
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.Subst.cons] using H
  | succ hl =>
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact .bvar

/-- An interpreted substitution with exactly recovering images for the image relation in each
typed realization of its source erasure. -/
def ImageSubstitution (ImageStep : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ₀ σ, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ' ∧
      Ctx.SubstEq env univs Γ₀ σ σ Γ ∧ ErasedSubstAgreement Γ Γ₀ σ τ ∧
      Images ImageStep Γ Γ₀ τ

/-- Forgetting image information gives ordinary interpreted substitution. -/
theorem ImageSubstitution.interpretation (W : ImageSubstitution ImageStep Δ Δ' τ) :
    ContextSubstitution Δ Δ' τ := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, _⟩ := W hΓ EΓ
  exact ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩

/-- The exact image condition extends through arbitrary typed binder realizations. -/
theorem ImageSubstitution.cons (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ)) (W : ImageSubstitution ImageStep Δ Δ' τ) :
    ImageSubstitution ImageStep (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ EΓ
    have hB' := hB.subst henv.orderedStrong WS hΓ₀
    refine ⟨B.subst σ :: Γ₀, σ.lift, ⟨hΓ₀, u, hB'⟩, ?_, WS.lift henv.ordered hB,
      ES.lift hΓ₀ WS hB, HI.cons hrename hΓ₀ WS ES hB⟩
    simp only [proofEraseCtx, proofErase_subst_with hΓ₀ WS hB ES, EB, EΓ₀]

/-- One actual source context suffices to certify the interpreted image
condition. Equal-erasure source realizations convert to that context. -/
theorem ImageSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images ImageStep Γ Γ₀ τ) :
    ImageSubstitution ImageStep (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  intro Γ' hΓ' EΓ
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  refine ⟨Γ₀, σ, hΓ₀, rfl, substEq_source_convert hΓ₀ HC W, ES.source_convert HC, ?_⟩
  intro i A hl hn
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  simpa only [EΓ] using HI hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))


end Lean4Lean.VEnv.Strengthening.NativeImageTransport
