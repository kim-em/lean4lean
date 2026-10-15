import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetainedRenaming

/-! # Typed substitutions with exactly recoverable non-proof images

Retained variables may be replaced by arbitrary expressions when their images
recover the substituted oracle types. This is an explicit premise, not recovery
completeness. It extends beneath typed binders using primitive renaming.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]
namespace ProofShape

/-- A typed context substitution whose retained images recover their exact
substituted declared types. Proof variables impose no image-recovery premise. -/
structure RecoveringSubstitution
    (Image : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ Δ' : List ProofShape) (τ : Subst) : Prop where
  interpretation : ContextSubstitution Δ Δ' τ
  lookup : ∀ {Γ i A}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery Image Δ' (τ i) ((contextOracle Δ i).subst τ)

/-- Retained renaming supplies recoverable images in any primitive relation. -/
theorem RetainedRenaming.recovering (W : RetainedRenaming Δ Δ' τ) :
    RecoveringSubstitution Image Δ Δ' τ := by
  refine ⟨W.interpretation, ?_⟩
  intro Γ i A hΓ EΓ hl hn
  obtain ⟨j, Ej, ET⟩ := W.lookup hΓ EΓ hl hn
  rw [Ej, ← ET]
  exact .bvar

/-- Enlarging the image computation relation preserves the exact-image premise. -/
theorem RecoveringSubstitution.mono
    (hinc : ∀ {Δ a b}, Image Δ a b → Image' Δ a b)
    (W : RecoveringSubstitution Image Δ Δ' τ) : RecoveringSubstitution Image' Δ Δ' τ :=
  ⟨W.interpretation, fun hΓ EΓ hl hn => (W.lookup hΓ EΓ hl hn).mono hinc⟩

/-- Exact recoverable images extend beneath every displayed domain. An actual
source realization supplies the substituted binder typing needed to weaken
older image recoveries; no inhabitant of that binder is used. -/
theorem RecoveringSubstitution.cons
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ContextRenaming Δ Δ' τ →
      Image Δ' (a.subst τ) (b.subst τ))
    (W : RecoveringSubstitution Image Δ Δ' τ) :
    RecoveringSubstitution Image (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  refine ⟨ContextSubstitution.cons W.interpretation, ?_⟩
  intro Γ i T hΓ EΓ hl hn
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    cases hl with
    | zero =>
      simpa only [contextOracle, TypeOracle.cons, lift_subst_lift, Subst.lift] using
        (ScopedTypeRecovery.bvar (Step := Image) (Δ := A.subst τ :: Δ') (i := 0))
    | @succ _ i T _ hl =>
      have hn₀ : ¬ IsProof Γ (.bvar i) :=
        fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
      have R := W.lookup hΓ.1 EΓ hl hn₀
      obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W.interpretation hΓ.1 EΓ
      obtain ⟨_, u, hB⟩ := hΓ
      have hΓB : OnCtx (B.subst σ :: Γ₀) (env.IsType univs) :=
        ⟨hΓ₀, u, hB.subst henv.orderedStrong WS hΓ₀⟩
      have Wlift := ContextRenaming.of_liftN hΓ₀ hΓB Ctx.LiftN.one
      have EB' : proofErase Γ₀ (B.subst σ) = A.subst τ := by
        rw [proofErase_subst_with hΓ₀ WS hB ES, EB]
      rw [proofEraseCtx, EB', EΓ₀] at Wlift
      have RL := R.rename hrename Wlift
      simpa only [subst_bvar_liftN, contextOracle, TypeOracle.cons, lift_subst_lift,
        Subst.lift] using RL

/-- Domain-sort witnesses use the underlying interpreted substitution. -/
theorem RecoveringSubstitution.sort (W : RecoveringSubstitution Image Δ Δ' τ)
    (S : DomainSort Δ A u) : DomainSort Δ' (A.subst τ) u :=
  ContextSubstitution.sort W.interpretation S

/-- The exact image premise need only be checked in one typed source context.
Other realizations with the same erasure convert to that source context. -/
theorem RecoveringSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (H : ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
      ScopedTypeRecovery Image (proofEraseCtx Γ₀) (τ i)
        ((contextOracle (proofEraseCtx Γ) i).subst τ)) :
    RecoveringSubstitution Image (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  refine ⟨ContextSubstitution.of_typed hΓ₀ W E, ?_⟩
  intro Γ' i A hΓ' EΓ hl hn
  have HC := proofEraseCtx_defeq W.wf hΓ' EΓ.symm
  have hx := (show env.HasType univs Γ' (.bvar i) A from .bvar hl).defeqDFC henv (HC.symm henv.ordered)
  obtain ⟨B, hl₀⟩ := hx.bvar_inv henv W.wf
  exact H hl₀ (fun hp => hn ((isProof_defeqCtx HC).1 hp))

/-- A typed single substitution is recoverable when its non-proof image has
an exact recovery at the assigned type. Proof images need no recovery. -/
theorem RecoveringSubstitution.inst
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (HR : ¬ IsProof Γ e → ScopedTypeRecovery Image (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ T)) :
    RecoveringSubstitution Image (proofEraseCtx (T :: Γ)) (proofEraseCtx Γ)
      (Subst.one (proofErase Γ e)) := by
  obtain ⟨u, hT⟩ := he.isType henv hΓ
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := e) (A₀ := T)).substEq hΓT he
  have E : ErasedSubstAgreement (T :: Γ) Γ (VExpr.Subst.one e)
      (Subst.one (proofErase Γ e)) := erasedSubstAgreement_one hΓT he
  apply RecoveringSubstitution.of_typed hΓ W E
  intro i A hl hn
  cases hl with
  | zero =>
    have hne : ¬ IsProof Γ e := by
      intro hp
      exact hn ((isProof_subst hΓ W (HasType.bvar Lookup.zero)).1 hp)
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, Subst.one, lift_subst_cons, subst_id]
    exact HR hne
  | @succ _ i A _ hl =>
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, Subst.one, lift_subst_cons, subst_id]
    exact .bvar

/-- Source-typed primitive simulation under exact recoverable images. The
image recovery relation may be weaker than the target computation relation. -/
def RecoveringPrimitiveTransport
    (Image Step Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Δ Δ' τ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
    proofEraseCtx Γ = Δ → RecoveringSubstitution Image Δ Δ' τ →
    Step Δ (proofErase Γ e) out → ScopedCompute Target Δ' ((proofErase Γ e).subst τ) (out.subst τ)

/-- Typed compatible paths transport using primitive simulation only at
realized sources; forward replay supplies all intermediate source typings. -/
theorem ScopedCompute.subst_recovering
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ContextRenaming Δ Δ' τ → Image Δ' (a.subst τ) (b.subst τ))
    (htrans : RecoveringPrimitiveTransport Image Step Target)
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : RecoveringSubstitution Image Δ Δ' τ) : ScopedCompute Target Δ' (source.subst τ) (out.subst τ) := by
  induction R generalizing Γ e T Δ' τ with
  | base H =>
    subst Ee
    exact htrans hΓ ht EΓ W H
  | beta H => exact .beta H.subst
  | trans R₁ _ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R₁
    exact .trans (ih₁ hΓ ht EΓ Ee W) (ih₂ hΓ HE.hasType.2 EΓ EE W)
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EΓ Ef W) (iha hΓ ha EΓ Ea W)
  | proj _ ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2 EΓ Em W)
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA hΓ hA EΓ EA W)
      (ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb (by simp only [proofEraseCtx, EA, EΓ]) Eb (W.cons hrename))
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ihA hΓ hA EΓ EA W)
      (ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB (by simp only [proofEraseCtx, EA, EΓ]) EB (W.cons hrename))

/-- Exact selected recovery transports when every retained image recovers its
assigned type. No recovery of erased proof markers is required. -/
theorem ScopedTypeRecovery.subst_recovering
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ContextRenaming Δ Δ' τ → Image Δ' (a.subst τ) (b.subst τ))
    (hinc : ∀ {Δ a b}, Image Δ a b → Target Δ a b)
    (htrans : RecoveringPrimitiveTransport Image Step Target)
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : RecoveringSubstitution Image Δ Δ' τ) : ScopedTypeRecovery Target Δ' (source.subst τ) (out.subst τ) := by
  induction R generalizing Γ e T Δ' τ with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv hΓ
    have hn : ¬ IsProof Γ (.bvar i) := by intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    exact (W.lookup hΓ EΓ hl hn).mono hinc
  | sort hu => exact .sort hu
  | const hc hw hn =>
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ih (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb (by simp only [proofEraseCtx, EA, EΓ]) Eb (W.cons hrename))
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    rw [subst_inst]
    exact .app (ih hΓ hf EΓ Ef W)
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ihA hΓ hA EΓ EA W)
      (ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB (by simp only [proofEraseCtx, EA, EΓ]) EB (W.cons hrename))
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    have HR' := ih hΓ hm.hasType.2 EΓ Em W
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at HR'
    rw [projectionType_subst HT hj (by omega)]
    exact .proj hi HT hj (by simpa only [List.length_map] using hlen) HR'
  | convert R RC ih =>
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    exact .convert (ih hΓ ht EΓ Ee W) (RC.subst_recovering hstep hrename htrans hΓ hA EΓ EA W)

end ProofShape
end Lean4Lean.VEnv.Strengthening
