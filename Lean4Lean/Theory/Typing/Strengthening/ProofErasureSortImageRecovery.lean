import Lean4Lean.Theory.Typing.Strengthening.SortRootedHeadExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveringSubstitution

/-! # Recovery after substitution of arbitrary types

Retained images may either recover their assigned type or be sort-typed.
Recovery then survives exactly, or the substituted expression has a finite
sort-rooted path. At a function type the latter alternative exposes a lambda
by beta. This does not align that lambda's annotation with the originally
selected recovered domain, or transport an arbitrary carrier guard between
those annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- A retained image either has exact native recovery or is an actual type.
The second alternative requires no recovery or normalization of the image. -/
def SortOrRecoveringImages
    (Target : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ Γ₀ : List VExpr) (σ : VExpr.Subst) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery Target (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) ∨ env.IsType univs Γ₀ (σ i)

/-- The image condition extends under typed binders. Old type images weaken;
old recoveries rename; the fresh variable has ordinary lookup recovery. -/
theorem SortOrRecoveringImages.cons
    (hrename : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort u))
    (H : SortOrRecoveringImages Target Γ Γ₀ σ τ) :
    SortOrRecoveringImages Target (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift := by
  intro i T hl hn
  cases hl with
  | zero =>
    apply Or.inl
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
      contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using
      (ScopedTypeRecovery.bvar (Step := Target)
        (Δ := proofEraseCtx (A.subst σ :: Γ₀)) (i := 0))
  | @succ _ i T _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) :=
      fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    rcases H hl hn₀ with R | ⟨v, hv⟩
    · apply Or.inl
      have RL := R.rename hrename (ContextRenaming.of_liftN hΓ₀ hΓA Ctx.LiftN.one)
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
        subst_bvar_liftN, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift] using RL
    · exact .inr ⟨v, hv.weak henv⟩

/-- Native recovery survives exactly unless its failure is confined to a
finite path ending in a type image. This covers every recovery constructor,
including conversion and projection, using typed primitive substitution. -/
theorem proofErase_recovery_subst_or_sortRooted
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hrename : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T) (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HI : SortOrRecoveringImages Target Γ Γ₀ σ τ) :
    ScopedTypeRecovery Target (proofEraseCtx Γ₀) (source.subst τ) (out.subst τ) ∨
      ∃ n, SortRooted Γ₀ (e.subst σ) n := by
  induction R generalizing Γ Γ₀ σ τ e T with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv W.wf
    have hn : ¬ IsProof Γ (.bvar i) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    rcases HI hl hn with R | ⟨u, hu⟩
    · exact .inl (EΓ ▸ R)
    · exact .inr ⟨0, .type hu⟩
  | sort hu => exact .inl (.sort hu)
  | const hc hw hn =>
    apply Or.inl
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    have W' := W.lift henv.ordered hA
    have ES' : ErasedSubstAgreement (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift :=
      ES.lift hΓ₀ W hA
    rcases ih hΓA W' ES' hb (by simp only [proofEraseCtx, EA, EΓ]) Eb
        (HI.cons hrename hΓ₀ W ES hA) with R | ⟨n, H⟩
    · apply Or.inl
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, EA, ProofShape.subst] using
        ScopedTypeRecovery.lam R
    · exact .inr ⟨n + 1, .lam H⟩
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv W.wf
    rcases ih hΓ₀ W ES hf EΓ Ef HI with R | ⟨n, H⟩
    · apply Or.inl
      rw [ProofShape.subst_inst]
      exact .app R
    · exact .inr ⟨n + 1, .app H⟩
  | forallE =>
    obtain ⟨A, B, rfl, _, _, _⟩ := erase_forallE_inv Ee
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .inr ⟨0, .type ((HasType.forallE hA hB).subst henv.orderedStrong W hΓ₀)⟩
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    rcases ih hΓ₀ W ES hm.hasType.2 EΓ Em HI with R | ⟨n, H⟩
    · apply Or.inl
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at R
      rw [projectionType_subst HT hj (by omega)]
      exact .proj hi HT hj (by simpa only [List.length_map] using hlen) R
    · exact .inr ⟨n + 1, .proj H⟩
  | convert R RC ih =>
    rcases ih hΓ₀ W ES ht EΓ Ee HI with R' | H
    · obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht
        (by simpa only [EΓ, Ee] using R)
      obtain ⟨_, hA⟩ := heA.isType henv W.wf
      exact .inl (.convert R' (RC.subst_typed hstep hsubst W.wf hA EΓ EA
        (by rw [← EΓ]; exact ContextSubstitution.of_typed hΓ₀ W ES)))
    · exact .inr H

/-- A function with a source recovery retains that exact recovery after
substitution, or beta-exposes a lambda. The latter domain is not asserted to
equal the selected substituted domain syntactically. -/
theorem proofErase_function_recovery_subst_or_lambda
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hrename : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hf : env.HasType univs Γ f (.forallE A B))
    (HI : SortOrRecoveringImages Target Γ Γ₀ σ τ)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) out) :
    ScopedTypeRecovery Target (proofEraseCtx Γ₀) (proofErase Γ₀ (f.subst σ)) (out.subst τ) ∨
      ∃ C b, VExpr.BetaRed (f.subst σ) (.lam C b) := by
  rcases proofErase_recovery_subst_or_sortRooted hstep hsubst hrename R hΓ₀ W ES hf rfl rfl HI with
    HR | ⟨n, H⟩
  · exact .inl (by rwa [proofErase_subst_with hΓ₀ W hf ES])
  · obtain ⟨C, b, _, _, _, RB⟩ := H.function_expose hΓ₀ (hf.subst henv.orderedStrong W hΓ₀)
    exact .inr ⟨C, b, RB⟩

/-- Substituting an arbitrary type meets the image condition: only the
replaced variable uses its sort typing; retained variables recover by lookup. -/
theorem SortOrRecoveringImages.inst_type
    (hp : env.HasType univs Γ p (.sort u)) :
    SortOrRecoveringImages Target (.sort u :: Γ) Γ
      (VExpr.Subst.one p) (ProofShape.Subst.one (proofErase Γ p)) := by
  intro i A hl _
  cases hl with
  | zero => exact .inr ⟨u, hp⟩
  | succ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact .bvar

/-- At stage zero, substitution of any type (in particular any proposition)
into a natively recovered function either preserves its exact selected output
or exposes a lambda by beta. Primitive transport is proved from core raw
substitution; no beta-stability, resynthesis or image-recovery premise remains.
This does not yet transport a carrier guard to the exposed annotation. -/
theorem proofErase_joint_zero_function_inst_type_recovery_or_lambda
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.sort u))
    (hf : env.HasType univs (.sort u :: Γ) f (.forallE A B))
    (R : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx (.sort u :: Γ))
      (proofErase (.sort u :: Γ) f) out) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (f.inst p)) (out.inst (proofErase Γ p)) ∨
      ∃ C b, VExpr.BetaRed (f.inst p) (.lam C b) := by
  have hU : env.HasType univs Γ (.sort u) (.sort (.succ u)) :=
    .sort (hp.isType henv hΓ |>.choose_spec.sort_inv henv)
  have hΓU : OnCtx (.sort u :: Γ) (env.IsType univs) := ⟨hΓ, _, hU⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := .sort u)).substEq hΓU hp
  have ES : ErasedSubstAgreement (.sort u :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓU hp
  have HS : ErasedPrimitiveSubstitutionTo (ErasedJointStage D 0) (ErasedJointStage D 0) := by
    intro Γ Γ₀ σ τ e T out hΓ₀ W ES ht H
    rw [proofErase_subst_with hΓ₀ W ht ES]
    exact .base (erased_iota_primitive_subst H)
  have HH := proofErase_function_recovery_subst_or_lambda
    (ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)) HS
    (fun H _ => erased_iota_primitive_subst H) hΓ W ES hf
    (SortOrRecoveringImages.inst_type hp) R
  simpa only [VExpr.inst_eq, ProofShape.inst_eq_subst, ProofShape.Subst.liftN, VExpr.Subst.liftN] using HH

end Lean4Lean.VEnv.Strengthening
