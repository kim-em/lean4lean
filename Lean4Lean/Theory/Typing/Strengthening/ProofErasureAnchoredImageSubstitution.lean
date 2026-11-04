import Lean4Lean.Theory.Typing.Strengthening.AnchoredFamilyRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePathImageSubstitution

/-! # Preserving selected domains under protected-family function substitution

The failure branch of native recovery retains the original selected output
through a protected-family recovery path. Thus a function with a selected Pi either
retains native recovery, computes to a lambda at the selected domain, or
proves that the selected domain is inert.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private forget_scope from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
variable [Params]

/-- Binder insertion preserves a selected protected-family recovery path. -/
theorem AnchoredFamilyRecovery.weakenPath (H : AnchoredFamilyRecovery D cut Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (ht : env.HasType univs Γ e T) :
    AnchoredFamilyRecovery D (cut + 1) (A :: Γ) (e.liftN 1) (out.liftN 1) n := by
  have W := substEq_of_thinning hΓ (Ctx.Lift'.skip (A := A) .refl)
  have ES : ErasedSubstAgreement Γ (A :: Γ) (fun i => .bvar (i + 1))
      (fun i => .bvar (liftVar 1 i 0)) := by
    intro i B hl hn
    have hx : env.HasType univs Γ (.bvar i) B := .bvar hl
    have EE := proofErase_liftN hΓ hΓA Ctx.LiftN.one hx
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn] at EE
    simpa [VExpr.liftN, ProofShape.liftN, liftVar, Nat.add_comm] using EE
  have WH : PreservesCarrierHeads cut (cut + 1) (fun i => .bvar (liftVar 1 i 0)) := by
    intro i hi
    exact ⟨1 + i, by omega, by simp [liftVar]⟩
  have HH := H.subst hΓA W ES ht WH
  have ET : out.subst (fun i => .bvar (liftVar 1 i 0)) = out.liftN 1 :=
    subst_bvar_liftN out
  simpa only [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift',
    ET] using HH

/-- Retained images recover exactly or carry a finite protected-family path with
the exact assigned output. This includes lambda-valued images whose bodies
are types; no recovery of those bodies is required. -/
def AnchoredOrRecoveringImages
    (D : PureObservation.Definitions) (cut : Nat)
    (Γ Γ₀ : List VExpr) (σ : VExpr.Subst) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) ∨
    ∃ n, AnchoredFamilyRecovery D cut Γ₀ (σ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) n

/-- The protected-family image condition extends under typed binders at stage
zero, preserving exact lookup outputs. -/
theorem AnchoredOrRecoveringImages.cons
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort u))
    (H : AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ) :
    AnchoredOrRecoveringImages D (cut + 1) (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift := by
  intro i T hl hn
  cases hl with
  | zero =>
    apply Or.inl
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
      contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using
      (ScopedTypeRecovery.bvar (Step := ErasedJointStage D 0)
        (Δ := proofEraseCtx (A.subst σ :: Γ₀)) (i := 0))
  | @succ _ i T _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) :=
      fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    rcases H hl hn₀ with R | ⟨n, HR⟩
    · apply Or.inl
      have RL := R.rename (Step' := ErasedJointStage D 0) (fun H _ => erased_iota_primitive_subst H) (ContextRenaming.of_liftN hΓ₀ hΓA Ctx.LiftN.one)
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
        subst_bvar_liftN, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift] using RL
    · refine .inr ⟨n, ?_⟩
      simpa only [proofEraseCtx, contextOracle, TypeOracle.cons,
        ProofShape.lift_subst_lift, ProofShape.Subst.lift, VExpr.Subst.lift] using
        HR.weakenPath hΓ₀ hΓA (W.lookup hl).hasType.1

/-- The previous finite protected-family image condition embeds at any cutoff. -/
theorem PathOrRecoveringImages.anchored
    (H : PathOrRecoveringImages D Γ Γ₀ σ τ) :
    AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ := by
  intro i A hl hn
  rcases H hl hn with R | ⟨n, HR⟩
  · exact .inl R
  · exact .inr ⟨n, HR.anchored⟩

/-- Single substitution of a protected-family value satisfies the enlarged image
condition at its exact assigned erasure. -/
theorem AnchoredOrRecoveringImages.inst
    (H : AnchoredFamilyRecovery D cut Γ p (proofErase Γ T) n) :
    AnchoredOrRecoveringImages D cut (T :: Γ) Γ
      (VExpr.Subst.one p) (ProofShape.Subst.one (proofErase Γ p)) := by
  intro i A hl _
  cases hl with
  | zero =>
    apply Or.inr
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id, VExpr.Subst.one, VExpr.Subst.cons] using Exists.intro n H
  | succ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact .bvar

private theorem rooted_not_structure (H : AnchoredFamilyRecovery D cut Γ e out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (ht : env.HasType univs Γ e (VExpr.mkApps (.const s ls) args))
    (Hout : ¬ AnchoredCarrier cut out) : False := by
  rcases H.expose hΓ ht with ⟨u, hu⟩ | HN | ⟨A, u, hf, _, _⟩ | ⟨A, b, _, _, _, _, R, _⟩
  · have HE := hu.uniqU henv hΓ ht
    exact henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ (HasType.sort (hu.isType henv hΓ |>.choose_spec.sort_inv henv)))
  · exact Hout HN
  · have HE := hf.uniqU henv hΓ ht
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    exact henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HE.typeChain henv hΓ hPi)
  · have HE := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht
    obtain ⟨⟨_, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
    have HC := (HasType.lam hA hb).uniqU henv hΓ HE.hasType.2
    obtain ⟨_, hPi⟩ := (HasType.lam hA hb).isType henv hΓ
    exact henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HC.typeChain henv hΓ hPi)

/-- Recovery at stage zero survives exactly, or its selected output is retained
by a finite protected-family recovery. This includes all recovery constructors. -/
theorem proofErase_joint_zero_recovery_subst_anchoredImages
    (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) Δ source out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T) (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HI : AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀) (source.subst τ) (out.subst τ) ∨
      ∃ n, AnchoredFamilyRecovery D cut Γ₀ (e.subst σ) (out.subst τ) n := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)
  induction R generalizing Γ Γ₀ σ τ e T cut with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv W.wf
    have hn : ¬ IsProof Γ (.bvar i) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    rcases HI hl hn with R | ⟨n, HR⟩
    · exact .inl (EΓ ▸ R)
    · exact .inr ⟨n, EΓ ▸ HR⟩
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
        (HI.cons hΓ₀ W ES hA) with R | ⟨n, H⟩
    · apply Or.inl
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, EA, ProofShape.subst] using
        ScopedTypeRecovery.lam R
    · apply Or.inr
      refine ⟨n + 1, ?_⟩
      simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ₀ W hA ES, EA] using
        AnchoredFamilyRecovery.lam H
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    rcases ih hΓ₀ W ES hf EΓ Ef HI with R | ⟨n, H⟩
    · apply Or.inl
      rw [ProofShape.subst_inst]
      exact .app R
    · apply Or.inr
      refine ⟨n + 1, ?_⟩
      simpa only [VExpr.subst, ProofShape.subst_inst, proofErase_subst_with hΓ₀ W ha ES, Ea] using
        AnchoredFamilyRecovery.app (a := a.subst σ) H
  | @forallE Δ A u B v RA RB =>
    have HR : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) (.sort (.imax u v)) := by
      simpa only [EΓ, Ee] using ScopedTypeRecovery.forallE RA RB
    obtain ⟨T', heT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht HR
    obtain rfl := erase_sort_inv ET
    exact .inr ⟨0, .type (heT.subst henv.orderedStrong W hΓ₀)⟩
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, hjInfo, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    rcases ih hΓ₀ W ES hm.hasType.2 EΓ Em HI with R | ⟨n, H⟩
    · apply Or.inl
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at R
      rw [projectionType_subst HT hj (by omega)]
      exact .proj hi HT hj (by simpa only [List.length_map] using hlen) R
    · exact (rooted_not_structure H hΓ₀ hjInfo (by
        simpa only [VExpr.subst_mkApps, VExpr.subst] using
          hm.hasType.2.subst henv.orderedStrong W hΓ₀) (by
          rintro ⟨i, args, _, HE⟩
          have HC := congrArg ProofShape.constHead HE
          simp only [ProofShape.subst_mkApps, ProofShape.subst,
            ProofShape.constHead_mkApps, ProofShape.constHead] at HC
          cases HC)).elim
  | convert R RC ih =>
    have RC' := (forget_scope RC).subst (σ := τ) (fun H => erased_iota_primitive_subst H)
    rcases ih hΓ₀ W ES ht EΓ Ee HI with R' | ⟨n, H⟩
    · exact .inl (.convert R' (RC'.scoped (fun H => .base H)))
    · exact .inr ⟨n + 1, .convert H RC'⟩

/-- A retained function with selected Pi either retains native recovery,
computes to a lambda at the exact selected domain, or has an inert selected
domain. These are the three cases of recursive checker transport. -/
theorem proofErase_joint_zero_function_subst_anchored_domain
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hf : env.HasType univs Γ f (.forallE C E)) (hn : ¬ IsProof Γ f)
    (HI : AnchoredOrRecoveringImages D cut Γ Γ₀ σ τ)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B)) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (f.subst σ)) (.forallE (A.subst τ) (B.subst τ.lift)) ∨
    (∃ body, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (f.subst σ)) (.lam (A.subst τ) body)) ∨
    (∀ {out}, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ₀) (A.subst τ) out →
      ¬ CarrierExposure out) := by
  rcases proofErase_joint_zero_recovery_subst_anchoredImages hs R hΓ₀ W ES hf rfl rfl HI with
    HR | ⟨n, H⟩
  · exact .inl (by rwa [proofErase_subst_with hΓ₀ W hf ES])
  · exact .inr (H.selected_domain_or_inert hΓ₀ (hf.subst henv.orderedStrong W hΓ₀)
      (mt (isProof_subst hΓ₀ W hf).1 hn))


end Lean4Lean.VEnv.Strengthening
