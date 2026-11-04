import Lean4Lean.Theory.Typing.Strengthening.SortTestedRecovery

/-! # Preserving selected domains under function substitution with shared test interpretations

The failure branch of native recovery retains the original selected output
through a tested recovery path. Thus a function with a selected Pi either
retains native recovery or computes to a lambda at that exact raw domain.
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

/-- Binder insertion lifts both the ordinary image and its shared test. -/
theorem SortTestedRecovery.weakenPath (H : SortTestedRecovery D Γ Γt σ e out n)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt σ σ Γ)
    (ht : env.HasType univs Γ e T) :
    SortTestedRecovery D (A :: Γ) (A.subst σ :: Γt) σ.lift e.lift (out.liftN 1) n := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hAT := hA.subst henv.orderedStrong WT hΓt
  have hΓAT : OnCtx (A.subst σ :: Γt) (env.IsType univs) := ⟨hΓt, u, hAT⟩
  have W := substEq_of_thinning hΓ (Ctx.Lift'.skip (A := A) .refl)
  have WP := substEq_of_thinning hΓt (Ctx.Lift'.skip (A := A.subst σ) .refl)
  have ES : ErasedSubstAgreement Γ (A :: Γ) (fun i => .bvar (i + 1))
      (fun i => .bvar (liftVar 1 i 0)) := by
    intro i B hl hn
    have hx : env.HasType univs Γ (.bvar i) B := .bvar hl
    have EE := proofErase_liftN hΓ hΓA Ctx.LiftN.one hx
    rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn] at EE
    simpa [VExpr.liftN, ProofShape.liftN, liftVar, Nat.add_comm] using EE
  have square : σ.comp (fun i => VExpr.bvar (i + 1)) =
      VExpr.Subst.comp (fun i => VExpr.bvar (i + 1)) σ.lift := by
    funext i
    change (σ i).subst (VExpr.Subst.shift 1) = (σ i).lift
    exact (VExpr.liftN_eq_subst (σ i) 1).symm
  have HH := H.subst_square hΓt WT hΓA W hΓAT WP ES square ht
  have ET : out.subst (fun i => .bvar (liftVar 1 i 0)) = out.liftN 1 := subst_bvar_liftN out
  simpa only [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift', ET] using HH

/-- Retained images recover exactly or carry a finite test-indexed path with
the exact assigned output. This includes lambda-valued images whose bodies
are types; no recovery of those bodies is required. -/
def TestedOrRecoveringImages
    (D : PureObservation.Definitions)
    (Γ Γ₀ Γt : List VExpr) (σ ν : VExpr.Subst) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) ∨
    ∃ n, SortTestedRecovery D Γ₀ Γt ν (σ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) n

/-- The test-indexed image condition extends under typed binders at stage
zero, preserving exact lookup outputs. -/
theorem TestedOrRecoveringImages.cons
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt ν ν Γ₀)
    (hA : env.HasType univs Γ A (.sort u))
    (H : TestedOrRecoveringImages D Γ Γ₀ Γt σ ν τ) :
    TestedOrRecoveringImages D (A :: Γ) (A.subst σ :: Γ₀)
      ((A.subst σ).subst ν :: Γt) σ.lift ν.lift τ.lift := by
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
        HR.weakenPath hΓ₀ (hA.subst henv.orderedStrong W hΓ₀) hΓt WT (W.lookup hl).hasType.1

private theorem tested_not_structure (H : SortTestedRecovery D Γ Γt ν e out n)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt ν ν Γ)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (ht : env.HasType univs Γ e (VExpr.mkApps (.const s ls) args)) : False := by
  rcases H.expose hΓt WT hΓ ht with HS | ⟨A, b, _, _, _, _, R, _⟩
  · exact HS.not_structure hi ht
  · have HE := R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht
    obtain ⟨⟨_, hA⟩, _, hb⟩ := HE.hasType.2.lam_inv henv hΓ
    have HC := (HasType.lam hA hb).uniqU henv hΓ HE.hasType.2
    obtain ⟨_, hPi⟩ := (HasType.lam hA hb).isType henv hΓ
    exact henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HC.typeChain henv hΓ hPi)

/-- Recovery at stage zero survives exactly, or its selected output is retained
by a finite test-indexed recovery. This includes all recovery constructors. -/
theorem proofErase_joint_zero_recovery_subst_testedImages
    (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) Δ source out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt ν ν Γ₀)
    (ht : env.HasType univs Γ e T) (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HI : TestedOrRecoveringImages D Γ Γ₀ Γt σ ν τ) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀) (source.subst τ) (out.subst τ) ∨
      ∃ n, SortTestedRecovery D Γ₀ Γt ν (e.subst σ) (out.subst τ) n := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (erased_joint_zero_certificate_descent hs)
  induction R generalizing Γ Γ₀ Γt σ ν τ e T with
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
    have hA₀ := hA.subst henv.orderedStrong W hΓ₀
    have hΓAt : OnCtx ((A.subst σ).subst ν :: Γt) (env.IsType univs) :=
      ⟨hΓt, u, hA₀.subst henv.orderedStrong WT hΓt⟩
    rcases ih hΓA W' ES' hΓAt (WT.lift henv.ordered hA₀) hb (by simp only [proofEraseCtx, EA, EΓ]) Eb
        (HI.cons hΓ₀ W ES hΓt WT hA) with R | ⟨n, H⟩
    · apply Or.inl
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, EA, ProofShape.subst] using
        ScopedTypeRecovery.lam R
    · apply Or.inr
      refine ⟨n + 1, ?_⟩
      simpa only [VExpr.subst, ProofShape.subst, proofErase_subst_with hΓ₀ W hA ES, EA] using
        SortTestedRecovery.lam H
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    rcases ih hΓ₀ W ES hΓt WT hf EΓ Ef HI with R | ⟨n, H⟩
    · apply Or.inl
      rw [ProofShape.subst_inst]
      exact .app R
    · apply Or.inr
      refine ⟨n + 1, ?_⟩
      simpa only [VExpr.subst, ProofShape.subst_inst, proofErase_subst_with hΓ₀ W ha ES, Ea] using
        SortTestedRecovery.app (a := a.subst σ) H
  | @forallE Δ A u B v RA RB =>
    have HR : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) (.sort (.imax u v)) := by
      simpa only [EΓ, Ee] using ScopedTypeRecovery.forallE RA RB
    obtain ⟨T', heT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht HR
    obtain rfl := erase_sort_inv ET
    exact .inr ⟨0, .atom ((heT.subst henv.orderedStrong W hΓ₀).subst henv.orderedStrong WT hΓt)⟩
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, hjInfo, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    rcases ih hΓ₀ W ES hΓt WT hm.hasType.2 EΓ Em HI with R | ⟨n, H⟩
    · apply Or.inl
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at R
      rw [projectionType_subst HT hj (by omega)]
      exact .proj hi HT hj (by simpa only [List.length_map] using hlen) R
    · exact (tested_not_structure H hΓt WT hΓ₀ hjInfo (by
        simpa only [VExpr.subst_mkApps, VExpr.subst] using
          hm.hasType.2.subst henv.orderedStrong W hΓ₀)).elim
  | convert R RC ih =>
    have RC' := (forget_scope RC).subst (σ := τ) (fun H => erased_iota_primitive_subst H)
    rcases ih hΓ₀ W ES hΓt WT ht EΓ Ee HI with R' | ⟨n, H⟩
    · exact .inl (.convert R' (RC'.scoped (fun H => .base H)))
    · exact .inr ⟨n + 1, .convert H RC'⟩

/-- A retained function with a selected Pi either retains exact native
recovery or computes to a lambda with that exact substituted domain. The
second branch needs no semantic conversion of the argument guard. -/
theorem proofErase_joint_zero_function_subst_tested_domain
    (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hΓt : OnCtx Γt (env.IsType univs)) (WT : Ctx.SubstEq env univs Γt ν ν Γ₀)
    (hf : env.HasType univs Γ f (.forallE C E)) (hn : ¬ IsProof Γ f)
    (HI : TestedOrRecoveringImages D Γ Γ₀ Γt σ ν τ)
    (R : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B)) :
    ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (f.subst σ)) (.forallE (A.subst τ) (B.subst τ.lift)) ∨
    ∃ body, ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (f.subst σ)) (.lam (A.subst τ) body) := by
  rcases proofErase_joint_zero_recovery_subst_testedImages hs R hΓ₀ W ES hΓt WT hf rfl rfl HI with
    HR | ⟨n, H⟩
  · exact .inl (by rwa [proofErase_subst_with hΓ₀ W hf ES])
  · exact .inr (H.selected_domain hΓt WT hΓ₀ (hf.subst henv.orderedStrong W hΓ₀)
      (mt (isProof_subst hΓ₀ W hf).1 hn))



end Lean4Lean.VEnv.Strengthening
