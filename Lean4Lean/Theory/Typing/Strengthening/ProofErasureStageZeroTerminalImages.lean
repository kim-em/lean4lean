import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageZeroTerminalPath

/-! # Native recovery after substitution of terminal images at the expansion base

A retained image may recover its assigned type exactly or be terminal. Failure
of exact recovery is recorded by a typed terminal path, which still exposes the
selected domain when the recovered term is used as a function.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Each retained image either recovers the exact substituted lookup type or
has terminal typing. Terminal images need no recovery at their assigned type. -/
def StageZeroTerminalImages (D : PureObservation.Definitions)
    (Γ Γ₀ : List VExpr) (σ : VExpr.Subst) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ) ∨ TerminalImage Γ₀ (σ i)

/-- The image condition extends under arbitrary typed binders. -/
theorem StageZeroTerminalImages.cons
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (hA : env.HasType univs Γ A (.sort u))
    (H : StageZeroTerminalImages D Γ Γ₀ σ τ) :
    StageZeroTerminalImages D (A :: Γ) (A.subst σ :: Γ₀) σ.lift τ.lift := by
  intro i T hl hn
  cases hl with
  | zero =>
    apply Or.inl
    simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES,
      contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using
      (ScopedTypeRecovery.bvar (Step := ErasedStaticStructureEtaExpansionStage D 0)
        (Δ := proofEraseCtx (A.subst σ :: Γ₀)) (i := 0))
  | @succ _ i T _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) := fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
      ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
    rcases H hl hn₀ with R | HT
    · apply Or.inl
      have RL := R.rename (erased_static_structure_eta_expansion_stage_rename heq hs 0)
        (ContextRenaming.of_liftN hΓ₀ hΓA Ctx.LiftN.one)
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, subst_bvar_liftN,
        contextOracle, TypeOracle.cons, ProofShape.lift_subst_lift, ProofShape.Subst.lift] using RL
    · have HW := substEq_of_thinning hΓ₀ (Ctx.Lift'.skip (A := A.subst σ) .refl)
      have HH := HT.subst hΓA HW
      apply Or.inr
      simpa only [← VExpr.lift'_subst, VExpr.subst_id, ← VExpr.lift_eq_lift', VExpr.Subst.lift] using HH

/-- Every native constructor retains exact recovery or an actual typed
terminal path at the exact substituted output. This includes conversion through
constant expansions and excludes retained projections of terminal paths. -/
theorem stage_zero_recovery_subst_terminal_images
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ source out)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T) (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (HI : StageZeroTerminalImages D Γ Γ₀ σ τ) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ₀)
      (source.subst τ) (out.subst τ) ∨
    ∃ T' n, StageZeroTerminalPath D Γ₀ (e.subst σ) T' n ∧ proofErase Γ₀ T' = out.subst τ := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  induction R generalizing Γ Γ₀ σ τ e T with
  | bvar =>
    rename_i Δ i
    obtain rfl := erase_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv W.wf
    have hn : ¬ IsProof Γ (.bvar i) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    rcases HI hl hn with RN | HT
    · exact .inl (EΓ ▸ RN)
    · refine .inr ⟨A.subst σ, 0, .terminal HT (W.lookup hl).hasType.1, ?_⟩
      rw [proofErase_subst_with hΓ₀ W ((HasType.bvar hl).isType henv W.wf |>.choose_spec) ES]
      rw [← EΓ, proofEraseCtx_oracle, erasedTypeOracle_valid W.wf hl]
  | sort hu => exact .inl (.sort hu)
  | const hc hw hn =>
    apply Or.inl
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv W.wf
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hA'⟩
    rcases ih hΓA (W.lift henv.ordered hA) (ES.lift hΓ₀ W hA) hb
      (by simp only [proofEraseCtx, EA, EΓ]) Eb (HI.cons heq hs hΓ₀ W ES hA) with RN | ⟨C, n, HP, EC⟩
    · apply Or.inl
      simpa only [proofEraseCtx, proofErase_subst_with hΓ₀ W hA ES, EA, ProofShape.subst] using
        ScopedTypeRecovery.lam RN
    · refine .inr ⟨.forallE (A.subst σ) C, n+1, .lam hA' HP, ?_⟩
      obtain ⟨_, hC⟩ := HP.hasType.isType henv hΓA
      rw [show proofErase Γ₀ (.forallE _ _) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ₀ (HasType.forallE hA' hC)), EC,
        proofErase_subst_with hΓ₀ W hA ES, EA]
      rfl
  | app _ ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv W.wf
    rcases ih hΓ₀ W ES hf EΓ Ef HI with RN | ⟨T', n, HP, ET⟩
    · apply Or.inl
      rw [ProofShape.subst_inst]; exact .app RN
    · change proofErase Γ₀ T' = .forallE _ _ at ET
      obtain ⟨C, E, rfl, _, EC, EE⟩ := erase_forallE_inv ET
      have ha' := argument_at_displayed_domain hΓ₀
        (hf.subst henv.orderedStrong W hΓ₀) HP.hasType (ha.subst henv.orderedStrong W hΓ₀)
      refine .inr ⟨E.inst (a.subst σ), n+1, .app HP ha', ?_⟩
      obtain ⟨_, hPi⟩ := HP.hasType.isType henv hΓ₀
      obtain ⟨⟨u, hC⟩, _, hE⟩ := hPi.forallE_inv henv
      have hΓC : OnCtx (C :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hC⟩
      rw [proofErase_instN hΓC ha' Ctx.InstN.zero hE, EE,
        proofErase_subst_with hΓ₀ W ha ES, Ea, ProofShape.subst_inst]
  | @forallE Δ A u B v RA RB =>
    have HR : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
        (proofEraseCtx Γ) (proofErase Γ e) (.sort (.imax u v)) := by
      simpa only [EΓ, Ee] using ScopedTypeRecovery.forallE RA RB
    obtain ⟨T', ht', ET⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht HR
    obtain rfl := erase_sort_inv ET
    have ht'' : env.HasType univs Γ₀ (e.subst σ) (.sort (.imax u v)) :=
      ht'.subst henv.orderedStrong W hΓ₀
    refine .inr ⟨.sort (.imax u v), 0, .terminal (.type ht'') ht'', ?_⟩
    exact if_neg (not_isProof_of_sort hΓ₀ (ht''.isType henv hΓ₀ |>.choose_spec))
  | proj hi HT hj hlen _ ih =>
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, hjInfo, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv W.wf
    rcases ih hΓ₀ W ES hm.hasType.2 EΓ Em HI with RN | ⟨C, n, HP, _⟩
    · apply Or.inl
      simp only [ProofShape.subst_mkApps, ProofShape.subst] at RN
      rw [projectionType_subst HT hj (by omega)]
      exact .proj hi HT hj (by simpa only [List.length_map] using hlen) RN
    · rcases HP.expose heq hs hΓ₀ with HTerm | ⟨A, b, B, j, u, _, hA, HB, RF, _⟩
      · exact (HTerm.not_projection hΓ₀ (ht.subst henv.orderedStrong W hΓ₀)
          (mt (isProof_subst hΓ₀ W ht).1 hn)).elim
      · have hm' := hm.hasType.2.subst henv.orderedStrong W hΓ₀
        have HE := RF.simAt henv.orderedStrong henv.betaSubjectReduction hΓ₀ _ hm'
        have hLam := HasType.lam hA HB.hasType
        have HC := hLam.uniqU henv hΓ₀ HE.hasType.2
        simp only [VExpr.subst_mkApps, VExpr.subst] at HC
        obtain ⟨_, hPi⟩ := hLam.isType henv hΓ₀
        exact (henv.headInversion.forallE_rigid hΓ₀ (henv.projectionRigid hjInfo)
          (HC.typeChain henv hΓ₀ hPi)).elim
  | convert R RC ih =>
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep W.wf ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨_, hA⟩ := heA.isType henv W.wf
    have RC' := RC.subst_typed hstep stage_zero_primitive_substitution W.wf hA EΓ EA
      (by rw [← EΓ]; exact ContextSubstitution.of_typed hΓ₀ W ES)
    rcases ih hΓ₀ W ES ht EΓ Ee HI with RN | ⟨C, n, HP, EC⟩
    · exact .inl (.convert RN RC')
    · obtain ⟨_, hC⟩ := HP.hasType.isType henv hΓ₀
      rw [← EC] at RC'
      obtain ⟨U, HE, EU⟩ := proofErase_scoped_compute_realize hstep hΓ₀ hC rfl rfl RC'
      exact .inr ⟨U, n+1, HP.convert HE (by simpa only [EU] using RC'), EU⟩

end Lean4Lean.VEnv.Strengthening
