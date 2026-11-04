import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointAnchoredSubstitution

/-! # Recursive binder conversion at terminal-valued domains

The variable at a terminal-valued domain may replace the old binder under
ordinary domain equality. This uses the earlier anchored substitution theorem,
independently of selected lambda-domain conversion and structural image repair.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- The generic variable at this domain is a terminal image. This records a
proved type/rigid-data/fieldless/proof-field classification, not a comparison
transport law or native recovery hypothesis. -/
def TerminalDomain (Γ : List VExpr) (A : VExpr) : Prop :=
  TerminalImage (A :: Γ) (.bvar 0)

/-- Terminal-valued domains are stable under actual typed substitution. -/
theorem TerminalDomain.subst (H : TerminalDomain Γ A)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hA : env.HasType univs Γ A (.sort u)) : TerminalDomain Γ₀ (A.subst σ) := by
  have hΓA₀ : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) :=
    ⟨hΓ₀, u, hA.subst henv.orderedStrong W hΓ₀⟩
  exact (show TerminalImage (A :: Γ) (.bvar 0) from H).subst (σ := σ.lift) hΓA₀ (W.lift henv.ordered hA)

/-- Ordinary equality transfers terminality to another domain, with no
computational join or raw annotation-shape restriction. -/
theorem TerminalDomain.convert (H : TerminalDomain Γ A)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u)) : TerminalDomain Γ B := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have W : Ctx.SubstEq env univs (B :: Γ) VExpr.Subst.id VExpr.Subst.id (A :: Γ) :=
    substEq_source_convert hΓB (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓB)
  exact (show TerminalImage (A :: Γ) (.bvar 0) from H).subst hΓB W

/-- Every literal universe is a terminal-valued input domain. -/
theorem TerminalDomain.sort : TerminalDomain Γ (.sort u) :=
  .type (HasType.bvar .zero)

/-- Rigid data without projections supplies a terminal-valued domain. -/
theorem TerminalDomain.data (hr : env.Rigid c) (hn : ∀ info, ¬ env.projections c info) :
    TerminalDomain Γ (VExpr.mkApps (.const c ls) args) := by
  have hx : env.HasType univs (VExpr.mkApps (.const c ls) args :: Γ) (.bvar 0)
      (VExpr.mkApps (.const c ls) (args.map (·.liftN 1))) := by
    simpa only [VExpr.liftN_mkApps, VExpr.liftN] using
      (HasType.bvar (U := univs) (env := env)
        (Lookup.zero (ty := VExpr.mkApps (.const c ls) args) (Γ := Γ)))
  exact TerminalImage.data hx hr hn

/-- A registered fieldless structure supplies a terminal-valued domain. -/
theorem TerminalDomain.fieldless (hi : env.projections c info) (hz : info.numFields = 0) :
    TerminalDomain Γ (VExpr.mkApps (.const c ls) args) := by
  have hx : env.HasType univs (VExpr.mkApps (.const c ls) args :: Γ) (.bvar 0)
      (VExpr.mkApps (.const c ls) (args.map (·.liftN 1))) := by
    simpa only [VExpr.liftN_mkApps, VExpr.liftN] using
      (HasType.bvar (U := univs) (env := env)
        (Lookup.zero (ty := VExpr.mkApps (.const c ls) args) (Γ := Γ)))
  exact TerminalImage.fieldless hx hi hz

/-- A closed all-proof-field certificate supplies a terminal-valued structure
domain. The structure itself may inhabit a data universe. -/
theorem TerminalDomain.proofStructure
    (hi : env.projections c info) (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (HF : StructureReplay.ProofFields env univs info ls) :
    TerminalDomain Γ (VExpr.mkApps (.const c ls) ps) := by
  have hv : env.HasType univs (VExpr.mkApps (.const c ls) ps :: Γ) (.bvar 0)
      (VExpr.mkApps (.const c ls) (ps.map (·.liftN 1))) := by
    simpa only [VExpr.liftN_mkApps, VExpr.liftN] using
      (HasType.bvar (U := univs) (env := env)
        (Lookup.zero (ty := VExpr.mkApps (.const c ls) ps) (Γ := Γ)))
  exact TerminalImage.proofStructure hv hi (by simpa only [List.length_map] using hp) hx HF

/-- Converting a binder with terminal-valued source annotation gives an interpreted
anchored-image identity substitution. The target annotation need only be
ordinarily equal and typed; no computational annotation join is required. -/
theorem AnchoredImageSubstitution.terminal_context
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A) :
    AnchoredImageSubstitution D (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ))
      ProofShape.Subst.id := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) :=
    .succ (.refl hΓ) HAB
  have W : Ctx.SubstEq env univs (B :: Γ) VExpr.Subst.id VExpr.Subst.id (A :: Γ) :=
    substEq_source_convert hΓB (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓB)
  have ES : ErasedSubstAgreement (A :: Γ) (B :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    have hn' : ¬ IsProof (B :: Γ) (.bvar i) := mt (isProof_defeqCtx HC).2 hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]
  apply AnchoredImageSubstitution.of_typed (cut := 0) hΓB W ES
  intro i T hl _
  cases hl with
  | zero =>
    apply Or.inr
    exact ⟨0, .terminal (HA.convert hΓ HAB)⟩
  | @succ _ i T _ hl =>
    apply Or.inl
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.subst_id]
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.id] using
      (ScopedTypeRecovery.bvar (Step := ErasedJointStage D 0)
        (Δ := proofEraseCtx (B :: Γ)) (i := i + 1))

/-- Full recursive comparison survives conversion of a terminal-valued source binder.
The raw expression endpoints are unchanged, while the context oracle changes. -/
theorem proofErase_computed_joint_zero_terminal_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (ErasedJointStage D 0) (proofEraseCtx (B :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_anchoredImages hs hΓA ha hb rfl rfl rfl
    (AnchoredImageSubstitution.terminal_context hΓ HAB HA)

/-- Carrier checking survives the same terminal-valued context conversion,
retaining the raw carrier and endpoint syntax. -/
theorem proofErase_computed_joint_zero_carrier_terminal_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HA : TerminalDomain Γ A)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  simpa only [ProofShape.subst_id] using H.transport_anchoredImages hs hΓA ha hb rfl rfl rfl rfl
    (AnchoredImageSubstitution.terminal_context hΓ HAB HA)

end Lean4Lean.VEnv.Strengthening
