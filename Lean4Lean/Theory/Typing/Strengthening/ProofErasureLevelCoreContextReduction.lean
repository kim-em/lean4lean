import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreJoinedSubstitution

/-! # Context reduction for level-core native recovery

Oracle entries compute in the ordinary core, while native certificates may use
universe conversion. Actual context interpretation turns this into the already
proved joined-image identity substitution; no second recovery induction is needed.
-/
namespace Lean4Lean.VEnv.Strengthening.LevelCoreNative
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private forall_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreNativeReduction
variable [Params] {D : Definitions}

/-- Context conversion realizable at every source erasure, together with forward
computation of every oracle entry. This does not assert arbitrary conversion
can be witnessed by computation. -/
structure ContextReduction (D : Definitions) (Δ Δ' : List ProofShape) : Prop where
  interpretation : ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ', OnCtx Γ' (env.IsType univs) ∧ proofEraseCtx Γ' = Δ' ∧ IsDefEqCtx env univs [] Γ Γ'
  lookup : ∀ i, Compute (ErasedIotaPrimitive D) (contextOracle Δ i) (contextOracle Δ' i)

/-- Actual context conversion and computed oracles supply the raw invariant.
Other source realizations convert through equality of their erased contexts. -/
theorem ContextReduction.of_defeqCtx (D : Definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, Compute (ErasedIotaPrimitive D) (contextOracle (proofEraseCtx Γ) i)
      (contextOracle (proofEraseCtx Γ') i)) :
    ContextReduction D (proofEraseCtx Γ) (proofEraseCtx Γ') := by
  refine ⟨?_, HO⟩
  intro Γ₀ hΓ₀ EΓ₀
  exact ⟨Γ', hΓ', rfl, (proofEraseCtx_defeq hΓ₀ hΓ EΓ₀).trans_empty henv W⟩

/-- Sort witnesses transport to the converted raw context without changing
syntax or universe. -/
theorem ContextReduction.sort (W : ContextReduction D Δ Δ') (S : DomainSort Δ A u) :
    DomainSort Δ' A u := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := S
  obtain ⟨Γ', hΓ', EΓ', HC⟩ := W.interpretation hΓ EΓ
  exact ⟨Γ', a, hΓ', EΓ', ha.defeqDFC henv HC, (proofErase_defeqCtx hΓ HC ha).symm.trans Ea⟩

/-- Ordinary-core computation preserves the universe of a realized domain. -/
theorem domainSort_compute (hs : D.Sound env univs)
    (S : DomainSort Δ A u) (R : Compute (ErasedIotaPrimitive D) A B) : DomainSort Δ B u := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := S
  obtain ⟨b, HR, Eb⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ ha (by simpa only [Ea] using R)
  have hb := (HR.simAt hs hΓ _ ha).hasType.2
  exact ⟨Γ, b, hΓ, EΓ, hb, Eb⟩

/-- Context-oracle reduction extends beneath a domain reduced in the target
context. Source typing and replay supply the actual converted target binder;
no syntactic original representative of the raw reduct is assumed. -/
theorem ContextReduction.cons_compute (hs : D.Sound env univs) (W : ContextReduction D Δ Δ')
    (R : Compute (ErasedIotaPrimitive D) A B) : ContextReduction D (A :: Δ) (B :: Δ') := by
  refine ⟨?_, ?_⟩
  · intro Γ hΓ EΓ
    cases Γ with
    | nil => cases EΓ
    | cons C Γ =>
      obtain ⟨EC, EΓ⟩ := List.cons.inj EΓ
      obtain ⟨hΓ, u, hC⟩ := hΓ
      obtain ⟨Γ', hΓ', EΓ', HC⟩ := W.interpretation hΓ EΓ
      have hC' := hC.defeqDFC henv HC
      have EC' := (proofErase_defeqCtx hΓ HC hC).symm.trans EC
      obtain ⟨C', HR, EC''⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ' hC'
        (by simpa only [EC'] using R)
      have hC'' := (HR.simAt hs hΓ' _ hC').hasType.2
      have HE := HR.simAt hs hΓ' _ hC'
      refine ⟨C' :: Γ', ⟨hΓ', u, hC''⟩, ?_, .succ HC (HE.defeqDFC henv (HC.symm henv.ordered))⟩
      simp only [proofEraseCtx, EC'', EΓ']
  · intro i
    cases i with
    | zero => exact R.liftN (fun H => erased_iota_primitive_liftN H)
    | succ i => exact (W.lookup i).liftN (fun H => erased_iota_primitive_liftN H)

/-- An unchanged displayed binder is the reflexive-domain case. -/
theorem ContextReduction.cons (hs : D.Sound env univs) (W : ContextReduction D Δ Δ') :
    ContextReduction D (A :: Δ) (A :: Δ') := W.cons_compute hs .refl

/-- A well-formed source supplies the reflexive context reduction. -/
theorem ContextReduction.refl (D : Definitions) (hΓ : OnCtx Γ (env.IsType univs)) :
    ContextReduction D (proofEraseCtx Γ) (proofEraseCtx Γ) :=
  .of_defeqCtx D hΓ hΓ (.refl hΓ) (fun _ => .refl)

/-- Native level-core recovery survives forward ordinary oracle reduction by
an interpreted identity substitution, with an ordinary output residual. -/
theorem ContextReduction.recovery
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : ContextReduction D (proofEraseCtx Γ) Δ')
    (R : ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ' (proofErase Γ e) out' ∧
      Compute (ErasedIotaPrimitive D) out out' := by
  obtain ⟨Γ', hΓ', EΓ', HC⟩ := W.interpretation hΓ rfl
  have WS : Ctx.SubstEq env univs Γ' VExpr.Subst.id VExpr.Subst.id Γ :=
    substEq_source_convert hΓ' (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓ')
  have ES : ErasedSubstAgreement Γ Γ' VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    have hn' : ¬ IsProof Γ' (.bvar i) := mt (isProof_defeqCtx HC).2 hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]
  have HI : Images D Γ Γ' ProofShape.Subst.id := by
    intro i A hl hn
    refine ⟨_, .bvar, ?_⟩
    simpa only [ProofShape.subst_id, EΓ'] using W.lookup i
  obtain ⟨out', RN, RC⟩ := recovery_subst hs hlevels hD hc hcon R hΓ' WS ES ht rfl rfl HI
  exact ⟨out', by simpa only [ProofShape.subst_id, EΓ'] using RN,
    by simpa only [ProofShape.subst_id] using RC⟩

/-- Recovered Pis retain forward ordinary domain and codomain paths through
context reduction, even though their native certificates allow universe steps. -/
theorem ContextReduction.recovery_pi
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : ContextReduction D (proofEraseCtx Γ) Δ')
    (R : ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (proofErase Γ e) (.forallE A B)) :
    ∃ A' B', ScopedTypeRecovery (fun _ => ErasedLevelCore D) Δ' (proofErase Γ e) (.forallE A' B') ∧
      Compute (ErasedIotaPrimitive D) A A' ∧ Compute (ErasedIotaPrimitive D) B B' := by
  obtain ⟨out, RN, RC⟩ := W.recovery hs hlevels hD hc hcon hΓ ht R
  obtain ⟨A', B', rfl, RA, RB⟩ := forall_parts RC
  exact ⟨A', B', RN, RA, RB⟩

end Lean4Lean.VEnv.Strengthening.LevelCoreNative
