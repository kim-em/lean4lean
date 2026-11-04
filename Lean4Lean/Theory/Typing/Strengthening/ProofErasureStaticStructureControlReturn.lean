import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureCommonApplication

/-! # Returning from computations of closed control types

Universes and closed arrows return from every enriched computed output.
In the arrow case, restore the domain before restoring the codomain: the
codomain history is already retained in precisely that original context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions} {t : ControlType}

/-- Return paths for a dependent Pi's components suffice to return from
any computation of the whole Pi. Both component premises use their ORIGINAL
contexts: restore the domain first, then use the codomain return there. -/
theorem static_structure_pi_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (HA : ∀ {out}, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) out → ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) out (proofErase Γ A))
    (HB : ∀ {out}, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) out → ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx (A :: Γ)) out (proofErase (A :: Γ) B))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (proofErase Γ (.forallE A B)) := by
  have E : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))
  rw [E] at R ⊢
  obtain ⟨X, Y, ⟨_, _, _, _, _, _, RA, RB⟩, Rβ⟩ :=
    proofErase_static_structure_union_pi_origin heq hs hΓ hA hB R
  exact (ScopedCompute.beta Rβ).trans
    ((ScopedCompute.forallE (HA RA) .refl).trans (.forallE .refl (HB RB)))

/-- Every computation from a well-formed closed control type can return to
its exact source. Temporary frames and arbitrary structure/function-eta guard
depths are allowed. Arrow components return in domain-then-codomain order. -/
theorem static_structure_control_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : t.WF univs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ t.expr) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (proofErase Γ t.expr) := by
  induction t generalizing Γ out with
  | sort u =>
    have E : proofErase Γ (.sort u) = .sort u :=
      if_neg (not_isProof_of_sort hΓ (HasType.sort hw))
    change ScopedCompute _ _ (proofErase Γ (.sort u)) out at R
    change ScopedCompute _ _ out (proofErase Γ (.sort u))
    rw [E] at R ⊢
    obtain ⟨v, HE, _, RB⟩ := proofErase_static_structure_union_sort_readout heq hs hΓ hw R
    exact (ScopedCompute.beta RB).trans (.base ⟨0, .inl (.inr (.sort HE.symm hw))⟩)
  | arrow A B ihA ihB =>
    have hA : env.HasType univs Γ A.expr (.sort A.level) := ControlType.typed hw.1
    have hΓA : OnCtx (A.expr :: Γ) (env.IsType univs) := ⟨hΓ, A.level, hA⟩
    have hB : env.HasType univs (A.expr :: Γ) B.expr (.sort B.level) := ControlType.typed hw.2
    exact static_structure_pi_return heq hs hΓ hA hB
      (fun R => ihA hΓ hw.1 R) (fun R => ihB hΓA hw.2 R) R

/-- Every fork from a closed control type joins at that original type,
without imposing any normal-form restriction on either output. -/
theorem static_structure_control_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hw : t.WF univs)
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ t.expr) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ t.expr) right) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared :=
  ⟨_, static_structure_control_return heq hs hΓ hw RL,
    static_structure_control_return heq hs hΓ hw RR⟩

/-- Common native recovery at a closed control type restores the exact
assigned type, including arbitrary nested higher-order control arrows. -/
theorem static_structure_exact_control_of_common
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e t.expr)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ t.expr) shared) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ t.expr) := by
  obtain ⟨_, hT⟩ := ht.isType henv hΓ
  exact RN.convert (static_structure_control_return heq hs hΓ
    (ControlType.wf_of_typing henv.ordered hT) RC)

/-- Backward transport across a computed binder preserves a native recovery
certificate exactly. The native identity images reuse the domain path. -/
theorem proofErase_static_structure_union_recovery_backward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (ht : env.HasType univs (B :: Γ) e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out := by
  obtain ⟨k, RA⟩ := RA.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  obtain ⟨n, RN⟩ := RN.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have R := StaticStructureEtaNativeSubstitution.recovery heq hs RN hΓB ht rfl rfl
    (static_structure_native_backward_context heq hs hΓ HAB RA)
  have EE := proofErase_defeqCtx hΓB (IsDefEqCtx.succ .zero HAB.symm) ht
  simpa only [ProofShape.subst_id, EE] using R.mono (fun H => ⟨n+k, H⟩)

/-- A binder computed from a closed control type admits exact forward native
transport. Its return computation supplies the reverse domain path needed by
backward context transport. The body and selected output are unrestricted. -/
theorem static_structure_control_forward_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAC : env.IsDefEq univs Γ t.expr C (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ t.expr) (proofErase Γ C))
    (ht : env.HasType univs (t.expr :: Γ) e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (t.expr :: Γ))
      (proofErase (t.expr :: Γ) e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) e) out := by
  have RR := static_structure_control_return heq hs hΓ
    (ControlType.wf_of_typing henv.ordered HAC.hasType.1) RA
  exact proofErase_static_structure_union_recovery_backward_context heq hs hΓ HAC.symm RR ht RN

/-- Applications at any closed control domain need only common native
argument evidence. This includes higher-order arguments at nested arrows. -/
theorem static_structure_common_control_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE t.expr B))
    (hx : env.HasType univs Γ x t.expr) (hn : ¬ IsProof Γ (.app f x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.forallE t.expr B)) shared)
    (RNx : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) sharedX)
    (RCx : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ t.expr) sharedX) :
    ∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (.app f x)) out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (B.inst x)) out :=
  static_structure_common_application heq hs hΓ hf hx hn
    (fun _ => static_structure_exact_control_of_common heq hs hΓ hx RNx RCx) RN RC

end Lean4Lean.VEnv.Strengthening
