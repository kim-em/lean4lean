import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeBetaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Binder transport from type instantiation joining

The single type-valued beta joining obligation already transports a type
computation across an arbitrary definitionally equal binder, without a forward
domain computation. Pi readout also extends that obligation to substitution
below any dependent prefix. Neither result assumes all type forks join.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- The open TypeInstantiationJoin premise transports a type computation
across one definitionally equal binder up to joining. No directed computation
between the binder types, native variable certificate, or TypeForkJoin is used.
The old raw output and the unchanged body are compared in the new context. -/
theorem TypeInstantiationJoin.type_compute_context_conversion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : TypeInstantiationJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ A C (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
        (proofErase (C :: Γ) B) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ)) out shared := by
  have hA := HAC.hasType.1
  have hC := HAC.hasType.2
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have hΓAC : OnCtx (A.lift :: C :: Γ) (env.IsType univs) :=
    ⟨hΓC, u, hA.weakN henv Ctx.LiftN.one⟩
  have W : Ctx.LiftN 1 1 (A :: Γ) (A.lift :: C :: Γ) := Ctx.LiftN.one.succ
  have hBU := hB.weakN henv W
  have hx : env.HasType univs (C :: Γ) (.bvar 0) A.lift :=
    (HAC.weakN henv Ctx.LiftN.one).symm.defeq
      (show env.HasType univs (C :: Γ) (.bvar 0) C.lift from .bvar .zero)
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have RCU := RC.rename hrename (ContextRenaming.of_liftN hΓA hΓAC W)
  simp only [subst_bvar_liftN] at RCU
  rw [← proofErase_liftN hΓA hΓAC W hB] at RCU
  obtain ⟨shared, RL, RR⟩ := HJ hΓC (hA.weakN henv Ctx.LiftN.one) hBU hx RCU
  simp only [VExpr.inst_liftN_bvar] at RL
  obtain ⟨B', HB', EB'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hB rfl rfl RC
  have EU := proofErase_liftN hΓA hΓAC W HB'.hasType.2
  have EI := proofErase_instN hΓAC hx Ctx.InstN.zero (HB'.hasType.2.weakN henv W)
  rw [VExpr.inst_liftN_bvar, EU, EB'] at EI
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have EC : proofErase (C :: Γ) B' = out :=
    (proofErase_defeqCtx hΓA HC HB'.hasType.2).symm.trans EB'
  rw [← EI, EC] at RR
  exact ⟨shared, RL, RR⟩

/-- The single top-binder obligation suffices for type instantiation below an
arbitrary dependent prefix. The induction packages a type below a binder as a
Pi, joins its instantiation, then reads out the two codomain paths in their
original common context. No confluence of a middle endpoint is needed. The
argument has ordinary typing only; TypeInstantiationJoin itself remains open. -/
theorem TypeInstantiationJoin.instN
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HJ : TypeInstantiationJoin D)
    (hx : env.HasType univs Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hB : env.HasType univs Γ₁ B (.sort v))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₁)
      (proofErase Γ₁ B) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x k)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst (proofErase Γ₀ x) k) shared := by
  induction W generalizing B v out with
  | zero =>
    obtain ⟨hΓ, u, hA⟩ := hΓ₁
    exact HJ hΓ hA hB hx RC
  | @succ k Γ₁ Γ A W ih =>
    obtain ⟨hΓ₁, u, hA⟩ := hΓ₁
    have hΓA : OnCtx (A :: Γ₁) (env.IsType univs) := ⟨hΓ₁, u, hA⟩
    have hPi := HasType.forallE hA hB
    have EP : proofErase Γ₁ (.forallE A B) =
        .forallE (proofErase Γ₁ A) (proofErase (A :: Γ₁) B) :=
      if_neg (not_isProof_of_sort hΓ₁ hPi)
    have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₁)
        (proofErase Γ₁ (.forallE A B)) (.forallE (proofErase Γ₁ A) out) := by
      rw [EP]
      exact .forallE .refl (by simpa only [proofEraseCtx] using RC)
    obtain ⟨joint, RL, RR⟩ := ih hΓ₁ hPi RP
    have hΓ := (W.wf henv hx hΓ₁).2
    have hAI := hA.instN henv.ordered W hx
    have hBI := hB.instN henv.ordered W.succ hx
    have EAI := proofErase_instN hΓ₁ hx W hA
    obtain ⟨B', HB', EB'⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hB rfl rfl RC
    have hB'I := HB'.hasType.2.instN henv.ordered W.succ hx
    have EBI := proofErase_instN hΓA hx W.succ HB'.hasType.2
    rw [EB'] at EBI
    have EPL : proofErase Γ ((VExpr.forallE A B).inst x k) =
        .forallE (proofErase Γ (A.inst x k)) (proofErase (A.inst x k :: Γ) (B.inst x (k+1))) :=
      if_neg (not_isProof_of_sort hΓ (HasType.forallE hAI hBI))
    rw [EPL] at RL
    change ScopedCompute _ _
      (.forallE ((proofErase Γ₁ A).inst (proofErase Γ₀ x) k)
        (out.inst (proofErase Γ₀ x) (k+1))) joint at RR
    rw [← EAI, ← EBI] at RR
    obtain ⟨X, Y, ⟨_, _, _, _, _, _, _, RBL⟩, Rβ⟩ :=
      proofErase_static_structure_union_pi_origin heq hs hΓ hAI hBI RL
    obtain ⟨_, _, _, _, _, _, _, RBR⟩ :=
      proofErase_static_structure_union_pi_components heq hs hΓ hAI hB'I (RR.trans (.beta Rβ))
    rw [EBI] at RBR
    exact ⟨Y, RBL, RBR⟩

end Lean4Lean.VEnv.Strengthening
