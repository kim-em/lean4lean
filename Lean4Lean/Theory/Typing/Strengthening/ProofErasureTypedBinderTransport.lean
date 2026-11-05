import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedTelescopeCongruence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationApplication

/-! # Changing binder declarations in typed computation chains

Abstract a body chain, convert the function assignment, weaken, then apply to a
fresh variable. Administrative beta returns the original body syntax in the new
context. This transports chains without claiming exact forward transport of
native certificates or primitive computations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Actual well-formed binder insertion preserves typed computation chains.
The forward steps use exact primitive renaming, not arbitrary substitution. -/
theorem TypedComputationEq.liftN
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (H : TypedComputationEq D Γ a b T) :
    TypedComputationEq D Γ' (a.liftN n k) (b.liftN n k) (T.liftN n k) := by
  have hrename : ∀ {Δ Δ' a b σ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' σ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst σ) (b.subst σ) := by
    intro Δ Δ' a b σ ⟨stage, R⟩ W
    exact ⟨stage, erased_static_structure_eta_expansion_stage_rename heq hs stage R W⟩
  induction H with
  | step HE R =>
    have R' := R.rename hrename (ContextRenaming.of_liftN hΓ hΓ' W)
    simp only [subst_bvar_liftN] at R'
    rw [← proofErase_liftN hΓ hΓ' W HE.hasType.1,
      ← proofErase_liftN hΓ hΓ' W HE.hasType.2] at R'
    exact .step (HE.weakN henv W) R'
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [Params] in
/-- Fresh application cancels a displayed lambda's annotation and returns its
body without any computation inside that body. -/
private theorem fresh_lambda_beta (A b : VExpr) :
    VExpr.BetaRed (.app (VExpr.lam A b).lift (.bvar 0)) b := by
  simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar] using
    (VExpr.BetaRed.beta (A := A.lift) (b := b.liftN 1 1) (a := .bvar 0))

/-- A typed chain under one binder survives ordinary conversion of that
binder's declaration, with identical term and assignment syntax. The proof
uses abstraction, converted application and beta forks; it does not preserve
the individual forward paths or assume native context transport. -/
theorem TypedComputationEq.change_binder
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HA : env.IsDefEq univs Γ A A' (.sort u))
    (H : TypedComputationEq D (A :: Γ) b b' T) :
    TypedComputationEq D (A' :: Γ) b b' T := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HA.hasType.1⟩
  have hΓA' : OnCtx (A' :: Γ) (env.IsType univs) := ⟨hΓ, u, HA.hasType.2⟩
  obtain ⟨v, hT⟩ := H.defeq.hasType.1.isType henv hΓA
  have HL : TypedComputationEq D Γ (.lam A b) (.lam A b') (.forallE A T) :=
    H.wrapLams (ds := [A]) hΓ hΓA
  have HL' := HL.convert (IsDefEq.forallEDF HA hT)
  have HW := HL'.liftN heq hs hΓ hΓA' Ctx.LiftN.one
  have hx : env.HasType univs (A' :: Γ) (.bvar 0) A'.lift := .bvar .zero
  have HP := HW.app_fn hΓA' hx
  change TypedComputationEq D (A' :: Γ)
    (.app (VExpr.lam A b).lift (.bvar 0)) (.app (VExpr.lam A b').lift (.bvar 0))
    ((T.liftN 1 1).inst (.bvar 0)) at HP
  rw [VExpr.inst_liftN_bvar] at HP
  exact (TypedComputationEq.of_beta hΓA' HP.defeq.hasType.1 (fresh_lambda_beta A b)).symm.trans
    (HP.trans (TypedComputationEq.of_beta hΓA' HP.defeq.hasType.2 (fresh_lambda_beta A b')))

/-- Opening a chain between literal lambda telescopes at their assigned
domains recovers a body chain under the full telescope. Fresh applications and
beta suffice; no inverse weakening or strengthening theorem is used. -/
theorem TypedComputationEq.open_wrapLams
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEq D Γ (VExpr.wrapLams ds b) (VExpr.wrapLams ds b') (VExpr.wrapForalls ds T)) :
    TypedComputationEq D (ds.reverse ++ Γ) b b' T := by
  induction ds generalizing Γ with
  | nil => exact H
  | cons A ds ih =>
    obtain ⟨⟨u, hA⟩, _⟩ := (H.defeq.hasType.1.isType henv hΓ).forallE_inv henv.ordered
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HW := H.liftN heq hs hΓ hΓA Ctx.LiftN.one
    have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
    have HP := HW.app_fn hΓA hx
    change TypedComputationEq D (A :: Γ)
      (.app (VExpr.lam A (VExpr.wrapLams ds b)).lift (.bvar 0))
      (.app (VExpr.lam A (VExpr.wrapLams ds b')).lift (.bvar 0))
      (((VExpr.wrapForalls ds T).liftN 1 1).inst (.bvar 0)) at HP
    rw [VExpr.inst_liftN_bvar] at HP
    have HB := (TypedComputationEq.of_beta hΓA HP.defeq.hasType.1
      (fresh_lambda_beta A (VExpr.wrapLams ds b))).symm.trans
      (HP.trans (TypedComputationEq.of_beta hΓA HP.defeq.hasType.2
        (fresh_lambda_beta A (VExpr.wrapLams ds b'))))
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih hΓA HB

/-- A declaration at arbitrary binder depth may change by ordinary equality
while a typed computation chain retains its literal terms and assigned type.
The intervening dependent prefix is closed, transported, then reopened. Its
well-formedness after the change follows from the transported function typing. -/
theorem TypedComputationEq.change_binder_under_prefix
    {ds : List VExpr}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HA : env.IsDefEq univs Γ A A' (.sort u))
    (hctx : OnCtx (ds.reverse ++ A :: Γ) (env.IsType univs))
    (H : TypedComputationEq D (ds.reverse ++ A :: Γ) b b' T) :
    TypedComputationEq D (ds.reverse ++ A' :: Γ) b b' T := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HA.hasType.1⟩
  have hΓA' : OnCtx (A' :: Γ) (env.IsType univs) := ⟨hΓ, u, HA.hasType.2⟩
  exact ((H.wrapLams hΓA hctx).change_binder heq hs hΓ HA).open_wrapLams heq hs hΓA'

/-- Full ordinary conversion of a dependent context preserves typed computation
equality. Each binder is handled by closing, transporting and reopening a lambda
chain, then changing its declaration by converted fresh application. There is no
assumption that the original forward computations or native guards transport. -/
theorem TypedComputationEq.defeqCtx
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ Γ') (H : TypedComputationEq D Γ a b T) :
    TypedComputationEq D Γ' a b T := by
  induction W generalizing a b T with
  | zero => exact H
  | @succ Γ₁ Γ₂ A₁ A₂ u W HA ih =>
    have hΓ₁ := W.isType' hΓ₀
    have hΓ₂ := (W.symm henv.ordered).isType' hΓ₀
    have hΓA : OnCtx (A₁ :: Γ₁) (env.IsType univs) := ⟨hΓ₁, u, HA.hasType.1⟩
    have HL := H.wrapLams (ds := [A₁]) hΓ₁ hΓA
    have HL' := ih HL
    have HB := HL'.open_wrapLams heq hs hΓ₂
    exact HB.change_binder heq hs hΓ₂ (HA.defeqDFC henv.ordered W)

/-- Typed computation equality is invariant under ordinary dependent-context
conversion. This concerns finite chains, not equality of individual paths. -/
theorem typed_computation_eq_defeqCtx_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : IsDefEqCtx env univs Γ₀ Γ Γ') :
    TypedComputationEq D Γ a b T ↔ TypedComputationEq D Γ' a b T :=
  ⟨fun H => H.defeqCtx heq hs hΓ₀ W,
    fun H => H.defeqCtx heq hs hΓ₀ (W.symm henv.ordered)⟩

end Lean4Lean.VEnv.Strengthening
