import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoverableInstantiation

/-! # Exactly recoverable inhabitants of proposition-producing function types

Canonical Eq supplies a closed proposition whose recovered sort is literally
Prop. A constant function returning it therefore recovers A -> Prop exactly
for every typed domain A, without normalizing universe syntax. Such a function
can retract an unused A -> Prop binder in the full finite joint checker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem native_app
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
      (proofErase Γ (.forallE A B))) :
    ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ (.app f x))
      (proofErase Γ (B.inst x)) := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, hB⟩ := hPi.forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at R
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn,
    proofErase_instN hΓA hx Ctx.InstN.zero hB]
  exact .app R

private theorem native_const
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars) (hn : ¬ IsProof Γ (.const c ls)) :
    ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ (.const c ls))
      (proofErase Γ (ci.type.instL ls)) := by
  have ht : env.HasType univs [] (.const c ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨_, hT⟩ := ht.isType henv (by trivial)
  rw [show proofErase Γ (.const c ls) = .const c ls from if_neg hn,
    proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ]
  exact .const hc hw hl

private def closedProposition : VExpr :=
  eqApp (.succ (.succ .zero)) (.sort (.succ .zero)) (.sort .zero) (.sort .zero)

private theorem closedProposition_typed (heq : env.HasCanonicalEq) :
    env.HasType univs Γ closedProposition (.sort .zero) :=
  HasType.eqApp heq (by trivial) (.sort (by trivial)) (.sort (by trivial)) (.sort (by trivial))

private theorem closedProposition_recovered (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ closedProposition) (.sort .zero) := by
  let w : VLevel := .succ (.succ .zero)
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort w) := .sort (by trivial)
  have hP : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have h0 : env.HasType univs Γ (.const ``Eq [w])
      (.forallE (.sort w) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) := by
    simpa [canonicalEqType, VExpr.instL, VLevel.inst] using
      (HasType.const (Γ := Γ) heq.1 (ls := [w]) (by intro l hl; cases List.mem_singleton.1 hl; trivial) rfl)
  have h1 : env.HasType univs Γ (.app (.const ``Eq [w]) (.sort (.succ .zero)))
      (.forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero)) (.sort .zero))) := by
    simpa [VExpr.inst, instVar, VExpr.liftN] using h0.app hS
  have h2 : env.HasType univs Γ (.app (.app (.const ``Eq [w]) (.sort (.succ .zero))) (.sort .zero))
      (.forallE (.sort (.succ .zero)) (.sort .zero)) := h1.app hP
  have h3 : env.HasType univs Γ closedProposition (.sort .zero) := h2.app hP
  have hn3 := not_isProof_of_sort hΓ h3
  have hn2 := not_isProof_fn hΓ h2 hP hn3
  have hn1 := not_isProof_fn hΓ h1 hP hn2
  have hn0 := not_isProof_fn hΓ h0 hS hn1
  have R0 := native_const (Step := Step) hΓ heq.1
    (ls := [w]) (by intro l hl; cases List.mem_singleton.1 hl; trivial) rfl hn0
  have R1 := native_app hΓ h0 hS hn1
    (by simpa [canonicalEqType, VExpr.instL, VLevel.inst] using R0)
  have R2 := native_app hΓ h1 hP hn2
    (by simpa [VExpr.inst, instVar, VExpr.liftN] using R1)
  have R3 := native_app hΓ h2 hP hn3 R2
  simpa only [VExpr.inst, closedProposition, eqApp, w, show proofErase Γ (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))] using R3

/-- Every typed A -> Prop has an actual non-proof inhabitant with exact
syntax-directed recovery in any computation relation, hence at stage zero.
No inhabitation or recovery premise on the domain A is required. -/
theorem recoverable_prop_function (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ∃ f, env.HasType univs Γ f (.forallE A (.sort .zero)) ∧ ¬ IsProof Γ f ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (proofErase Γ (.forallE A (.sort .zero))) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hf : env.HasType univs Γ (.lam A closedProposition) (.forallE A (.sort .zero)) :=
    .lam hA (closedProposition_typed heq)
  have hn := not_isProof_function_to_sort hΓ hf
  refine ⟨_, hf, hn, ?_⟩
  have hPi := HasType.forallE hA (HasType.sort (l := .zero) (by trivial))
  rw [show proofErase Γ (.lam A closedProposition) = .lam _ _ from if_neg hn,
    show proofErase Γ (.forallE A (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi),
    show proofErase (A :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓA (HasType.sort (by trivial)))]
  exact .lam (closedProposition_recovered heq hΓA)

/-- An unused proposition-producing function binder can be removed from an
existing joint comparison certificate without increasing its finite stage.
The proof substitutes an exactly recovered inhabitant, not inverse weakening. -/
theorem proofErase_joint_compare_drop_prop_function
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : JointCompare (ErasedJointStage D stage)
      (proofEraseCtx (.forallE A (.sort .zero) :: Γ)) mode
      ((proofErase Γ a).liftN 1) ((proofErase Γ b).liftN 1)) :
    JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b) := by
  obtain ⟨f, hf, _, RF⟩ := recoverable_prop_function (Step := ErasedJointStage D 0) heq hΓ hA
  have hPi := HasType.forallE hA (HasType.sort (l := .zero) (by trivial))
  have hΓF : OnCtx (.forallE A (.sort .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hPi⟩
  rw [← proofErase_liftN hΓ hΓF Ctx.LiftN.one ha,
    ← proofErase_liftN hΓ hΓF Ctx.LiftN.one hb] at H
  have HC := proofErase_joint_compare_inst_recoverable heq hs hΓ hf (fun _ => RF)
    (ha.weak henv) (hb.weak henv) H
  simpa only [Nat.zero_add, VExpr.inst_lift] using HC

end Lean4Lean.VEnv.Strengthening
