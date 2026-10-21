import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqNativeCarrierRecovery

/-! # Native recovery paths through arbitrary typed declaration telescopes

Recovery may convert at every prefix before supplying the next argument.
Typed Pi inversion moves those conversions into the original domain context,
where the actual argument can be substituted. The resulting path begins at
the declaration's native residual type, with no exact-recovery requirement.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Recovery of a constant computes from the stored declaration type.
No normal-form assumption on that declaration type is required. -/
theorem ProofShape.ScopedTypeRecovery.const_compute
    (hc : env.constants c = some ci)
    (R : ScopedTypeRecovery Step Δ (.const c ls) out) :
    ScopedCompute Step Δ (proofErase [] (ci.type.instL ls)) out := by
  generalize E : ProofShape.const c ls = e at R
  induction R with
  | const hc' hw hl =>
    cases E
    cases Option.some.inj (hc.symm.trans hc')
    exact .refl
  | convert _ H ih => exact (ih E).trans H
  | bvar | sort | lam | app | forallE | proj => cases E

/-- A computed Pi can be instantiated using an argument typed at its original
domain. The resulting computation begins at the original substituted codomain,
although the Pi's computed domain and codomain may both have changed. -/
theorem proofErase_computed_pi_inst
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (ha : env.HasType univs Γ a A)
    (R : ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (.forallE D C)) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (B.inst a))
      (C.inst (proofErase Γ a)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  rw [show proofErase Γ (.forallE A B) =
    .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))] at R
  obtain ⟨D', C', HE, _, RB⟩ := R.forallE_inv_typed hstep hsubst hhead hΓ hA rfl
  cases HE
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA ha
  change ScopedCompute Step (proofEraseCtx (A :: Γ)) _ _ at RB
  have RB := RB.subst hsubst (ContextSubstitution.of_typed hΓ W (erasedSubstAgreement_one hΓA ha))
  rw [proofErase_instN hΓA ha Ctx.InstN.zero hB]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RB

private theorem app_native_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (ha : env.HasType univs Γ a A)
    (HN : ∀ {T}, ScopedTypeRecovery Step (proofEraseCtx Γ) f T →
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) T)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (.app f (proofErase Γ a)) out) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (B.inst a)) out := by
  generalize EΔ : proofEraseCtx Γ = Δ at R
  generalize E : ProofShape.app f (proofErase Γ a) = e at R
  induction R with
  | app RF =>
    cases E
    rw [← EΔ] at RF ⊢
    exact proofErase_computed_pi_inst hstep hhead hsubst hΓ hA hB ha (HN RF)
  | convert _ H ih => exact (ih EΔ E).trans H
  | bvar | sort | const | lam | forallE | proj => cases E

private theorem computed_app_native_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (ha : env.HasType univs Γ a A)
    (HN : ∀ {T}, ScopedTypeRecovery Step (proofEraseCtx Γ) f T →
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) T)
    (RA : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ a) argOut)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (.app f argOut) out) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (B.inst a)) out := by
  obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha rfl rfl RA
  have R' := app_native_compute hstep hhead hsubst hΓ hA hB HA.hasType.2 HN (EA ▸ R)
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have RB := proofErase_scoped_compute_inst_argument hsubst hΓA hB ha RA
  rw [proofErase_instN hΓA HA.hasType.2 Ctx.InstN.zero hB, EA] at R'
  exact RB.trans R'

/-- Computing every supplied argument still leaves every recovered residual
type reachable from the original native residual. Earlier computed arguments
may change all later dependent domains; their paths are retained throughout. -/
theorem proofErase_computed_telescope_native_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args residual)
    (HN : ∀ {U}, ScopedTypeRecovery Step (proofEraseCtx Γ) f U →
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) U)
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args.map (proofErase Γ)) args')
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (ProofShape.mkApps f args') out) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ residual) out := by
  induction HW generalizing f u args' with
  | nil => cases HA; exact HN R
  | cons ha HW ih =>
    cases HA with | cons RA HA =>
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
    exact ih (hB.instN henv Ctx.InstN.zero ha)
      (fun R => computed_app_native_compute hstep hhead hsubst hΓ hA hB ha HN RA R) HA R

/-- Native recovery computations propagate through a whole typed telescope.
Every intermediate binder may undergo arbitrary compatible computation before
application. The supplied native type and the actual telescope walk suffice;
the raw head itself needs no additional original realization. -/
theorem proofErase_telescope_native_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args residual)
    (HN : ∀ {U}, ScopedTypeRecovery Step (proofEraseCtx Γ) f U →
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) U)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (ProofShape.mkApps f (args.map (proofErase Γ))) out) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ residual) out := by
  induction HW generalizing f u with
  | nil => exact HN R
  | cons ha HW ih =>
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
    have hBa := hB.instN henv Ctx.InstN.zero ha
    exact ih hBa
      (fun R => app_native_compute hstep hhead hsubst hΓ hA hB ha HN R) R

/-- A declared constant's typed prefix always recovers by computation from its
native residual type. This uses the literal declaration telescope, not an
arbitrary type assigned to the prefix by semantic conversion. -/
theorem proofErase_const_prefix_native_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args residual)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) out) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ residual) out := by
  have hf := HasType.const (Γ := Γ) hc hw hl
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have hf₀ := HasType.const (Γ := []) hc hw hl
  obtain ⟨_, hT₀⟩ := hf₀.isType henv (by trivial)
  apply proofErase_telescope_native_compute hstep hhead hsubst hΓ hT HW ?_ R
  intro U H
  rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT₀ hΓ]
  exact H.const_compute hc

/-- A constant prefix may compute all of its arguments before recovery.
The original declaration residual still computes to the entire selected type. -/
theorem proofErase_computed_const_prefix_native_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args residual)
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args.map (proofErase Γ)) args')
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) args') out) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ residual) out := by
  have hf := HasType.const (Γ := Γ) hc hw hl
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have hf₀ := HasType.const (Γ := []) hc hw hl
  obtain ⟨_, hT₀⟩ := hf₀.isType henv (by trivial)
  apply proofErase_computed_telescope_native_compute hstep hhead hsubst hΓ hT HW ?_ HA R
  intro U H
  rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT₀ hΓ]
  exact H.const_compute hc

/-- The domain chosen for the next argument is reachable from the declaration's
native domain after the supplied prefix. Parameters may themselves be proofs,
functions, or arbitrary typed data; none must recover an assigned type. -/
theorem proofErase_const_prefix_domain_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) (.forallE D C)) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) D := by
  have H := proofErase_const_prefix_native_compute hstep hhead hsubst hΓ hc hw hl HW R
  rw [show proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ hPi)] at H
  obtain ⟨_, _, HE, HD⟩ := H.forallE_domain_inv hhead
  cases HE
  exact HD

end Lean4Lean.VEnv.Strengthening
