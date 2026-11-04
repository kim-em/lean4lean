import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePathImageSubstitution

/-! # Exact native recovery when local arguments are never queried

Recovery follows application functions and projection majors, but does not query
an application's argument. A syntactic footprint records only variables which
recovery can inspect. Substitution may replace local arguments arbitrarily while
preserving exact native outputs at the protected variable heads.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace ProofShape

/-- Every variable queried by syntax-directed recovery lies above the cutoff.
Application arguments and lambda domains are deliberately not queried. -/
def RecoveryHeadsAbove (cut : Nat) : ProofShape → Prop
  | .bvar i => cut ≤ i
  | .app f _ => RecoveryHeadsAbove cut f
  | .proj _ _ m => RecoveryHeadsAbove cut m
  | .lam _ b => RecoveryHeadsAbove (cut + 1) b
  | .forallE A B => RecoveryHeadsAbove cut A ∧ RecoveryHeadsAbove (cut + 1) B
  | .proof | .sort _ | .const _ _ => True

/-- Exact renaming is required only at queried heads. Local indices below the
cutoff may map to arbitrary expressions, including images without native recovery. -/
structure ProtectedOracleSubstitution (cut cut' : Nat) (Δ Δ' : List ProofShape)
    (τ : Subst) : Prop where
  interpretation : ContextSubstitution Δ Δ' τ
  lookup : ∀ i, cut ≤ i → ∃ j, cut' ≤ j ∧ τ i = .bvar j ∧
    contextOracle Δ' j = (contextOracle Δ i).subst τ

/-- Extending a local telescope preserves the protected suffix and its exact
oracle assignments. The fresh variable is below the new cutoff. -/
theorem ProtectedOracleSubstitution.cons
    (W : ProtectedOracleSubstitution cut cut' Δ Δ' τ) :
    ProtectedOracleSubstitution (cut + 1) (cut' + 1)
      (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  refine ⟨ContextSubstitution.cons W.interpretation, ?_⟩
  intro i hi
  cases i with
  | zero => omega
  | succ i =>
    obtain ⟨j, hj, Ej, ET⟩ := W.lookup i (by omega)
    refine ⟨j + 1, by omega, ?_, ?_⟩
    · simp [Subst.lift, Ej, ProofShape.liftN, liftVar, Nat.add_comm]
    · simp only [contextOracle, TypeOracle.cons, lift_subst_lift] at ET ⊢
      exact congrArg (·.liftN 1) ET

/-- Ordinary exact renaming is the zero-cutoff instance. -/
theorem ContextRenaming.protected (W : ContextRenaming Δ Δ' τ) :
    ProtectedOracleSubstitution 0 0 Δ Δ' τ := by
  refine ⟨W.interpretation, ?_⟩
  intro i _
  obtain ⟨j, Ej, ET⟩ := W.lookup i
  exact ⟨j, Nat.zero_le _, Ej, ET⟩

/-- Removing the newest local binder never queries the replacement image at a
protected head. The old tail assignments remain exact after substitution. -/
theorem ProtectedOracleSubstitution.one
    (W : ContextSubstitution (A :: Δ) Δ (Subst.one x)) :
    ProtectedOracleSubstitution (cut + 1) cut (A :: Δ) Δ (Subst.one x) := by
  refine ⟨W, ?_⟩
  intro i hi
  cases i with
  | zero => omega
  | succ i =>
    refine ⟨i, by omega, rfl, ?_⟩
    simp only [contextOracle, TypeOracle.cons, Subst.one, lift_subst_cons, subst_id]

omit [Params] in
private theorem recoveryHeads_subst (H : RecoveryHeadsAbove cut e)
    (HV : ∀ i, cut ≤ i → ∃ j, cut' ≤ j ∧ τ i = .bvar j) :
    RecoveryHeadsAbove cut' (e.subst τ) := by
  have lift_hv {cut cut' : Nat} {τ : Subst}
      (HV : ∀ i, cut ≤ i → ∃ j, cut' ≤ j ∧ τ i = .bvar j) :
      ∀ i, cut + 1 ≤ i → ∃ j, cut' + 1 ≤ j ∧ τ.lift i = .bvar j := by
    intro i hi
    cases i with
    | zero => omega
    | succ i =>
      obtain ⟨j, hj, E⟩ := HV i (by omega)
      exact ⟨j + 1, by omega, by simp [Subst.lift, E, liftN, liftVar, Nat.add_comm]⟩
  induction e generalizing cut cut' τ with
  | proof | sort | const => trivial
  | bvar i =>
    obtain ⟨j, hj, E⟩ := HV i H
    simpa only [subst, E, RecoveryHeadsAbove] using hj
  | app f a ih _ => exact ih H HV
  | proj s i m ih => exact ih H HV
  | lam A b _ ih => exact ih H (lift_hv HV)
  | forallE A B ihA ihB => exact ⟨ihA H.1 HV, ihB H.2 (lift_hv HV)⟩

/-- The recovery footprint itself survives every protected oracle substitution. -/
theorem RecoveryHeadsAbove.subst (H : RecoveryHeadsAbove cut e)
    (W : ProtectedOracleSubstitution cut cut' Δ Δ' τ) :
    RecoveryHeadsAbove cut' (e.subst τ) :=
  recoveryHeads_subst H (fun i hi => let ⟨j, hj, E, _⟩ := W.lookup i hi; ⟨j, hj, E⟩)

/-- Contextual computation may change primitive relations during interpreted
substitution; every binder uses the lifted actual interpretation. -/
theorem ScopedCompute.subst_between
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (R : ScopedCompute Step Δ a b) (W : ContextSubstitution Δ Δ' τ) :
    ScopedCompute Step' Δ' (a.subst τ) (b.subst τ) := by
  induction R generalizing Δ' τ with
  | base H => exact .base (hstep H W)
  | beta H => exact .beta H.subst
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ W) (ih₂ W)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ W) (ih₂ W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ W) (ih₂ (ContextSubstitution.cons W))
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ W) (ih₂ (ContextSubstitution.cons W))

/-- Exact native recovery survives arbitrary local replacements when recovery
queries only the protected suffix. Primitive transport is the only computation
hypothesis; no recovery is required for images below the cutoff. -/
theorem ScopedTypeRecovery.subst_protected
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (R : ScopedTypeRecovery Step Δ e T) (H : RecoveryHeadsAbove cut e)
    (W : ProtectedOracleSubstitution cut cut' Δ Δ' τ) :
    ScopedTypeRecovery Step' Δ' (e.subst τ) (T.subst τ) := by
  induction R generalizing cut cut' Δ' τ with
  | bvar =>
    rename_i Δ i
    obtain ⟨j, _, Ej, ET⟩ := W.lookup i H
    simp only [subst, Ej, ← ET]
    exact .bvar
  | sort hu => exact .sort hu
  | const hc hw hn =>
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih => exact .lam (ih H W.cons)
  | app _ ih =>
    rw [subst_inst]
    exact .app (ih H W)
  | forallE _ _ ihA ihB => exact .forallE (ihA H.1 W) (ihB H.2 W.cons)
  | proj hi HT hj hlen _ ih =>
    have HR := ih H W
    simp only [subst_mkApps, subst] at HR
    rw [projectionType_subst HT hj (by omega)]
    exact .proj hi HT hj (by simpa only [List.length_map] using hlen) HR
  | convert _ RC ih => exact .convert (ih H W) (RC.subst_between hstep W.interpretation)

/-- A local beta substitution retains both exact recovery and its footprint. -/
theorem ScopedTypeRecovery.inst_protected
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (R : ScopedTypeRecovery Step (A :: Δ) e T) (H : RecoveryHeadsAbove (cut + 1) e)
    (W : ContextSubstitution (A :: Δ) Δ (Subst.one x)) :
    ScopedTypeRecovery Step' Δ (e.inst x) (T.inst x) ∧ RecoveryHeadsAbove cut (e.inst x) := by
  have WP := ProtectedOracleSubstitution.one (cut := cut) W
  simpa only [inst_eq_subst, Subst.liftN] using
    And.intro (R.subst_protected hstep H WP) (H.subst WP)

end ProofShape

/-- Actual typed instantiation realizes the protected oracle substitution.
The erased replacement may have no native recovery at its assigned type. -/
theorem proofErase_scoped_recovery_inst_protected
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p A) (he : env.HasType univs (A :: Γ) e T)
    (R : ProofShape.ScopedTypeRecovery Step (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) e) out)
    (H : ProofShape.RecoveryHeadsAbove (cut + 1) (proofErase (A :: Γ) e)) :
    ProofShape.ScopedTypeRecovery Step' (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) ∧
      ProofShape.RecoveryHeadsAbove cut (proofErase Γ (e.inst p)) := by
  obtain ⟨u, hA⟩ := hp.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have WI := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have W : ProofShape.ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ p)) :=
    ProofShape.ContextSubstitution.of_typed hΓ WI (erasedSubstAgreement_one hΓA hp)
  have HH := R.inst_protected hstep H W
  simpa only [← proofErase_instN hΓA hp .zero he] using HH

end Lean4Lean.VEnv.Strengthening
