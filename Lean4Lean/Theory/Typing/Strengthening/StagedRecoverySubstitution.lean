import Lean4Lean.Theory.Typing.Strengthening.StagedEtaComputation
import Lean4Lean.Theory.Typing.Strengthening.RecoverySubstitutionCore

/-! # Substitution adds finite recovery stages

If the argument recovers its declaration at stage r, substituting it in a
stage-n computation gives a stage-(r+n) computation. The bound handles eta
inside recovered types and inside K endpoint certificates. Exact recovery
of the argument is essential; arbitrary typed substitution is not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- Computed endpoint comparisons transform along their component computations;
homogeneous substitution preserves the final hybrid normal comparison. -/
theorem ComputedComparison.instN_to (H : ComputedComparison C Γ₁ a b)
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ha : env.HasType univs Γ₁ a α) (hb : env.HasType univs Γ₁ b α) :
    ComputedComparison C' Γ (a.inst x k) (b.inst x k) := by
  obtain ⟨a', b', n, Ra, Rb, H⟩ := H
  obtain ⟨n', H'⟩ := H.instN hΓ₁ hx W
  exact ⟨_, _, n', hsub hΓ₁ W ⟨_, ha⟩ Ra, hsub hΓ₁ W ⟨_, hb⟩ Rb, H'⟩

/-- A stage's two computational alternatives transform when its predecessor
does. The K alternative replaces its whole guard relation with the new one. -/
theorem NextComputation.substitution (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : ComputeDescent C) (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hx : env.HasType univs Γ₀ x A₀) :
    ComputeSubstitutionTo (NextComputation D C) (NextComputation D C') Γ₀ x A₀ := by
  intro k Γ₁ Γ e out hΓ₁ W ht R
  cases R with
  | inl R => exact .inl (hsub hΓ₁ W ht R)
  | inr R =>
    apply Or.inr
    exact R.instN_to heq hs (ComputedComparison.descends hc)
      (fun hΓ W ha hb H => H.instN_to hsub hΓ hx W ha hb) hΓ₁ W ht

/-- Substitution has an additive bound in the source and argument stages. All
recursive eta annotations and endpoint computations are transformed together. -/
theorem StagedEtaCompute.substitution (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hx : env.HasType univs Γ₀ x A₀) (Rx : StagedTypeRecovery D kdepth r Γ₀ x A₀) :
    ∀ stage, ComputeSubstitutionTo (StagedEtaCompute D kdepth stage)
      (StagedEtaCompute D kdepth (r + stage)) Γ₀ x A₀ := by
  intro stage
  induction stage with
  | zero =>
    intro k Γ₁ Γ e out hΓ₁ W ht R
    have R' := CertifiedKCompute.instN R heq hs hΓ₁ hx W ht
    exact StagedEtaCompute.mono (Nat.zero_le _) R'
  | succ stage ih =>
    have hcs : ComputeDescent (StagedEtaCompute D kdepth stage) := computeDescent heq hs stage
    have hwt : ComputeWeakening (StagedEtaCompute D kdepth (r + stage)) := computeWeakening (r + stage)
    have Rx' : TypeRecoveryWith (NextComputation D (StagedEtaCompute D kdepth (r + stage))) Γ₀ x A₀ :=
      Rx.mono (fun H => Or.inl (H.mono (Nat.le_add_right r stage)))
    intro k Γ₁ Γ e out hΓ₁ W ht R
    exact RecoveredEtaWith.instN_to R (NextComputation.descends heq hs hcs)
      (NextComputation.weakens hwt) (NextComputation.substitution heq hs hcs ih hx)
      hΓ₁ hx Rx' W ht

/-- A source-typed staged path survives a recoverable typed substitution. -/
theorem StagedEtaCompute.instN (R : StagedEtaCompute D kdepth stage Γ₁ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : StagedTypeRecovery D kdepth r Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (ht : VExpr.WF env univs Γ₁ e) :
    StagedEtaCompute D kdepth (r + stage) Γ (e.inst x k) (out.inst x k) :=
  substitution heq hs hx Rx stage hΓ₁ W ht R

/-- Type recovery also preserves the exact substituted output at the additive
stage bound. This is conditional on recovery of the argument's declaration. -/
theorem StagedTypeRecovery.instN (R : StagedTypeRecovery D kdepth stage Γ₁ e T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : StagedTypeRecovery D kdepth r Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (ht : VExpr.WF env univs Γ₁ e) :
    StagedTypeRecovery D kdepth (r + stage) Γ (e.inst x k) (T.inst x k) :=
  TypeRecoveryWith.instN_to R (StagedEtaCompute.computeDescent heq hs stage)
    (StagedEtaCompute.computeWeakening (r + stage))
    (StagedEtaCompute.substitution heq hs hx Rx stage) hΓ₁ hx
    (Rx.mono (fun H => H.mono (Nat.le_add_right r stage))) W ht

/-- Contracting a displayed beta redex carries a body computation through the
argument substitution. The argument may be a lambda and create further redexes. -/
theorem StagedEtaCompute.beta_inst (R : StagedEtaCompute D kdepth stage (A :: Γ) b b')
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx (A :: Γ) (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (Rx : StagedTypeRecovery D kdepth r Γ x A) (hb : VExpr.WF env univs (A :: Γ) b) :
    StagedEtaCompute D kdepth (r + stage) Γ (.app (.lam A b) x) (b'.inst x) :=
  StagedEtaCompute.beta.trans (R.instN heq hs hΓ hx Rx .zero hb)

end Lean4Lean.VEnv.Strengthening
