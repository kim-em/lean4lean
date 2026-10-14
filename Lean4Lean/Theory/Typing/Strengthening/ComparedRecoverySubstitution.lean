import Lean4Lean.Theory.Typing.Strengthening.ComparedEtaComputation
import Lean4Lean.Theory.Typing.Strengthening.StagedRecoverySubstitution
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalApplication

/-! # Substitution through recovered comparison guards

The argument must recover its declared type. Its stage is added to the source
stage, including recoveries inside the new endpoint comparison guards. No
arbitrary-argument exact-output substitution law is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]
variable {C C' : List VExpr → VExpr → VExpr → Prop}

/-- A change of computational base transforms all recovered type certificates
inside both comparison modes. Ambient soundness supplies their source typings. -/
theorem RecoveredComparisonWith.instN_to_of_types
    (H : RecoveredComparisonWith C mode Γ₁ a b)
    (hc : TypeComputeDescent C) (hw : ComputeWeakening C')
    (hsub : TypeComputeSubstitutionTo C C' Γ₀ x A₀)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith C' Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) :
    RecoveredComparisonWith C' mode Γ (a.inst x k) (b.inst x k) := by
  induction H generalizing k Γ with
  | base H => exact .base (H.instN hx W)
  | app hf hg ha hb _ _ ihf iha =>
    exact .app (hf.instN henv W hx) (hg.instN henv W hx) (ha.instN henv W hx)
      (hb.instN henv W hx) (ihf hΓ₁ W) (iha hΓ₁ W)
  | recover Ra Rb HT Hab ihT ihab =>
    obtain ⟨_, hab⟩ := Hab.defeq hΓ₁
    exact .recover (Ra.instN_to_of_types hc hw hsub hΓ₁ hx Rx W ⟨_, hab.hasType.1⟩)
      (Rb.instN_to_of_types hc hw hsub hΓ₁ hx Rx W ⟨_, hab.hasType.2⟩) (ihT hΓ₁ W) (ihab hΓ₁ W)
  | sameType Ra Rb Hab ih =>
    obtain ⟨_, hab⟩ := Hab.defeq hΓ₁
    exact .sameType (Ra.instN_to_of_types hc hw hsub hΓ₁ hx Rx W ⟨_, hab.hasType.1⟩)
      (Rb.instN_to_of_types hc hw hsub hΓ₁ hx Rx W ⟨_, hab.hasType.2⟩) (ih hΓ₁ W)

/-- The former ordinary-computation interface is a specialization of the
sort-source transformation used inside recovered types. -/
theorem RecoveredComparisonWith.instN_to
    (H : RecoveredComparisonWith C mode Γ₁ a b)
    (hc : ComputeDescent C) (hw : ComputeWeakening C')
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith C' Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) :
    RecoveredComparisonWith C' mode Γ (a.inst x k) (b.inst x k) :=
  H.instN_to_of_types hc.types hw hsub.types hΓ₁ hx Rx W

/-- Endpoint computations and the final recovered comparison transform to the
same target base. This includes the comparison's own type computations. -/
theorem RecoveredComputedComparison.instN_to
    (H : RecoveredComputedComparison C Γ₁ a b)
    (hc : ComputeDescent C) (hw : ComputeWeakening C')
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith C' Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ha : env.HasType univs Γ₁ a α) (hb : env.HasType univs Γ₁ b α) :
    RecoveredComputedComparison C' Γ (a.inst x k) (b.inst x k) := by
  obtain ⟨a', b', Ra, Rb, H⟩ := H
  exact ⟨_, _, hsub hΓ₁ W ⟨_, ha⟩ Ra, hsub hΓ₁ W ⟨_, hb⟩ Rb,
    H.instN_to hc hw hsub hΓ₁ hx Rx W⟩

/-- Both alternatives of the extended guard transform under recoverable
substitution, retaining the original endpoint comparison mode. -/
theorem RecoveryComparisonGuard.instN_to
    (H : RecoveryComparisonGuard C Γ₁ a b)
    (hc : ComputeDescent C) (hw : ComputeWeakening C')
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith C' Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ha : env.HasType univs Γ₁ a α) (hb : env.HasType univs Γ₁ b α) :
    RecoveryComparisonGuard C' Γ (a.inst x k) (b.inst x k) :=
  H.elim (fun H => .inl (H.instN_to hsub hΓ₁ hx W ha hb))
    (fun H => .inr (H.instN_to hc hw hsub hΓ₁ hx Rx W ha hb))

/-- Guard transformation supplies the K part of the next-stage substitution. -/
theorem ComparedNextComputation.substitution (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hc : ComputeDescent C) (hw : ComputeWeakening C')
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hx : env.HasType univs Γ₀ x A₀) (Rx : TypeRecoveryWith C' Γ₀ x A₀) :
    ComputeSubstitutionTo (ComparedNextComputation D C) (ComparedNextComputation D C') Γ₀ x A₀ := by
  intro k Γ₁ Γ e out hΓ₁ W ht R
  cases R with
  | inl R => exact .inl (hsub hΓ₁ W ht R)
  | inr R =>
    exact .inr (R.instN_to heq hs (RecoveryComparisonGuard.descends hc)
      (fun hΓ W ha hb H => H.instN_to hc hw hsub hΓ hx Rx W ha hb) hΓ₁ W ht)

/-- The additive stage bound survives recovered application guards, including
type computations nested inside those guards. -/
theorem ComparedEtaCompute.substitution (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith (ComparedEtaCompute D kdepth r) Γ₀ x A₀) :
    ∀ stage, ComputeSubstitutionTo (ComparedEtaCompute D kdepth stage)
      (ComparedEtaCompute D kdepth (r + stage)) Γ₀ x A₀ := by
  intro stage
  induction stage with
  | zero =>
    intro k Γ₁ Γ e out hΓ₁ W ht R
    have R' := CertifiedKCompute.instN R heq hs hΓ₁ hx W ht
    exact ComparedEtaCompute.mono (Nat.zero_le _) R'
  | succ stage ih =>
    have hcs : ComputeDescent (ComparedEtaCompute D kdepth stage) := computeDescent heq hs stage
    have hwt : ComputeWeakening (ComparedEtaCompute D kdepth (r + stage)) := computeWeakening (r + stage)
    have Rx' : TypeRecoveryWith (ComparedEtaCompute D kdepth (r + stage)) Γ₀ x A₀ :=
      Rx.mono (fun H => H.mono (Nat.le_add_right r stage))
    intro k Γ₁ Γ e out hΓ₁ W ht R
    exact RecoveredEtaWith.instN_to R (ComparedNextComputation.descends heq hs hcs)
      (ComparedNextComputation.weakens hwt)
      (ComparedNextComputation.substitution heq hs hcs hwt ih hx Rx') hΓ₁ hx
      (Rx'.mono (fun H => Or.inl H)) W ht

/-- Every source-typed path preserves its exact output at the additive bound
when the argument recovers its declaration. -/
theorem ComparedEtaCompute.instN (R : ComparedEtaCompute D kdepth stage Γ₁ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith (ComparedEtaCompute D kdepth r) Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (ht : VExpr.WF env univs Γ₁ e) :
    ComparedEtaCompute D kdepth (r + stage) Γ (e.inst x k) (out.inst x k) :=
  substitution heq hs hx Rx stage hΓ₁ W ht R

/-- Composition does not increase a shared stage bound. -/
theorem ComparedEtaCompute.trans (R : ComparedEtaCompute D kdepth stage Γ a b)
    (S : ComparedEtaCompute D kdepth stage Γ b c) :
    ComparedEtaCompute D kdepth stage Γ a c := by
  cases stage with
  | zero => exact GuardedKCompute.trans R S
  | succ stage => exact RecoveredEtaWith.trans R S

/-- A displayed beta redex can carry the transformed body computation through
its argument, including the newly admitted recovered comparison guards. -/
theorem ComparedEtaCompute.beta_inst
    (R : ComparedEtaCompute D kdepth stage (A :: Γ) b b')
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx (A :: Γ) (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (Rx : TypeRecoveryWith (ComparedEtaCompute D kdepth r) Γ x A)
    (hb : VExpr.WF env univs (A :: Γ) b) :
    ComparedEtaCompute D kdepth (r + stage) Γ (.app (.lam A b) x) (b'.inst x) :=
  (ComparedEtaCompute.of_staged _ StagedEtaCompute.beta).trans
    (R.instN heq hs hΓ hx Rx .zero hb)

end Lean4Lean.VEnv.Strengthening
