import Lean4Lean.Theory.Typing.Strengthening.TypedIndexedEtaComputation
import Lean4Lean.Theory.Typing.Strengthening.IndexedRecoverySubstitution

/-! # Recoverable substitution with cast-head type computations

Restricted type computations transform only at sort-typed sources. Their
ordinary payload computations and the resulting eta/K/prefix steps still use
the source-typed substitution interface. The finite stage bound is additive.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params] {C C' : List VExpr → VExpr → VExpr → Prop}

/-- The type extension transforms under substitution at a sort-typed source.
That premise types transitive intermediates and the cast payloads. -/
theorem TypeHeadExtension.substitution (heq : env.HasCanonicalEq) (hc : ComputeDescent C)
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀) :
    TypeComputeSubstitutionTo (TypeHeadExtension C) (TypeHeadExtension C') Γ₀ x A₀ := by
  intro k Γ₁ Γ e out hΓ W ht R
  induction R generalizing k Γ with
  | base R =>
    obtain ⟨_, ht⟩ := ht
    exact .base (hsub hΓ W ⟨_, ht⟩ R)
  | castPi R =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, hx⟩ := typeCast_typings henv heq hΓ ⟨_, ht⟩
    have R' := hsub hΓ W ⟨_, hx⟩ R
    simpa only [instN_eq, typeCast_subst, VExpr.subst, Subst.liftN] using TypeHeadExtension.castPi R'
  | castFamily hi ha R =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, hx⟩ := typeCast_typings henv heq hΓ ⟨_, ht⟩
    have R' := hsub hΓ W ⟨_, hx⟩ R
    simp only [inst_mkApps, VExpr.inst] at R'
    simpa only [instN_eq, typeCast_subst, subst_mkApps, VExpr.subst] using
      TypeHeadExtension.castFamily hi (by simpa using ha) R'
  | trans R1 _ ih1 ih2 =>
    obtain ⟨_, ht⟩ := ht
    have hcT : TypeComputeDescent (TypeHeadExtension C) := typeDescent heq hc
    have H := hcT.replay R1 hΓ ht
    exact .trans (ih1 hΓ W ⟨_, ht⟩) (ih2 hΓ W ⟨_, H.hasType.2⟩)

/-- The eta step retains its exact annotation after substituting an argument
whose declaration type is recovered in the target type-computation base. -/
theorem TypedEtaStep.substitution (hc : TypeComputeDescent TC) (hw : ComputeWeakening TC')
    (hsub : TypeComputeSubstitutionTo TC TC' Γ₀ x A₀)
    (hx : env.HasType univs Γ₀ x A₀) (Rx : TypeRecoveryWith TC' Γ₀ x A₀) :
    ComputeSubstitutionTo (TypedEtaStep TC) (TypedEtaStep TC') Γ₀ x A₀ := by
  intro k Γ₁ Γ e out hΓ W ht R
  cases R with
  | eta R =>
    have R' := R.instN_to_of_types hc hw hsub hΓ hx Rx W ht
    simpa only [inst, instVar, Nat.zero_lt_succ, if_true, ← lift_instN_lo] using
      TypedEtaStep.eta R'

/-- Both sorts of endpoint guards and the separate type-backed eta rule
transform using the same recovered argument. -/
theorem TypedIndexedNext.substitution (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hc : ComputeDescent C) (hw : ComputeWeakening C')
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hx : env.HasType univs Γ₀ x A₀) (Rx : TypeRecoveryWith C' Γ₀ x A₀) :
    ComputeSubstitutionTo (TypedIndexedNext D C) (TypedIndexedNext D C') Γ₀ x A₀ := by
  intro k Γ₁ Γ e out hΓ W ht R
  have hcT : TypeComputeDescent (TypeHeadExtension C) := TypeHeadExtension.typeDescent heq hc
  have hwT : ComputeWeakening (TypeHeadExtension C') := TypeHeadExtension.weakening hw
  have hsT : TypeComputeSubstitutionTo (TypeHeadExtension C) (TypeHeadExtension C') Γ₀ x A₀ :=
    TypeHeadExtension.substitution heq hc hsub
  have RxT : TypeRecoveryWith (TypeHeadExtension C') Γ₀ x A₀ := Rx.mono (fun H => .base H)
  rcases R with R | R | R | R
  · exact .inl (IndexedNextComputation.substitution heq hs hc hw hsub hx Rx hΓ W ht R)
  · exact .inr (.inl (R.instN_to heq hs (TypeHeadExtension.comparisonDescent heq hc)
      (fun hΓ W _ _ H => H.instN_to_of_types hcT hwT hsT hΓ hx RxT W) hΓ W ht))
  · exact .inr (.inr (.inl (R.instN_to heq
      (fun hΓ W _ _ H => H.instN_to_of_types hcT hwT hsT hΓ hx RxT W) hΓ W ht)))
  · exact .inr (.inr (.inr (TypedEtaStep.substitution hcT hwT hsT hx RxT hΓ W ht R)))

/-- Substitution of an argument recovered at stage r sends a stage-n path to
stage r+n, including all cast-head recovery inside eta and indexed guards. -/
theorem TypedIndexedEtaCompute.substitution (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith (TypedIndexedEtaCompute D kdepth r) Γ₀ x A₀) :
    ∀ stage, ComputeSubstitutionTo (TypedIndexedEtaCompute D kdepth stage)
      (TypedIndexedEtaCompute D kdepth (r + stage)) Γ₀ x A₀ := by
  intro stage
  induction stage with
  | zero =>
    intro k Γ₁ Γ e out hΓ W ht R
    have R' := CertifiedKCompute.instN R heq hs hΓ hx W ht
    exact TypedIndexedEtaCompute.mono (Nat.zero_le _) R'
  | succ stage ih =>
    have hcs : ComputeDescent (TypedIndexedEtaCompute D kdepth stage) := computeDescent heq hs stage
    have hwt : ComputeWeakening (TypedIndexedEtaCompute D kdepth (r + stage)) :=
      computeWeakening heq (r + stage)
    have Rx' : TypeRecoveryWith (TypedIndexedEtaCompute D kdepth (r + stage)) Γ₀ x A₀ :=
      Rx.mono (fun H => H.mono (Nat.le_add_right r stage))
    intro k Γ₁ Γ e out hΓ W ht R
    exact RecoveredEtaWith.instN_to R (TypedIndexedNext.descends heq hs hcs)
      (TypedIndexedNext.weakens heq hwt)
      (TypedIndexedNext.substitution heq hs hcs hwt ih hx Rx') hΓ hx
      (Rx'.mono (fun H => Or.inl (Or.inl (Or.inl H)))) W ht

/-- Exact result substitution at the additive bound. The argument-recovery
premise remains essential, as in the earlier captured-eta boundary. -/
theorem TypedIndexedEtaCompute.instN (R : TypedIndexedEtaCompute D kdepth stage Γ₁ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith (TypedIndexedEtaCompute D kdepth r) Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (ht : VExpr.WF env univs Γ₁ e) :
    TypedIndexedEtaCompute D kdepth (r + stage) Γ (e.inst x k) (out.inst x k) :=
  substitution heq hs hx Rx stage hΓ W ht R

/-- Composition keeps a shared finite bound. -/
theorem TypedIndexedEtaCompute.trans (R : TypedIndexedEtaCompute D kdepth stage Γ a b)
    (S : TypedIndexedEtaCompute D kdepth stage Γ b c) :
    TypedIndexedEtaCompute D kdepth stage Γ a c := by
  cases stage with
  | zero => exact GuardedKCompute.trans R S
  | succ stage => exact RecoveredEtaWith.trans R S

/-- A displayed beta redex may create the substituted computation, including
type-restricted casts inside recovered annotations and indexed guards. -/
theorem TypedIndexedEtaCompute.beta_inst
    (R : TypedIndexedEtaCompute D kdepth stage (A :: Γ) b b')
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx (A :: Γ) (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (Rx : TypeRecoveryWith (TypedIndexedEtaCompute D kdepth r) Γ x A)
    (hb : VExpr.WF env univs (A :: Γ) b) :
    TypedIndexedEtaCompute D kdepth (r + stage) Γ (.app (.lam A b) x) (b'.inst x) :=
  (TypedIndexedEtaCompute.of_indexed _ (IndexedEtaCompute.of_compared _
    (ComparedEtaCompute.of_staged _ StagedEtaCompute.beta))).trans
      (substitution heq hs hx Rx stage hΓ .zero hb R)

end Lean4Lean.VEnv.Strengthening
