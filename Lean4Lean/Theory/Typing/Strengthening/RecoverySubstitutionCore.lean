import Lean4Lean.Theory.Typing.Strengthening.RecoveredEtaCore

/-! # Recovery-certified substitution across computational bases

Substituting an argument with a recovered declaration type can change the
computational base of the resulting certificate. This permits finite stages
to grow when eta annotations themselves require staged computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Source-typed substitution transforms one computational base into another
for a fixed argument and declaration. Neither base need be substitution-closed
at its original stage. -/
def ComputeSubstitutionTo (C C' : List VExpr → VExpr → VExpr → Prop)
    (Γ₀ : List VExpr) (x A₀ : VExpr) : Prop :=
  ∀ {k Γ₁ Γ e out}, OnCtx Γ₁ (env.IsType univs) → Ctx.InstN Γ₀ x A₀ k Γ₁ Γ →
    VExpr.WF env univs Γ₁ e → C Γ₁ e out → C' Γ (e.inst x k) (out.inst x k)

/-- Type recovery only substitutes computation paths whose source is a type.
This interface allows a computational base with sort-source replay only. -/
def TypeComputeSubstitutionTo (C C' : List VExpr → VExpr → VExpr → Prop)
    (Γ₀ : List VExpr) (x A₀ : VExpr) : Prop :=
  ∀ {k Γ₁ Γ e out}, OnCtx Γ₁ (env.IsType univs) → Ctx.InstN Γ₀ x A₀ k Γ₁ Γ →
    env.IsType univs Γ₁ e → C Γ₁ e out → C' Γ (e.inst x k) (out.inst x k)

/-- Ordinary source-typed substitution supplies the restricted type interface. -/
theorem ComputeSubstitutionTo.types (H : ComputeSubstitutionTo C C' Γ₀ x A₀) :
    TypeComputeSubstitutionTo C C' Γ₀ x A₀ := by
  intro k Γ₁ Γ e out hΓ W ht R
  obtain ⟨_, ht⟩ := ht
  exact H hΓ W ⟨_, ht⟩ R

/-- The substituted lookup uses the argument's target-base recovery; other
lookups use weakening under each subsequent binder. -/
theorem TypeRecoveryWith.lookup_instN (hw : ComputeWeakening C)
    (Rx : TypeRecoveryWith C Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (h : Lookup Γ₁ i T) :
    TypeRecoveryWith C Γ ((.bvar i : VExpr).inst x k) (T.inst x k) := by
  dsimp [inst]
  induction W generalizing i T with
  | zero =>
    cases h with simp [inst_lift]
    | zero => exact Rx
    | succ h => exact .bvar h
  | succ _ ih =>
    cases h with (simp; rw [Nat.add_comm, ← VExpr.liftN_instN_lo (hj := Nat.zero_le _)])
    | zero => exact .bvar .zero
    | succ h => exact TypeRecoveryWith.weakN hw .one (ih h)

/-- Exact output recovery survives substitution when the argument recovers its
declaration in the target base and all source computations transform there. -/
theorem TypeRecoveryWith.instN_to_of_types (R : TypeRecoveryWith C Γ₁ e T)
    (hc : TypeComputeDescent C) (hw : ComputeWeakening C')
    (hsub : TypeComputeSubstitutionTo C C' Γ₀ x A₀)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith C' Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ht : VExpr.WF env univs Γ₁ e) :
    TypeRecoveryWith C' Γ (e.inst x k) (T.inst x k) := by
  induction R generalizing k Γ with
  | sort hu => exact .sort hu
  | const hd hl hn =>
    rw [((henv.ordered.closedC hd).instL).instN_eq (Nat.zero_le _)]
    exact .const hd hl hn
  | bvar h => exact TypeRecoveryWith.lookup_instN hw Rx W h
  | lam _ ih =>
    obtain ⟨hA, hb⟩ := ht.lam_inv henv hΓ₁
    exact .lam (ih ⟨hΓ₁, hA⟩ W.succ hb)
  | app _ ih =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ₁
    exact VExpr.inst_inst_hi .. ▸ TypeRecoveryWith.app (ih hΓ₁ W ⟨_, hf⟩)
  | forallE hA hB => exact .forallE (hA.instN henv W hx) (hB.instN henv W.succ hx)
  | @proj s info Γs m ls args i F hi _ hF ih =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ₁ ht
    have hclosed := henv.ordered.closedC (henv.ordered.projectionConstructor hi)
    have hF' := VProjectionInfo.fieldType_inst_some info hclosed hF (value := x) (k := k)
    simp only [List.map_take] at hF'
    have hm' := ih hΓ₁ W ⟨_, hm.hasType.2⟩
    simp only [inst_mkApps, inst] at hm'
    exact TypeRecoveryWith.proj hi hm' hF'
  | convert R RC ih =>
    have heT := R.hasType_of_types hc hΓ₁ ht
    obtain ⟨_, hT⟩ := heT.isType henv hΓ₁
    exact .convert (ih hΓ₁ W ht) (hsub hΓ₁ W ⟨_, hT⟩ RC)

/-- Ordinary descent and substitution remain sufficient through the restricted
type interfaces; existing clients need no changes. -/
theorem TypeRecoveryWith.instN_to (R : TypeRecoveryWith C Γ₁ e T)
    (hc : ComputeDescent C) (hw : ComputeWeakening C')
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith C' Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ht : VExpr.WF env univs Γ₁ e) :
    TypeRecoveryWith C' Γ (e.inst x k) (T.inst x k) :=
  R.instN_to_of_types hc.types hw hsub.types hΓ₁ hx Rx W ht

/-- Compatible eta computation transforms under the same certified argument.
Eta preserves its recovered Pi, and replay types all transitive intermediates. -/
theorem RecoveredEtaWith.instN_to (R : RecoveredEtaWith C Γ₁ e out)
    (hc : ComputeDescent C) (hw : ComputeWeakening C')
    (hsub : ComputeSubstitutionTo C C' Γ₀ x A₀)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecoveryWith C' Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ht : VExpr.WF env univs Γ₁ e) :
    RecoveredEtaWith C' Γ (e.inst x k) (out.inst x k) := by
  induction R generalizing k Γ with
  | base R => exact .base (hsub hΓ₁ W ht R)
  | eta R =>
    have R' := R.instN_to hc hw hsub hΓ₁ hx Rx W ht
    simpa only [inst, instVar, Nat.zero_lt_succ, if_true, ← lift_instN_lo] using
      RecoveredEtaWith.eta R'
  | trans R1 _ ih1 ih2 =>
    obtain ⟨T, ht⟩ := ht
    have hmid := (R1.simAt hc hΓ₁ T ht).hasType.2
    exact .trans (ih1 hΓ₁ W ⟨_, ht⟩) (ih2 hΓ₁ W ⟨_, hmid⟩)
  | app _ _ ih1 ih2 =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ₁
    exact .app (ih1 hΓ₁ W ⟨_, hf⟩) (ih2 hΓ₁ W ⟨_, ha⟩)
  | lam _ _ ih1 ih2 =>
    obtain ⟨hA, hb⟩ := ht.lam_inv henv hΓ₁
    exact .lam (ih1 hΓ₁ W (hA.elim fun _ h => ⟨_, h⟩)) (ih2 ⟨hΓ₁, hA⟩ W.succ hb)
  | forallE _ _ ih1 ih2 =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨hA, hB⟩ := HasType.forallE_inv henv.ordered ht
    exact .forallE (ih1 hΓ₁ W (hA.elim fun _ h => ⟨_, h⟩))
      (ih2 ⟨hΓ₁, hA⟩ W.succ (hB.elim fun _ h => ⟨_, h⟩))
  | proj _ ih =>
    obtain ⟨_, ht⟩ := ht
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ₁ ht
    exact .proj (ih hΓ₁ W ⟨_, hm.hasType.2⟩)

end Lean4Lean.VEnv.Strengthening
