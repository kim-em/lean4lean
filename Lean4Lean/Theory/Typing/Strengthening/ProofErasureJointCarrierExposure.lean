import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryJoinBoundary

/-! # Carrier guards only add power at exposed structure or function types

Every joint carrier guard either gives ordinary common-mode comparison, or its
carrier computes to a registered unindexed structure or a displayed Pi. The
factorization retains the endpoint guard at the exposed carrier. In particular,
variable-headed carriers add no checking power, even when their arguments have
arbitrary computations. Their guards transfer to any newly recovered domain;
no literal join or type-comparison certificate is needed for that case.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape

private def variableHead : ProofShape → Option Nat
  | .bvar i => some i
  | .app f _ => variableHead f
  | _ => none

private theorem variableHead_mkApps (f : ProofShape) (args : List ProofShape) :
    variableHead (mkApps f args) = variableHead f := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

private theorem bvar_spine_app (E : mkApps (.bvar i) args = .app f a) :
    ∃ args₀, args = args₀ ++ [a] ∧ f = mkApps (.bvar i) args₀ := by
  induction args using List.snoc_induction with
  | nil => cases E
  | snoc args x _ =>
    rw [mkApps_snoc] at E
    obtain ⟨rfl, rfl⟩ := ProofShape.app.inj E
    exact ⟨args, rfl, rfl⟩

private theorem bvar_spine_not_primitive (args : List ProofShape) :
    ¬ PrimitiveHead (mkApps (.bvar i) args) := by
  induction args using List.snoc_induction with
  | nil => exact id
  | snoc args x ih => simpa only [mkApps_snoc, PrimitiveHead] using ih

/-- Beta computation of a variable-headed spine changes only its arguments,
retaining the variable index and arity without any normality assumption. -/
theorem BetaRed.bvar_spine (R : BetaRed (mkApps (.bvar i) args) out) :
    ∃ args', out = mkApps (.bvar i) args' ∧ List.Forall₂ BetaRed args args' := by
  generalize E : mkApps (.bvar i) args = source at R
  induction R generalizing args with
  | refl => exact ⟨args, E.symm, Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨args₁, rfl, H₁⟩ := ih₁ E
    obtain ⟨args₂, HE, H₂⟩ := ih₂ rfl
    exact ⟨_, HE, Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') H₁ H₂⟩
  | app Rf Ra ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := bvar_spine_app E
    obtain ⟨args', rfl, H⟩ := ihf rfl
    exact ⟨args' ++ [_], mkApps_snoc.symm, H.append' (.cons Ra .nil)⟩
  | proj | lam | forallE | beta =>
    have H := congrArg variableHead E
    simp only [variableHead_mkApps, variableHead] at H
    cases H

/-- Constant/projection-headed primitives leave every variable-headed spine
intact. All argument computations remain at the original raw context. -/
theorem ScopedCompute.bvar_spine
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (mkApps (.bvar i) args) out) :
    ∃ args', out = mkApps (.bvar i) args' ∧
      List.Forall₂ (ScopedCompute Step Δ) args args' := by
  generalize E : mkApps (.bvar i) args = source at R
  induction R generalizing args with
  | base H => exact (bvar_spine_not_primitive args (E ▸ hhead H)).elim
  | beta H =>
    cases E
    obtain ⟨args', HE, HA⟩ := H.bvar_spine
    exact ⟨_, HE, HA.imp (fun _ _ h => .beta h)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨args₁, rfl, H₁⟩ := ih₁ E
    obtain ⟨args₂, HE, H₂⟩ := ih₂ rfl
    exact ⟨_, HE, Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') H₁ H₂⟩
  | app Rf Ra ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := bvar_spine_app E
    obtain ⟨args', rfl, H⟩ := ihf rfl
    exact ⟨args' ++ [_], mkApps_snoc.symm, H.append' (.cons Ra .nil)⟩
  | proj | lam | forallE =>
    have H := congrArg variableHead E
    simp only [variableHead_mkApps, variableHead] at H
    cases H

variable [Params]

/-- The only carrier shapes at which the joint grammar adds rules beyond
ordinary endpoint comparison: registered unindexed structures and Pi types.
This describes syntax and metadata, not arbitrary definitionally equal types. -/
inductive CarrierExposure : ProofShape → Prop where
  | record (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams) : CarrierExposure (mkApps (.const family ls) ps)
  | function : CarrierExposure (.forallE A B)

/-- Every carrier guard factors through ordinary endpoint checking or an
actually exposed structural carrier. Symmetry and endpoint reductions stay in
the resulting guard; successive carrier computations compose into one path. -/
theorem JointCarrierGuard.checked_or_exposed
    (H : JointCarrierGuard Step Δ A a b) :
    JointCompare Step Δ true a b ∨
      ∃ B, ScopedCompute Step Δ A B ∧ CarrierExposure B ∧ JointCarrierGuard Step Δ B a b := by
  change JointCheck Step Δ (.carrier A) a b at H
  generalize E : JointCheckKind.carrier A = kind at H
  induction H generalizing A with
  | carrierChecked H => exact .inl H
  | carrierSubsingleton H =>
    cases E
    refine .inr ⟨_, .refl, ?_, .carrierSubsingleton H⟩
    cases H with
    | unit hi hx hf hp => exact .record hi hx hp
    | forallE => exact .function
  | carrierFunction S H =>
    cases E
    exact .inr ⟨_, .refl, .function, .carrierFunction S H⟩
  | carrierSymm _ ih =>
    rcases ih E with HC | ⟨B, R, HB, H⟩
    · exact .inl (.symm HC)
    · exact .inr ⟨B, R, HB, .carrierSymm H⟩
  | carrierCompute R _ ih =>
    cases E
    rcases ih rfl with HC | ⟨B, R', HB, H⟩
    · exact .inl HC
    · exact .inr ⟨B, R.trans R', HB, H⟩
  | carrierReduce Ra Rb _ ih =>
    rcases ih E with HC | ⟨B, R, HB, H⟩
    · exact .inl (.compute Ra Rb HC)
    · exact .inr ⟨B, R, HB, .carrierReduce Ra Rb H⟩
  | carrierIntro hi hx hp hadm H =>
    cases E
    exact .inr ⟨_, .refl, .record hi hx hp, .carrierIntro hi hx hp hadm H⟩
  | carrierNested hi hx hp hadm HT H =>
    cases E
    exact .inr ⟨_, .refl, .record hi hx hp, .carrierNested hi hx hp hadm HT H⟩
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- A carrier with no path to a structural checking shape contributes no extra
checking power. This criterion needs no confluence, normality or original typing. -/
theorem JointCarrierGuard.checked_of_no_exposure
    (hn : ∀ {B}, ScopedCompute Step Δ A B → ¬ CarrierExposure B)
    (H : JointCarrierGuard Step Δ A a b) : JointCompare Step Δ true a b := by
  rcases H.checked_or_exposed with HC | ⟨B, R, HB, _⟩
  · exact HC
  · exact (hn R HB).elim

/-- At a variable-headed type, carrier checking is ordinary common-mode
comparison, even if its arguments reduce or diverge. -/
theorem JointCarrierGuard.bvar_spine_checked
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCarrierGuard Step Δ (mkApps (.bvar i) args) a b) :
    JointCompare Step Δ true a b := by
  apply H.checked_of_no_exposure
  intro B R HB
  obtain ⟨args', rfl, _⟩ := R.bvar_spine hhead
  generalize E : mkApps (.bvar i) args' = out at HB
  cases HB with
  | record | function =>
    have HE := congrArg variableHead E
    simp only [variableHead_mkApps, variableHead] at HE
    cases HE

/-- A guard at a variable-headed assigned domain transfers to any selected
recovered domain. Sound use supplies endpoint typings at that selected domain;
this raw certificate conversion asserts no equality between the carrier types. -/
theorem JointCarrierGuard.bvar_spine_reindex
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCarrierGuard Step Δ (mkApps (.bvar i) args) a b) :
    JointCarrierGuard Step Δ B a b := .carrierChecked (H.bvar_spine_checked hhead)

end ProofShape
end Lean4Lean.VEnv.Strengthening
