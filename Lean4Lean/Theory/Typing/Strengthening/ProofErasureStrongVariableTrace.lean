import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertSortBetaBoundary
import Lean4Lean.Theory.Typing.Strong

/-! # Native variable assignments retain strong conversion premises

This extraction precedes any interpretation of strong equality as computation.
It follows the endpoint typing children already present in every strong rule,
and records the type-equality child of each conversion rule it encounters.
No pattern coverage, strengthening or type-fork joining assumption is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A finite path of actual strong type-conversion premises. Universes may
change from edge to edge. The path does not assert that its edges already have
computational or hereditary interpretations. -/
inductive StrongTypeTrace : List VExpr → VExpr → VExpr → Prop where
  | refl : StrongTypeTrace Γ A A
  | step : StrongTypeTrace Γ A B → env.IsDefEqStrong univs Γ B C (.sort u) →
      StrongTypeTrace Γ A C

private def VariableAssignment (Γ : List VExpr) (e A : VExpr) : Prop :=
  ∀ i, e = .bvar i → ∃ B, Lookup Γ i B ∧ StrongTypeTrace Γ B A

private theorem VariableAssignment.convert (H : VariableAssignment Γ e A)
    (HT : env.IsDefEqStrong univs Γ A B (.sort u)) : VariableAssignment Γ e B := by
  intro i E
  obtain ⟨C, HC, R⟩ := H i E
  exact ⟨C, HC, R.step HT⟩

private theorem variable_assignment
    (H : env.IsDefEqStrong univs Γ a b A) :
    VariableAssignment Γ a A ∧ VariableAssignment Γ b A := by
  induction H with
  | bvar hl hu hA =>
    constructor <;> intro i E <;> cases E <;> exact ⟨_, hl, .refl⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | sortDF | constDF | appDF | projDF | lamDF | forallEDF =>
    constructor <;> intro i E <;> cases E
  | defeqDF hu HT H ihT ih => exact ⟨ih.1.convert HT, ih.2.convert HT⟩
  | beta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ ih8 =>
    exact ⟨(fun i E => by cases E), ih8.1⟩
  | eta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ _ =>
    exact ⟨(fun i E => by cases E), ih6.1⟩
  | proofIrrel h1 h2 h3 _ ih2 ih3 => exact ⟨ih2.1, ih3.1⟩
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ ih8 ih9 => exact ⟨ih8.1, ih9.1⟩
  | pat hp hm he hred hr hall ihe ihred ihall => exact ⟨ihe.1, ihred.1⟩
  | projIota hi ht hg hf iht ihf => exact ⟨iht.1, ihf.1⟩
  | structEta hi hp hx hm hc ihm ihc => exact ⟨ihc.1, ihm.1⟩
  | unitLike hi hp hx hz hm hn ihm ihn => exact ⟨ihm.1, ihn.1⟩

/-- Either variable endpoint of an actual strong derivation has a path from
its literal lookup type to the assigned carrier. The construction is one
structural induction over the original derivation; each path edge is taken
directly from a conversion-rule type child. It synthesizes no new equality by
uniqueness or by translating ordinary typing back into strong typing. -/
theorem strong_variable_assignment_trace
    (H : env.IsDefEqStrong univs Γ a b A) (HE : a = .bvar i ∨ b = .bvar i) :
    ∃ B, Lookup Γ i B ∧ StrongTypeTrace Γ B A :=
  HE.elim (fun E => (variable_assignment H).1 i E) (fun E => (variable_assignment H).2 i E)

/-- A specified native lookup selects the exact starting type of the extracted
path. This retains conversion information independently of any computational
pattern-coverage theorem. -/
theorem strong_variable_native_trace
    (H : env.IsDefEqStrong univs Γ (.bvar i) (.bvar i) A) (hl : Lookup Γ i B) :
    StrongTypeTrace Γ B A := by
  obtain ⟨C, hc, R⟩ := strong_variable_assignment_trace H (.inl rfl)
  cases hl.uniq hc
  exact R

/-- Concatenation retains all original conversion edges without replacing
them by an opaque strong transitivity derivation. -/
theorem StrongTypeTrace.trans (H : StrongTypeTrace Γ A B) (K : StrongTypeTrace Γ B C) :
    StrongTypeTrace Γ A C := by
  induction K with
  | refl => exact H
  | step K HE ih => exact ih.step HE

/-- Reading the finite trace as ordinary type equality is sound once its
initial type is known to be well formed. This is only a forgetful interpretation;
it does not supply computational carrier conversion. -/
theorem StrongTypeTrace.defeq (H : StrongTypeTrace Γ A B)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.IsType univs Γ A) :
    env.IsDefEqU univs Γ A B := by
  induction H with
  | refl => obtain ⟨u, hA⟩ := hA; exact ⟨_, hA⟩
  | step H HE ih => exact ih.trans henv hΓ ⟨_, HE.defeq⟩

/-- To move a property back to the native type, it is enough to interpret each
recorded strong conversion backwards. The handler is the exact remaining
conversion task, not a claim that semantic equality preserves the property. -/
theorem StrongTypeTrace.pullback (H : StrongTypeTrace Γ A B)
    (P : VExpr → Prop)
    (edge : ∀ {X Y u}, env.IsDefEqStrong univs Γ X Y (.sort u) → P Y → P X)
    (HB : P B) : P A := by
  induction H with
  | refl => exact HB
  | step H HE ih => exact ih (edge HE HB)

end Lean4Lean.VEnv.Strengthening
