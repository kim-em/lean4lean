import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStrongBoundedInstantiation

/-! # Neutral application frames retain actual smaller strong children

Endpoint typing is represented by a side of its original equality, avoiding
the two-rank symmetry/transitivity reconstruction. A variable-headed application
has actual function and argument children strictly below its parent's rank.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- One endpoint of a strong equality, at the equality's original rank. This
is typing evidence, but does not assert a reflexive derivation at that rank. -/
def BoundedEndpoint (env : VEnv) (U n : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  ∃ a b, StrongBounded env U n Γ a b A ∧ (e = a ∨ e = b)

/-- Keeping the original left endpoint costs no additional rank. -/
theorem BoundedEndpoint.left (H : StrongBounded env U n Γ a b A) :
    BoundedEndpoint env U n Γ a A := ⟨_, _, H, .inl rfl⟩

/-- Keeping the original right endpoint costs no additional rank. -/
theorem BoundedEndpoint.right (H : StrongBounded env U n Γ a b A) :
    BoundedEndpoint env U n Γ b A := ⟨_, _, H, .inr rfl⟩

/-- A variable endpoint's native conversion trace stays strictly below the
original equality's rank, without first extracting its reflexive typing. -/
theorem BoundedEndpoint.variable_trace
    (H : BoundedEndpoint env U n Γ (.bvar i) A) (hl : Lookup Γ i B) :
    BoundedTypeTrace env U n Γ B A := by
  obtain ⟨a, b, HE, hside⟩ := H
  obtain ⟨C, hc, R⟩ := HE.variable_assignment_trace
    (hside.elim (fun E => .inl E.symm) (fun E => .inr E.symm))
  cases hl.uniq hc
  exact R

/-- The actual source premises for a neutral application. The function and
argument remain endpoints of their original strong equalities. Domain and
codomain formation are retained at the same strictly smaller rank. -/
inductive BoundedNeutralFrame (env : VEnv) (U bound : Nat)
    (Γ : List VExpr) (i : Nat) (x : VExpr) : Prop where
  | intro (hlt : k < bound) (hu : u.WF U) (hv : v.WF U)
      (hA : StrongBounded env U k Γ A A (.sort u))
      (hB : StrongBounded env U k (A::Γ) B B (.sort v))
      (hF : BoundedEndpoint env U k Γ (.bvar i) (.forallE A B))
      (hX : BoundedEndpoint env U k Γ x A) : BoundedNeutralFrame env U bound Γ i x

/-- Increasing the outer bound changes none of the recorded premise ranks. -/
theorem BoundedNeutralFrame.mono (H : BoundedNeutralFrame env U n Γ i x) (hle : n ≤ m) :
    BoundedNeutralFrame env U m Γ i x := by
  cases H with
  | intro hlt hu hv hA hB hF hX => exact .intro (Nat.lt_of_lt_of_le hlt hle) hu hv hA hB hF hX

private def NeutralAssignment (env : VEnv) (U n : Nat) (Γ : List VExpr) (e : VExpr) : Prop :=
  ∀ i x, e = .app (.bvar i) x → BoundedNeutralFrame env U n Γ i x

private theorem NeutralAssignment.mono (H : NeutralAssignment env U n Γ e) (hle : n ≤ m) :
    NeutralAssignment env U m Γ e := fun i x E => (H i x E).mono hle

private theorem bounded_neutral_assignment (H : StrongBounded env U n Γ a b A) :
    NeutralAssignment env U n Γ a ∧ NeutralAssignment env U n Γ b := by
  induction H with
  | bvar | sortDF | constDF | projDF | lamDF | forallEDF =>
    constructor <;> intro i x E <;> cases E
  | appDF hu hv hA hB hF hX hBI ihA ihB ihF ihX ihBI =>
    constructor
    · intro i x E
      cases E
      exact .intro (Nat.lt_succ_self _) hu hv hA hB (.left hF) (.left hX)
    · intro i x E
      cases E
      exact .intro (Nat.lt_succ_self _) hu hv hA hB (.right hF) (.right hX)
  | symm _ ih => exact ⟨ih.2.mono (Nat.le_succ _), ih.1.mono (Nat.le_succ _)⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1.mono (Nat.le_succ _), ih₂.2.mono (Nat.le_succ _)⟩
  | defeqDF hu HT H ihT ih => exact ⟨ih.1.mono (Nat.le_succ _), ih.2.mono (Nat.le_succ _)⟩
  | beta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ ih8 =>
    exact ⟨(fun i x E => by cases E), ih8.1.mono (Nat.le_succ _)⟩
  | eta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ _ =>
    exact ⟨(fun i x E => by cases E), ih6.1.mono (Nat.le_succ _)⟩
  | proofIrrel h1 h2 h3 _ ih2 ih3 =>
    exact ⟨ih2.1.mono (Nat.le_succ _), ih3.1.mono (Nat.le_succ _)⟩
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ ih8 ih9 =>
    exact ⟨ih8.1.mono (Nat.le_succ _), ih9.1.mono (Nat.le_succ _)⟩
  | pat hp hm he hred hr hall ihe ihred ihall =>
    exact ⟨ihe.1.mono (Nat.le_succ _), ihred.1.mono (Nat.le_succ _)⟩
  | projIota hi ht hg hf iht ihf =>
    exact ⟨iht.1.mono (Nat.le_succ _), ihf.1.mono (Nat.le_succ _)⟩
  | structEta hi hp hx hm hc ihm ihc =>
    exact ⟨ihc.1.mono (Nat.le_succ _), ihm.1.mono (Nat.le_succ _)⟩
  | unitLike hi hp hx hz hm hn ihm ihn =>
    exact ⟨ihm.1.mono (Nat.le_succ _), ihn.1.mono (Nat.le_succ _)⟩
  | raise hlt H ih => exact ⟨ih.1.mono (Nat.le_of_lt hlt), ih.2.mono (Nat.le_of_lt hlt)⟩

/-- Either neutral-application endpoint of any strong rule has an actual
smaller-premise frame. Beta's lambda-headed source cannot be this endpoint;
its reduct is handled by the reduct-typing child already present in the rule. -/
theorem StrongBounded.neutral_frame (H : StrongBounded env U n Γ a b A)
    (HE : a = .app (.bvar i) x ∨ b = .app (.bvar i) x) :
    BoundedNeutralFrame env U n Γ i x :=
  HE.elim (fun E => (bounded_neutral_assignment H).1 i x E)
    (fun E => (bounded_neutral_assignment H).2 i x E)

/-- Reading an endpoint view preserves its original bound during inversion. -/
theorem BoundedEndpoint.neutral_frame
    (H : BoundedEndpoint env U n Γ (.app (.bvar i) x) A) :
    BoundedNeutralFrame env U n Γ i x := by
  obtain ⟨a, b, HE, hside⟩ := H
  exact HE.neutral_frame (hside.elim (fun E => .inl E.symm) (fun E => .inr E.symm))

/-- The assigned function domain and argument evidence lie at k<n; every
native-to-assigned function-type conversion edge lies at j<k. This exposes
two strict levels of the original derivation without reconstructing typings.
It does not project domains through intermediate non-Pi conversion types. -/
theorem BoundedNeutralFrame.native_trace
    (H : BoundedNeutralFrame env U n Γ i x) (hl : Lookup Γ i T) :
    ∃ k, k < n ∧ ∃ A B u v, u.WF U ∧ v.WF U ∧
      StrongBounded env U k Γ A A (.sort u) ∧
      StrongBounded env U k (A::Γ) B B (.sort v) ∧
      BoundedEndpoint env U k Γ x A ∧ BoundedTypeTrace env U k Γ T (.forallE A B) := by
  cases H with
  | intro hlt hu hv hA hB hF hX => exact ⟨_, hlt, _, _, _, _, hu, hv, hA, hB, hX, hF.variable_trace hl⟩

/-- The assigned-function case and every conversion handler can use only
ranks below the original neutral application's bound. The finite native trace
then returns the property to the lookup type. The handlers remain hypotheses;
this is not a proof of general hereditary carrier transport. -/
theorem StrongBounded.neutral_native_pullback
    (H : StrongBounded env U n Γ a b C)
    (HE : a = .app (.bvar i) x ∨ b = .app (.bvar i) x) (hl : Lookup Γ i T)
    (P : VExpr → Prop)
    (assigned : ∀ {k A B u v}, k < n → u.WF U → v.WF U →
      StrongBounded env U k Γ A A (.sort u) →
      StrongBounded env U k (A::Γ) B B (.sort v) →
      BoundedEndpoint env U k Γ x A → P (.forallE A B))
    (edge : ∀ {j X Y u}, j < n → StrongBounded env U j Γ X Y (.sort u) → P Y → P X) :
    P T := by
  obtain ⟨k, hk, A, B, u, v, hu, hv, hA, hB, hX, R⟩ := (H.neutral_frame HE).native_trace hl
  exact R.pullback P (fun hj HE => edge (Nat.lt_trans hj hk) HE)
    (assigned hk hu hv hA hB hX)

/-- A candidate that only inspects literal Pi syntax. Non-Pi intermediate
types satisfy this predicate vacuously, which makes it unsuitable for the
general conversion-edge handler unless every relevant domain already has R. -/
def LiteralPiDomain (R : VExpr → Prop) (T : VExpr) : Prop :=
  ∀ A B, T = .forallE A B → R A

/-- A literal-Pi-only conversion handler already forces R for every domain
of a strongly typed Pi. A single identity-beta expansion is non-Pi syntax,
but convertible to the original type at an explicit finite rank. This is a
checked obstruction to using vacuous truth for non-Pi intermediate types. -/
theorem literal_pi_transport_forces_domain
    (ht : StrongBounded env U n Γ (.forallE A B) (.forallE A B) (.sort u))
    (hu : u.WF U) (R : VExpr → Prop)
    (edge : ∀ {j X Y v}, j < n+5 → StrongBounded env U j Γ X Y (.sort v) →
      LiteralPiDomain R Y → LiteralPiDomain R X) : R A := by
  have hsort : StrongBounded env U (n+2) Γ (.sort u) (.sort u) (.sort u.succ) :=
    (StrongBounded.sortDF (n := 0) hu hu rfl).mono (by omega)
  have hsort' : StrongBounded env U (n+2) (.sort u::Γ) (.sort u) (.sort u) (.sort u.succ) :=
    (StrongBounded.sortDF (n := 0) hu hu rfl).mono (by omega)
  have hvar : StrongBounded env U (n+2) (.sort u::Γ) (.bvar 0) (.bvar 0) (.sort u) := by
    have hv : StrongBounded env U 2 (.sort u::Γ) (.bvar 0) (.bvar 0) (.sort u) :=
      .bvar .zero (show u.succ.WF U from hu) (StrongBounded.sortDF (n := 0) hu hu rfl)
    exact hv.mono (by omega)
  have hb : StrongBounded env U (n+3) Γ
      (.app (.lam (.sort u) (.bvar 0)) (.forallE A B)) (.forallE A B) (.sort u) := by
    simpa [VExpr.inst, instVar_zero] using
      (StrongBounded.beta (e := .bvar 0) (e' := .forallE A B) (B := .sort u)
        (show u.succ.WF U from hu) (show u.succ.WF U from hu) hsort hsort' hvar (ht.mono (m := n+2) (by omega)) hsort (by simpa [VExpr.inst, instVar_zero] using ht.mono (m := n+2) (by omega)))
  have H := edge (j := n+4) (by omega) (StrongBounded.symm hb)
    (by intro X Y E; cases E)
  exact H A B rfl

/-- In particular, even a bounded handler for the vacuous literal-Pi
predicate with false domain property is impossible once a typed Pi is present.
This refutes that candidate motive, not strengthening or general conversion. -/
theorem no_false_literal_pi_transport
    (ht : StrongBounded env U n Γ (.forallE A B) (.forallE A B) (.sort u))
    (hu : u.WF U) :
    ¬ (∀ {j X Y v}, j < n+5 → StrongBounded env U j Γ X Y (.sort v) →
      LiteralPiDomain (fun _ => False) Y → LiteralPiDomain (fun _ => False) X) :=
  fun edge => literal_pi_transport_forces_domain ht hu (fun _ => False) edge

end Lean4Lean.VEnv.Strengthening
