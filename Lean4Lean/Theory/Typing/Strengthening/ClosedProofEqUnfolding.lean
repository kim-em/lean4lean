import Lean4Lean.Theory.Typing.Strengthening.EqRecPrefixComputation
import Lean4Lean.Theory.Typing.Strengthening.ConstructorHeadExposure

/-! # Closed indexed Eq.rec unfolding at a propositional carrier universe

When the carrier universe is equivalent to zero, both endpoints are proofs of
the same proposition. Proof irrelevance therefore aligns even a fresh endpoint.
The entire bare recursor has a closed unfolding, despite Eq being indexed.
This does not unfold Eq.rec at arbitrary carrier universes.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedProofEq
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- The six canonical domains, before any arguments are supplied. -/
def domains (v w : VLevel) : List VExpr :=
  [.sort w, .bvar 0, canonicalEqRecMotive.instL [v, w], canonicalEqRecMinor.instL [v, w],
    .bvar 3, eqApp w (.bvar 4) (.bvar 3) (.bvar 0)]

/-- The closed value ignores the last endpoint and proof and returns the minor. -/
def value (v w : VLevel) : VExpr := wrapLams (domains v w) (.bvar 2)

/-- Proof irrelevance under the complete telescope permits unfolding the bare
constant. The certificate works at every preceding stage, without definitions. -/
theorem compute (heq : env.HasCanonicalEq) (hv : v.WF univs) (hw : w.WF univs)
    (hz : w ≈ .zero) :
    StagedEtaCompute D kdepth (stage + 1) Γ (.const ``Eq.rec [v, w]) (value v w) := by
  have hα : env.HasType univs ((domains v w).reverse ++ Γ) (.bvar 5) (.sort w) :=
    .bvar (.succ (.succ (.succ (.succ (.succ .zero)))))
  have hp := (IsDefEq.sortDF hw (by trivial) hz).defeq hα
  have ha : env.HasType univs ((domains v w).reverse ++ Γ) (.bvar 4) (.bvar 5) :=
    .bvar (.succ (.succ (.succ (.succ .zero))))
  have hb : env.HasType univs ((domains v w).reverse ++ Γ) (.bvar 1) (.bvar 5) :=
    .bvar (.succ .zero)
  have H : ComputedComparison (StagedEtaCompute D kdepth stage) ((domains v w).reverse ++ Γ)
      (.bvar 4) (.bvar 1) := ⟨_, _, 0, .refl, .refl, .proofIrrel hp ha hb⟩
  exact StagedEtaCompute.eqRec_prefix (args := []) (n := 6) (domains := domains v w)
    heq hv hw rfl rfl rfl H

/-- The closed equation is typed at the original canonical recursor type. -/
theorem equation (heq : env.HasCanonicalEq) (hv : v.WF univs) (hw : w.WF univs)
    (hz : w ≈ .zero) :
    env.IsDefEq univs [] (.const ``Eq.rec [v, w]) (value v w)
      (canonicalEqRecType.instL [v, w]) := by
  have R : StagedEtaCompute (Definitions.ofEnv env univs henv) 0 1 []
      (.const ``Eq.rec [v, w]) (value v w) := compute heq hv hw hz
  exact R.simAt heq (Definitions.ofEnv_sound henv) trivial _
    (.const heq.2.2.1 (by simp_all) rfl)

/-- Registration of this indexed closed equation is restricted by the carrier
universe, not by a zero index count. -/
inductive Unfolds : Name → List VLevel → VExpr → Prop where
  | eqRec : v.WF univs → w.WF univs → w ≈ .zero → Unfolds ``Eq.rec [v, w] (value v w)

/-- Each added equation is available in the empty context. -/
theorem Unfolds.equation (heq : env.HasCanonicalEq) (H : Unfolds name levels rhs) :
    env.IsDefEqU univs [] (.const name levels) rhs := by
  cases H with
  | eqRec hv hw hz => exact ⟨_, ClosedProofEq.equation heq hv hw hz⟩

/-- Add the proof-carrier indexed equations to any existing collection. -/
def definitions (heq : env.HasCanonicalEq) (D : Definitions) : Definitions where
  unfolds name levels rhs := D.unfolds name levels rhs ∨ Unfolds name levels rhs
  closed := by
    rintro name levels rhs (h | h)
    · exact D.closed h
    · obtain ⟨_, he⟩ := h.equation heq
      exact he.hasType.2.closedN henv.ordered trivial

/-- The enriched collection is sound at every occurrence context. -/
theorem definitions_sound (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    (definitions heq D).Sound env univs := by
  rintro Γ name levels rhs (h | h)
  · exact hs Γ name levels rhs h
  · obtain ⟨_, he⟩ := h.equation heq
    exact ⟨_, he.weak0 henv.ordered⟩

/-- The canonical recursor head cannot be a projection constructor because it
already carries the installed iota pattern. -/
theorem Unfolds.not_constructor (heq : env.HasCanonicalEq) (H : Unfolds name levels rhs)
    (hi : env.projections s info) : info.ctorName ≠ name := by
  cases H with
  | eqRec _ _ _ =>
    intro hn
    obtain ⟨_, _, _, hp⟩ := heq.2.2.2
    exact (henv.projectionCtorRigid hi).pats _ _ hp
      (by simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using hn.symm)

/-- Existing constructor-sensitive head observations remain sound after adding
the proof-carrier indexed unfolding. -/
theorem definitions_rigid (heq : env.HasCanonicalEq)
    (hD : ConstructorObservation.ConstructorRigid D) :
    ConstructorObservation.ConstructorRigid (definitions heq D) := by
  rintro s info hi levels rhs (h | h)
  · exact hD s info hi levels rhs h
  · exact h.not_constructor heq hi rfl

/-- All supplied arities inherit this closed unfolding by compatible application. -/
theorem apply_compute (heq : env.HasCanonicalEq) (hv : v.WF univs) (hw : w.WF univs)
    (hz : w ≈ .zero) :
    PureObservation.Compute (definitions heq D) (mkApps (.const ``Eq.rec [v, w]) args)
      (mkApps (value v w) args) := by
  have R : PureObservation.Compute (definitions heq D) (.const ``Eq.rec [v, w]) (value v w) :=
    .delta (.inr (.eqRec hv hw hz))
  have applyArgs {f g : VExpr} (R : PureObservation.Compute (definitions heq D) f g) :
      PureObservation.Compute (definitions heq D) (mkApps f args) (mkApps g args) := by
    induction args generalizing f g with
    | nil => exact R
    | cons a args ih => exact ih (.app R .refl)
  exact applyArgs R

end Lean4Lean.VEnv.Strengthening.ClosedProofEq
