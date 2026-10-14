import Lean4Lean.Theory.Typing.Strengthening.StructureEtaReadout

/-! # Deterministic registry-selected structure equations

The earlier closed structure collection accepts any registration certificate.
For computational joining, select the recursor datum from the actual registry.
This makes its unfolding unique at fixed universes, using projection metadata
uniqueness and pattern uniqueness. The selected equations retain soundness and
all fully supplied projection-program computations. Confluence of the augmented
computation relation is not asserted here.
-/
namespace Lean4Lean.VEnv.Strengthening.RegisteredStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
open PureObservation
variable [Params] {D : Definitions}

/-- A closed structure program selected by the actual recursor lookup.
Registration and the recursor's name are recovered from that lookup. -/
inductive Unfolds : Name → List VLevel → VExpr → Prop where
  | intro {r : (ClosedStructure.pattern data info).RHS × (ClosedStructure.pattern data info).Check} :
      recursorData name = some data →
      (∀ l ∈ levels, l.WF univs) → levels.length = data.uvars →
      env.projections (ClosedStructure.family data) info → info.nindices = 0 →
      ClosedStructure.Admissible env univs data info levels →
      Pat _ r → CheckFromTyping env univs _ r levels →
      Unfolds name levels
        (ClosedStructure.value data info levels r.1 (ClosedStructure.domainsOf data levels))

/-- Registry selection only restricts the already proved closed equations. -/
theorem Unfolds.closedStructure (H : Unfolds name levels rhs) :
    ClosedStructure.Unfolds name levels rhs := by
  cases H with
  | intro hreg hw hl hi hx hz hp hc =>
    obtain ⟨hr, hname⟩ := recursorData_registered hreg
    rw [← hname]
    exact .intro hr hw hl hi hx hz hp hc

/-- A fixed name and universe list select exactly one raw projection program.
No computation, conversion or normalization is needed to compare the outputs. -/
theorem Unfolds.unique (H1 : Unfolds name levels rhs1) (H2 : Unfolds name levels rhs2) :
    rhs1 = rhs2 := by
  cases H1 with
  | intro hreg1 hw1 hl1 hi1 hx1 hz1 hp1 hc1 =>
    cases H2 with
    | intro hreg2 hw2 hl2 hi2 hx2 hz2 hp2 hc2 =>
      cases Option.some.inj (hreg1.symm.trans hreg2)
      cases henv.ordered.projections_unique hi1 hi2
      have he := (pat_uniq hp1 hp2 .refl (Pattern.inter_self _)).2.2
      cases he
      rfl

/-- Include the deterministic structure programs alongside existing equations. -/
def definitions (D : Definitions) : Definitions where
  unfolds name levels rhs := D.unfolds name levels rhs ∨ Unfolds name levels rhs
  closed := by
    rintro name levels rhs (H | H)
    · exact D.closed H
    · obtain ⟨_, he⟩ := H.closedStructure.equation
      exact he.hasType.2.closedN henv (by trivial)

/-- Every selected equation remains sound in arbitrary well-formed contexts. -/
theorem definitions_sound (hs : D.Sound env univs) : (definitions D).Sound env univs := by
  rintro Γ name levels rhs (H | H)
  · exact hs Γ name levels rhs H
  · obtain ⟨_, he⟩ := H.closedStructure.equation
    exact ⟨_, he.weak0 henv⟩

/-- The previous constructor rigidity condition survives registry selection. -/
theorem definitions_rigid (hD : ConstructorObservation.ConstructorRigid D) :
    ConstructorObservation.ConstructorRigid (definitions D) := by
  rintro family info hi levels rhs (H | H)
  · exact hD family info hi levels rhs H
  · exact H.closedStructure.not_constructor hi rfl

/-- The selected collection embeds into the original closed structure one. -/
theorem definitions_inclusion (H : (definitions D).unfolds name levels rhs) :
    (ClosedStructure.definitions D).unfolds name levels rhs :=
  H.elim Or.inl (fun H => .inr H.closedStructure)

/-- Full saturation of a registry-selected unfolding reaches its original
projection program. Restricting the collection loses none of these actual roots. -/
theorem saturated_compute
    {r : (ClosedStructure.pattern data info).RHS × (ClosedStructure.pattern data info).Check}
    (hreg : recursorData name = some data)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = data.uvars)
    (hi : env.projections (ClosedStructure.family data) info) (hx : info.nindices = 0)
    (hz : ClosedStructure.Admissible env univs data info levels)
    (hp : Pat _ r) (hc : CheckFromTyping env univs _ r levels)
    (ha : args.length = data.majorOffset + 1) :
    Compute (definitions D) (mkApps (.const name levels) args)
      ((ClosedStructure.body data info levels r.1).instOuter args) := by
  obtain ⟨hr, hname⟩ := recursorData_registered hreg
  obtain ⟨type, htype⟩ := hr.recursorType_exists
  have hdom := (ClosedStructure.type_shape (levels := levels) htype).2
  have R := ClosedQuot.compute_mkApps (D := definitions D)
    (Compute.delta (.inr (Unfolds.intro hreg hw hl hi hx hz hp hc))) args
  apply R.trans
  have HB := BetaRed.mkApps_wrapLams (ClosedStructure.domainsOf data levels)
    (ClosedStructure.body data info levels r.1) args (by omega)
  apply Compute.of_beta
  simpa only [ClosedStructure.value, ← ha, hdom, List.take_length,
    List.drop_length, mkApps_nil] using HB

/-- Supplying the prefix and major has the same exact projected RHS as before. -/
theorem supplied_compute
    {r : (ClosedStructure.pattern data info).RHS × (ClosedStructure.pattern data info).Check}
    (hreg : recursorData name = some data)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = data.uvars)
    (hi : env.projections (ClosedStructure.family data) info) (hx : info.nindices = 0)
    (hz : ClosedStructure.Admissible env univs data info levels)
    (hp : Pat _ r) (hc : CheckFromTyping env univs _ r levels)
    (ha : args.length = data.majorOffset) :
    Compute (definitions D) (.app (mkApps (.const name levels) args) major)
      (ClosedStructure.suppliedBody data info levels r.1 args ha major) := by
  have R := saturated_compute (D := D) hreg hw hl hi hx hz hp hc
    (args := args ++ [major]) (by simp [ha])
  simpa only [mkApps_append, mkApps_cons, mkApps_nil,
    ClosedStructure.body_instOuter ha] using R

end Lean4Lean.VEnv.Strengthening.RegisteredStructure
