import Lean4Lean.Theory.Typing.AnchoredOriginalWorldComputationalPrefix

/-! The shared rigid-family F clause at an arbitrary actual constant endpoint.
Its real constant prefix selects the primitive source; exact assigned support
is restored through that prefix using only lower formation/equality calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private prefixCalls from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantStep
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private prefixProvenance from Lean4Lean.Theory.Typing.AnchoredOriginalWorldComputationalPrefix
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- No current-node F or R is invoked. The finite original prefix preserves
the displayed levels; `primitiveWorld` separately keeps the stored header seed
and frozen demand levels, including a right endpoint of genuine `constDF`. -/
theorem RichRigidConstantInput.computationalWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {plan : RigidFamilySpine n} {support : Profile n}
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (provenance : EndpointProvenance context node)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (sourceClosed : ∀ source, source ≤ env → P source)
    (queryReady : ControlledStoredQuery controls frontier
      (.observation (input.observation node locals σ)))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node baseline]))
    (replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node baseline])) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target node
        locals σ τ available (.singleton (plan.atom name frozenLevels [])),
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)) := by
  let head := constantPrefix node
  obtain ⟨route⟩ := head.directLocated provenance.location
  have cost := head.route.dependency_cost_le controls.ordered baselineEnvironment
  have parentRelation : originalCallWorld controls .fundamental (.ref head.reference) baseline =
      originalCallWorld controls .fundamental node baseline ∨
      WorldBelow strata.rules.length (originalCallWorld controls .fundamental (.ref head.reference) baseline)
        (originalCallWorld controls .fundamental node baseline) := by
    rcases Nat.eq_or_lt_of_le cost with same | smaller
    · left
      simp only [originalCallWorld, same]
    · exact .inr (original_child (richSchedule_strict smaller _ _) _ _ _ _ _)
  have funded : ∀ calls, CallBelow strata.rules.length calls
      (frontier ++ [originalCallWorld controls .fundamental (.ref head.reference) baseline]) →
      CallBelow strata.rules.length calls (frontier ++ [originalCallWorld controls .fundamental node baseline]) := by
    intro calls lower
    rcases parentRelation with same | smaller
    · simpa only [same] using lower
    · exact lower.trans (prefixCalls frontier (calls :=
        [originalCallWorld controls .fundamental (.ref head.reference) baseline])
        (by intro child member; cases List.mem_singleton.mp member; exact smaller))
  have primitivePaid : Sponsored frontier
      [originalCallWorld controls .fundamental (.ref head.reference) baseline] := by
    rcases parentRelation with same | smaller
    · simpa only [same] using paid
    · exact singletonSponsoredBelow paid smaller
  have headerPaid := singletonSponsoredBelow paid
    (originalClosedHeader_below controls input.origin
      (.ref (input.origin.familyHeader input.seedWF).reference) node baseline .fundamental .fundamental)
  let childReady := input.certificateControlled controls node locals σ queryReady
  let primitiveReady := input.observationControlled controls (.ref head.reference) locals σ childReady headerPaid
  obtain ⟨primitive, ⟨primitiveReady⟩, _⟩ := input.primitiveWorld head.reference head.primitive
    (prefixProvenance provenance head.route) controls frame captured baseline frontier capacity covered data
    closed formed substitutions henv hscoped sourceClosed primitiveReady primitivePaid
    (fun calls lower => unary calls (funded calls lower))
    (fun calls lower => replay calls (funded calls lower))
  obtain ⟨restored, ⟨restoredReady⟩⟩ := route.restoreSupportedWorld node controls frame captured baseline
    frontier capacity covered data closed formed substitutions henv hscoped paid unary replay provenance
    (Nat.le_refl _) primitive.toRichSupportedValue primitiveReady
  let answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available
      (.singleton (plan.atom name frozenLevels [])) := {
    restored with
    rightQuery := {
      rank := n, bound := Nat.le_refl _, raw := .singleton (plan.atom name frozenLevels []),
      footprint := [], observation := input.observation node locals τ,
      adapter := by rw [raiseProfile_self]; exact .refl _,
      resources := (fun _ _ member => nomatch member),
      live := input.ready.live plan name frozenLevels [] } }
  exact ⟨answer, ⟨restoredReady⟩,
    ⟨input.observationControlled controls node locals τ childReady headerPaid⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
