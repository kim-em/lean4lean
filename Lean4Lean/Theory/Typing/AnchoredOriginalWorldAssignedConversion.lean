import Lean4Lean.Theory.Typing.AnchoredOriginalWorldSortInversion

/-! Assigned-type conversion from the actual all-budget comparison interface.
The two independent original typings, identity frame, empty query, and phase
sponsors are constructed here. No uniqueness or inversion theorem is used. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Even an empty assigned-code request returns an unconditional raw path.
This executes C at the two actual independently reified typing originals. -/
theorem assignedConversionOfWorldBanks
    (strata : EquationStratification env) (henv : env.Ordered)
    (formed : OnCtx Γ (env.IsType U))
    (banks : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget)
    (first : env.HasType U Γ expression A)
    (second : env.HasType U Γ expression B) : TypeConversion env U Γ A B := by
  obtain ⟨firstOriginal⟩ := Derivation.reify (first.strong henv formed)
  obtain ⟨secondOriginal⟩ := Derivation.reify (second.strong henv formed)
  let controls := worldAdequacyControls strata henv
  obtain ⟨context, locals, frame, captured, allReady⟩ := initialWorldFrame (registry := registry) controls formed
  let firstNode : EndpointState env U Γ expression A := .ref (.left firstOriginal)
  let secondNode : EndpointState env U Γ expression B := .ref (.left secondOriginal)
  let frontier := [originalCallWorld controls .expressionReindex firstNode captured,
    originalCallWorld controls .expressionReindex secondNode captured]
  let calls := [originalCallWorld controls .assignedComparison firstNode captured,
    originalCallWorld controls .assignedComparison secondNode captured]
  obtain ⟨data⟩ := allReady frontier
  have substitutions := Ctx.SubstEq.id henv formed
  let base := frame.captureBase substitutions
  let leftDisplay := OriginalNestedDisplay.identity base firstNode (.ofLocation .here context)
  let rightDisplay := OriginalNestedDisplay.identity base secondNode (.ofLocation .here context)
  obtain ⟨ready⟩ := data.controlled substitutions
  let firstData : WorldCallFrameData (P := fun _ => True) (base := base) (caps := base.initialCaps)
      (display := leftDisplay) controls captured frontier base.identityRealization := {
    generation := data.generation substitutions
    replayable := trivial
    controlled := ready
    compatible := ⟨rfl, rfl⟩
    closed := fun _ _ member => False.elim (List.not_mem_nil member)
    capacity := Nat.le_refl _
    covered := Covered.refl _
    hereditary := data.generation_hereditary substitutions }
  let secondData : WorldCallFrameData (P := fun _ => True) (base := base) (caps := base.initialCaps)
      (display := rightDisplay) controls captured frontier base.identityRealization := {
    generation := data.generation substitutions
    replayable := trivial
    controlled := ready
    compatible := ⟨rfl, rfl⟩
    closed := fun _ _ member => False.elim (List.not_mem_nil member)
    capacity := Nat.le_refl _
    covered := Covered.refl _
    hereditary := data.generation_hereditary substitutions }
  have lower {assigned} (node : EndpointState env U Γ expression assigned) :
      WorldBelow strata.rules.length (originalCallWorld controls .assignedComparison node captured)
        (originalCallWorld controls .expressionReindex node captured) := by
    apply original_child
    exact richReindex_to_assignedComparison _
  have paid : Sponsored frontier calls := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, lower firstNode⟩
    · cases List.mem_singleton.mp member
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), lower secondNode⟩
  let query : RichCert env env U registry Γ firstNode.typeFormation.node
      locals Subst.id true (Profile.empty : Profile 0) [] :=
    .legacy (.seed .empty (.empty (.sort true)))
  let queryReady : ControlledStoredQuery controls frontier (.certificate query) := {
    annotation := .legacy _ (.seed _ _ .empty)
    within := by
      intro control _
      change query.headDepth _ ≤ _
      simp only [query, RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    sponsored := by intro world member; cases member }
  obtain ⟨answer, _⟩ := (banks (frontier ++ calls)).assigned base base.initialCaps
    leftDisplay rightDisplay Subst.id Subst.id controls controls rfl rfl captured captured frontier rfl paid
    base.identityRealization firstData base.identityRealization secondData
    query (by intro index need member; cases member) queryReady
  simpa only [OriginalNestedDisplay.formationDisplay, OriginalNestedDisplay.identity, subst_id] using answer.path

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
