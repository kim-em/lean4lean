import Lean4Lean.Theory.Typing.AnchoredOriginalWorldSortInversion

/-! Initial assigned-sort demand for an independently typed original endpoint.
This is the seed for backward rigid-application query construction: the actual
sort typing supplies the initial literal observation, and C produces a query
at the other endpoint's actual assigned formation with its selected history. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The arbitrary rank allows the first family terminal's assigned support
to be seeded directly. No observation or selected-frame answer is supplied.
In the application case `second.typeFormation.node` is its actual result child. -/
theorem EndpointState.assignedSortQueryOfWorldBanks
    (strata : EquationStratification env) (henv : env.Ordered)
    (formed : OnCtx Γ (env.IsType U))
    (context : ContextDerivation env U Γ)
    (first : EndpointRef env U Γ expression (.sort level))
    (second : EndpointState env U Γ expression assigned)
    (secondProvenance : EndpointProvenance context second)
    (banks : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget)
    (n : Nat) :
    let controls := worldAdequacyControls strata henv
    ∃ locals, ∃ frame : OriginalRichFrame env env U registry Γ context locals .id .id (fun _ => []),
    ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
    let substitutions := Ctx.SubstEq.id henv formed
    let base := frame.captureBase substitutions
    let right := OriginalNestedDisplay.identity base second secondProvenance
    let frontier := [originalCallWorld controls .expressionReindex (.ref first) captured,
      originalCallWorld controls .expressionReindex second captured]
    ∃ flag, Relevant level flag ∧
      ∃ answer : AmbientBoundedParameterReply base base.initialCaps (.sort level)
          right.formationDisplay .id .id (Profile.sort (n := n) flag)
          (environmentCost (frame.dependencyEnvironment controls.ordered)),
        Nonempty (WorldParameterReplyData (P := fun _ => True) controls captured frontier answer) := by
  classical
  dsimp only
  let controls := worldAdequacyControls strata henv
  let substitutions := Ctx.SubstEq.id henv formed
  obtain ⟨locals, frame, captured, allReady⟩ := context.emptyWorldFrame
    (registry := registry) controls VEnv.LE.rfl substitutions
  let base := frame.captureBase substitutions
  let left := OriginalNestedDisplay.identity base (.ref first) (.ofLocation .here context)
  let right := OriginalNestedDisplay.identity base second secondProvenance
  let frontier := [originalCallWorld controls .expressionReindex (.ref first) captured,
    originalCallWorld controls .expressionReindex second captured]
  let calls := [originalCallWorld controls .assignedComparison (.ref first) captured,
    originalCallWorld controls .assignedComparison second captured]
  obtain ⟨data⟩ := allReady frontier
  obtain ⟨ready⟩ := data.controlled substitutions
  let firstData : WorldCallFrameData (P := fun _ => True) (base := base) (caps := base.initialCaps)
      (display := left) controls captured frontier base.identityRealization := {
    generation := data.generation substitutions
    replayable := trivial
    controlled := ready
    compatible := ⟨rfl, rfl⟩
    closed := fun _ _ member => False.elim (List.not_mem_nil member)
    capacity := Nat.le_refl _
    covered := Covered.refl _
    hereditary := data.generation_hereditary substitutions }
  let secondData : WorldCallFrameData (P := fun _ => True) (base := base) (caps := base.initialCaps)
      (display := right) controls captured frontier base.identityRealization := {
    generation := data.generation substitutions
    replayable := trivial
    controlled := ready
    compatible := ⟨rfl, rfl⟩
    closed := fun _ _ member => False.elim (List.not_mem_nil member)
    capacity := Nat.le_refl _
    covered := Covered.refl _
    hereditary := data.generation_hereditary substitutions }
  have lower {type} (node : EndpointState env U Γ expression type) :
      WorldBelow strata.rules.length (originalCallWorld controls .assignedComparison node captured)
        (originalCallWorld controls .expressionReindex node captured) := by
    apply original_child
    exact richReindex_to_assignedComparison _
  have paid : Sponsored frontier calls := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, lower (.ref first)⟩
    · cases List.mem_singleton.mp member
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), lower second⟩
  obtain ⟨flag, relevant⟩ : ∃ flag, Relevant level flag := by
    by_cases zero : level ≈ .zero
    · exact ⟨false, zero⟩
    · exact ⟨true, zero⟩
  let query : RichCert env env U registry Γ first.typeFormation.node
      locals .id true (Profile.sort (n := n) flag) [] :=
    .legacy (.seed (.sort relevant) (Profile.HasType.sort flag))
  let queryReady : ControlledStoredQuery controls frontier (.certificate query) := {
    annotation := .legacy _ (.seed _ _ (.sort relevant))
    within := by
      intro control _
      change query.headDepth _ ≤ _
      simp only [query, RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    sponsored := by intro world member; cases member }
  obtain ⟨answer, answerData⟩ := (banks (frontier ++ calls)).assigned base base.initialCaps
    left right .id .id controls controls rfl rfl captured captured frontier rfl paid
    base.identityRealization firstData base.identityRealization secondData
    query (by intro index need member; cases member) queryReady
  exact ⟨locals, frame, captured, flag, relevant, answer, answerData⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
