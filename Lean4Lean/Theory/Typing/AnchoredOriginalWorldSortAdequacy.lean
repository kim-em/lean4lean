import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalPiLevels
import Lean4Lean.Theory.Typing.AnchoredCodeExtraction

/-! Literal sort inversion obtained by executing the actual rank-zero query
through the unary equality interface. The final initial-frame wrapper is
supplied below by the constructive world entry, not by a semantic oracle. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

/-- A real world frame suffices for the literal-sort query. The sponsor is
the same actual original in the strictly later R phase, so no separate
sponsorship or interpretation answer is assumed. -/
theorem Derivation.sortLevelsOfWorldUnary
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    (original : Derivation sourceEnv U source (.sort left) (.sort right) assigned)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls
      [originalCallWorld controls .expressionReindex (.ref (.left original)) captured] frame captured)
    (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (banks : ∀ budget, WorldBoundedUnaryAt env U registry strata P budget) : left ≈ right := by
  classical
  obtain ⟨flag, relevant⟩ : ∃ flag, Relevant left flag := by
    by_cases zero : left ≈ .zero
    · exact ⟨false, zero⟩
    · exact ⟨true, zero⟩
  let profile : Profile 0 := .sort flag
  let query : RichObs sourceEnv env U registry target (.ref (.left original))
      locals σ profile [] := .legacy (.legacy (.sort relevant))
  let active := originalCallWorld controls .fundamental (.ref (.left original)) captured
  let sponsor := originalCallWorld controls .expressionReindex (.ref (.left original)) captured
  have smaller : WorldBelow strata.rules.length active sponsor := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have sponsored : Sponsored [sponsor] [active] := by
    intro world member
    cases List.mem_singleton.mp member
    exact ⟨sponsor, List.mem_singleton_self _, smaller⟩
  let ready : ControlledStoredQuery controls [sponsor] (.observation query) := {
    annotation := .legacy _ (.legacy _ (.sort relevant))
    within := by
      intro control _
      change query.headDepth _ ≤ _
      simp only [query, RichObs.headDepth, SortableObs.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    sponsored := by intro world member; cases member }
  obtain ⟨answer, _⟩ := (banks ([sponsor] ++ [active])).equality original true
    (.ofLocation .here context) controls frame captured captured [sponsor]
    (Nat.le_refl _) (Covered.refl _) rfl sponsored data closed formed substitutions
    query (by intro index need member; cases member) ready
  have code := answer.related.code_of_sortable henv hscoped formed (Profile.HasType.sort flag)
  have literal : TypeRelated env U registry target (.sort left) (.sort right) profile := by
    simpa only [Bool.not_true, Bool.false_eq_true, reduceIte, subst_sort] using code
  exact TypeRelated.literalSortLevels formed literal

/-- Independent original typings of the same expression are compared by an
actual assigned-code query. No raw uniqueness or sort inversion theorem is
used to identify their universe levels. -/
theorem EndpointRef.sortTypingLevelsOfWorldReplay
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    (first : EndpointRef sourceEnv U source expression (.sort left))
    (second : EndpointRef sourceEnv U source expression (.sort right))
    (_henv : env.Ordered)
    (formed : OnCtx target (env.IsType U))
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls
      [originalCallWorld controls .expressionReindex (.ref first) captured,
       originalCallWorld controls .expressionReindex (.ref second) captured] frame captured)
    (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (banks : ∀ budget, WorldBoundedReplayAt env U registry strata P budget) : left ≈ right := by
  classical
  obtain ⟨flag, relevant⟩ : ∃ flag, Relevant left flag := by
    by_cases zero : left ≈ .zero
    · exact ⟨false, zero⟩
    · exact ⟨true, zero⟩
  let base := frame.captureBase substitutions
  let leftDisplay := OriginalNestedDisplay.identity base (.ref first) (.ofLocation .here context)
  let rightDisplay := OriginalNestedDisplay.identity base (.ref second) (.ofLocation .here context)
  let frontier := [originalCallWorld controls .expressionReindex (.ref first) captured,
    originalCallWorld controls .expressionReindex (.ref second) captured]
  let calls := [originalCallWorld controls .assignedComparison (.ref first) captured,
    originalCallWorld controls .assignedComparison (.ref second) captured]
  obtain ⟨ready⟩ := data.controlled substitutions
  let firstData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := leftDisplay) controls captured frontier base.identityRealization := {
    generation := data.generation substitutions
    replayable := trivial
    controlled := ready
    compatible := ⟨rfl, rfl⟩
    closed := closed
    capacity := Nat.le_refl _
    covered := Covered.refl _
    hereditary := data.generation_hereditary substitutions }
  let secondData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := rightDisplay) controls captured frontier base.identityRealization := {
    generation := data.generation substitutions
    replayable := trivial
    controlled := ready
    compatible := ⟨rfl, rfl⟩
    closed := closed
    capacity := Nat.le_refl _
    covered := Covered.refl _
    hereditary := data.generation_hereditary substitutions }
  have lower {assigned} (node : EndpointState sourceEnv U source expression assigned) :
      WorldBelow strata.rules.length (originalCallWorld controls .assignedComparison node captured)
        (originalCallWorld controls .expressionReindex node captured) := by
    apply original_child
    exact richReindex_to_assignedComparison _
  have paid : Sponsored frontier calls := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, lower (.ref first)⟩
    · cases List.mem_singleton.mp member
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), lower (.ref second)⟩
  let query : RichCert sourceEnv env U registry target first.typeFormation.node
      locals σ true (Profile.sort (n := 0) flag) [] :=
    .legacy (.seed (.sort relevant) (Profile.HasType.sort flag))
  let queryReady : ControlledStoredQuery controls frontier (.certificate query) := {
    annotation := .legacy _ (.seed _ _ (.sort relevant))
    within := by
      intro control _
      change query.headDepth _ ≤ _
      simp only [query, RichCert.headDepth, SortableCert.headDepth, Obs.headDepth]
      exact Nat.zero_le _
    sponsored := by intro world member; cases member }
  obtain ⟨answer, _⟩ := (banks (frontier ++ calls)).assigned base base.initialCaps
    leftDisplay rightDisplay σ τ controls controls rfl rfl captured captured frontier rfl paid
    base.identityRealization firstData base.identityRealization secondData
    query (by intro index need member; cases member) queryReady
  have literal : TypeRelated env U registry target (.sort left) (.sort right) (Profile.sort (n := 0) flag) := by
    simpa only [OriginalNestedDisplay.formationDisplay, OriginalNestedDisplay.identity, subst_sort] using answer.related
  exact TypeRelated.literalSortLevels formed literal

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
