import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidSpineInitialization

/-! Rigid-query initialization on the actual left endpoint of an equality.
The independent sort typing seeds C, while every subsequent original and the
retained R sponsor belong to the equality which will consume the query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- No later endpoint reindex or frontier enlargement is needed: the
initial assigned comparison already returns a query at the actual equality's
left assigned formation, and its own retained R world sponsors the trace. -/
theorem Derivation.rigidSpineOfWorldBanks
    (strata : EquationStratification env) (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx Γ (env.IsType U)) (context : ContextDerivation env U Γ)
    (typed : EndpointRef env U Γ (VExpr.mkApps (.const name levels) arguments) (.sort level))
    (original : Derivation env U Γ (VExpr.mkApps (.const name levels) arguments) right assigned)
    (unary : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget)
    (replay : ∀ budget, WorldBoundedReplayAt env U registry strata (fun _ => True) budget) :
    let controls := worldAdequacyControls strata henv
    ∃ locals, ∃ frame : OriginalRichFrame env env U registry Γ context locals .id .id (fun _ => []),
    ∃ baseline : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
    let frontier := [originalCallWorld controls .expressionReindex (.ref typed) baseline,
      originalCallWorld controls .expressionReindex (.ref (.left original)) baseline]
    ∃ flag, Relevant level flag ∧
    ∃ input : WorldAssignedQuery (registry := registry) (target := Γ) (context := context)
      (fun _ => True) controls baseline frontier (.ref (.left original)) .id .id true (Profile.sort (n := 1) flag),
      Nonempty (WorldRigidBackwardTrace context controls baseline frontier .id .id name levels
        (.ref (.left original)) .here (RigidFamilySpine.Prepared.terminal flag) input) := by
  dsimp only
  let controls := worldAdequacyControls strata henv
  let substitutions := Ctx.SubstEq.id henv formed
  obtain ⟨locals, frame, baseline, flag, relevant, answer, ⟨data⟩⟩ :=
    EndpointState.assignedSortQueryOfWorldBanks strata henv formed context typed (.ref (.left original))
      (.ofLocation .here context) replay 1
  let base := frame.captureBase substitutions
  let display := OriginalNestedDisplay.identity base (.ref (.left original)) (.ofLocation .here context)
  let frontier := [originalCallWorld controls .expressionReindex (.ref typed) baseline,
    originalCallWorld controls .expressionReindex (.ref (.left original)) baseline]
  obtain ⟨input, _localsEq, _availableEq, _frameEq⟩ := WorldAssignedQuery.ofReply (display := display)
    henv controls baseline frontier answer data (Profile.HasType.sort flag)
  have trace := input.initializeRigidSpine (root := .left original) (sponsor := .ref (.left original))
    context controls baseline frontier (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    henv hscoped formed unary replay
    (RigidApplicationSpine.mkApps .constant arguments) (.ref (.left original)) .here
    (RigidFamilySpine.Prepared.terminal flag) (Nat.le_refl _)
  exact ⟨locals, frame, baseline, flag, relevant, input, trace⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
