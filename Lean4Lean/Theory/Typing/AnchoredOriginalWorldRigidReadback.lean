import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidSpineInitialization
import Lean4Lean.Theory.Typing.AnchoredRigidFamilyReadback

/-! Execute the initialized query on its actual equality original. The
assigned support needed by the graded adapter is obtained by a real formation
F call on the same selected certificate and frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

theorem WorldAssignedQuery.rigidReadback
    {strata : EquationStratification env}
    {context : ContextDerivation env U Γ}
    (original : Derivation env U Γ (mkApps (.const name levels) arguments)
      (mkApps (.const name rightLevels) rightArguments) assigned)
    (controls : OriginalWorldControls strata env)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (sponsor : originalCallWorld controls .expressionReindex (.ref (.left original)) baseline ∈ frontier)
    (input : WorldAssignedQuery (registry := registry) (target := Γ) (context := context)
      (fun _ => True) controls baseline frontier (.ref (.left original)) .id .id true
      (Profile.sort (n := 1) flag))
    (past : List RigidFamilyArgument)
    (query : RichGradedResult env env U registry Γ (.ref (.left original)) input.locals .id input.available
      (.singleton ((RigidFamilySpine.terminal flag).atom name levels past)))
    (queryReady : ControlledStoredQuery controls frontier (.observation query.observation))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    (banks : ∀ budget, WorldBoundedUnaryAt env U registry strata (fun _ => True) budget) :
    List.Forall₂ (· ≈ ·) levels rightLevels ∧
      List.Forall₂ (env.IsDefEqU U Γ) arguments rightArguments := by
  let node := EndpointState.ref (.left original)
  have lower {expression childType : VExpr} (child : EndpointState env U Γ expression childType)
      (bound : (Closure.close (child.dependencyOrigin controls.ordered) baselineEnvironment).cost ≤
        (Closure.close (node.dependencyOrigin controls.ordered) baselineEnvironment).cost) :
      WorldBelow strata.rules.length (originalCallWorld controls .fundamental child baseline)
        (originalCallWorld controls .expressionReindex node baseline) := by
    apply original_child
    simp only [richSchedule, RichPhase.code]
    omega
  have pay {expression childType : VExpr} {child : EndpointState env U Γ expression childType}
      (bound : (Closure.close (child.dependencyOrigin controls.ordered) baselineEnvironment).cost ≤
        (Closure.close (node.dependencyOrigin controls.ordered) baselineEnvironment).cost) :
      Sponsored frontier [originalCallWorld controls .fundamental child baseline] := by
    intro world member
    cases List.mem_singleton.mp member
    exact ⟨_, sponsor, lower child bound⟩
  obtain ⟨formation, _, _⟩ := (banks _).computational node.typeFormation.node
    (.ofLocation (.assignedFormation .here) context) controls input.frame input.captured baseline frontier
    input.capacity input.covered rfl (pay (node.typeFormation_dependency_cost_le controls.ordered _))
    input.frameData input.closed formed input.substitutions (.code input.certificate)
    input.resources input.certificateReady.code
  have code : TypeRelated env U registry Γ assigned assigned (Profile.sort (n := 1) flag) := by
    simpa only [subst_id] using
      formation.related.code_of_sortable henv hscoped formed input.certificate.formed
  obtain ⟨answer, _⟩ := (banks _).equality original true (.ofLocation .here context)
    controls input.frame input.captured baseline frontier input.capacity input.covered rfl
    (pay (child := node) (Nat.le_refl _)) input.frameData input.closed formed input.substitutions
    query.observation query.resources queryReady
  have typed := RigidFamilySpine.terminal_typed name levels flag past
  have related := query.adapter.termMap henv hscoped formed
    (Profile.HasType.raise query.bound typed) (code.raise henv query.bound) (by
      simpa only [Bool.not_true, Bool.false_eq_true, reduceIte, subst_id] using answer.related)
  have lowered := lowerProfile.related query.bound henv formed related
  rw [OriginalFactorCut.lower_raised] at lowered
  exact lowered.rigidFamilyReadback henv hscoped formed typed (List.mem_singleton_self _)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
