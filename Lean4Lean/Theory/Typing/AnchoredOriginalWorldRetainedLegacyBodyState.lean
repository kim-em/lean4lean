import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyBodyTransition
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback

/-! Continue the retained interpreter at the original legacy row body. Its
annotation size is measured before attachment to the original endpoint; the
actual binder execution supplies exactly the frame and recursive call bank. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- Concrete retained legacy next state, exposing the selected row and
execution to a transition transcript without counting attachment wrappers. -/
noncomputable def WorldLegacyPiSizedSelection.programState
    {strata : EquationStratification env} {P : VEnv → Prop}
    {budget : WorldPiDomainBudget strata}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {n : Nat} {key : Key n} {result : Profile n} {atom : Atom n}
    (selection : WorldLegacyPiSizedSelection env budget U registry target locals σ A B available
      sizeBudget annotationBudget key result)
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body selection.row.attach τ anchor hu hv parentEnvironment)
    (sameAnnotation : (show WorldCertProvenance strata selection.row.attach.body from execution.ready.annotation) =
      .legacy selection.row.body.certificate selection.bodyAnnotation.certificate)
    (continuation : RetainedApplicationDemand env U registry target
      goalFunction goalArgument goalOutput B atom)
    (member : atom ∈ result.atoms)
    (sourceBelow : sourceEnv ≤ env) :
    RetainedProgramState env U registry target strata P frontier
      goalFunction goalArgument goalOutput := by
  let original := Classical.choose (selection.pending.output.atom member)
  have present := (Classical.choose_spec (selection.pending.output.atom member)).1
  let action := Classical.choice (Classical.choose_spec (selection.pending.output.atom member)).2
  have sponsored : Sponsored frontier selection.bodyAnnotation.certificate.worlds := by
    have paid := execution.ready.sponsored
    change Sponsored frontier
      (show WorldCertProvenance strata selection.row.attach.body from execution.ready.annotation).worlds at paid
    rw [sameAnnotation] at paid
    exact paid
  exact {
    sourceEnv := sourceEnv
    source := A :: source
    context := .cons context domain
    expression := B
    assigned := .sort v
    node := body
    provenance := execution.provenance
    controls := controls
    locals := Locals.push locals
    left := σ.cons selection.pending.oldKey.anchor
    right := τ.cons anchor
    available := available.push (selection.row.bodyFootprint.localNeeds ++
      selection.row.bodyFootprint.localNeeds.flatMap Need.singletons)
    frame := execution.frame
    captured := execution.captured
    data := execution.data
    closed := execution.closed
    substitutions := execution.substitutions
    sourceBelow := sourceBelow
    relevant := selection.relevant
    rank := selection.rank
    profile := selection.pending.oldResult
    footprint := selection.row.bodyFootprint
    program := .legacy selection.row.body
    annotation := .legacy selection.bodyAnnotation
    within := execution.ready.within
    sponsored := sponsored
    resources := execution.resources
    selected := original
    member := present
    demand := .output (.code .refl action
      (selection.row.body.certificate.formed.singleton_of_mem present)) continuation
    paid := execution.sponsored
    bank := execution.bank }

theorem WorldLegacyPiSizedSelection.nextProgramState
    {strata : EquationStratification env} {P : VEnv → Prop}
    {budget : WorldPiDomainBudget strata}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {n : Nat} {key : Key n} {result : Profile n} {atom : Atom n}
    (selection : WorldLegacyPiSizedSelection env budget U registry target locals σ A B available
      sizeBudget annotationBudget key result)
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body selection.row.attach τ anchor hu hv parentEnvironment)
    (sameAnnotation : (show WorldCertProvenance strata selection.row.attach.body from execution.ready.annotation) =
      .legacy selection.row.body.certificate selection.bodyAnnotation.certificate)
    (continuation : RetainedApplicationDemand env U registry target
      goalFunction goalArgument goalOutput B atom)
    (member : atom ∈ result.atoms)
    (sourceBelow : sourceEnv ≤ env) :
    ∃ next : RetainedProgramState env U registry target strata P frontier
        goalFunction goalArgument goalOutput,
      next.programSize < annotationBudget ∧
      next.demand.readback next.right = continuation.readback (τ.cons anchor) := by
  exact ⟨selection.programState execution sameAnnotation continuation member sourceBelow,
    selection.bodySmaller, rfl⟩

/-- Enter the original selected body and continue with its raw legacy program.
No body execution or recursive answer is supplied by the caller. -/
theorem WorldLegacyPiSizedSelection.enterBodyProgramState
    {strata : EquationStratification env} {P : VEnv → Prop}
    {budget : WorldPiDomainBudget strata}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (selection : WorldLegacyPiSizedSelection env budget U registry target locals σ A B available
      sizeBudget annotationBudget key result)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv (.ref domain) body))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => budget.depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier budget.worlds)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (admitted : Admitted env U registry target key anchor anchor)
    {atom : Atom _}
    (continuation : RetainedApplicationDemand env U registry target
      goalFunction goalArgument goalOutput B atom)
    (member : atom ∈ result.atoms) :
    ∃ next : RetainedProgramState env U registry target strata P frontier
        goalFunction goalArgument goalOutput,
      next.programSize < annotationBudget ∧
      next.demand.readback next.right = continuation.readback (τ.cons anchor) := by
  obtain ⟨execution, sameAnnotation, _⟩ := selection.enterPrefixBodyWorldExact
    route provenance frame captured data within sponsored closed formed substitutions
    henv hscoped sourceBelow paid bank admitted
  exact selection.nextProgramState execution sameAnnotation continuation member sourceBelow

/-- Retain the actual binder execution and annotation identity alongside the
concrete next state, so a later caller compiler can replay this same row. -/
theorem WorldLegacyPiSizedSelection.enterBodyProgram
    {strata : EquationStratification env} {P : VEnv → Prop}
    {budget : WorldPiDomainBudget strata}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (selection : WorldLegacyPiSizedSelection env budget U registry target locals σ A B available
      sizeBudget annotationBudget key result)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv (.ref domain) body))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
      (fun control => budget.depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier budget.worlds)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (admitted : Admitted env U registry target key anchor anchor)
    {atom : Atom _}
    (continuation : RetainedApplicationDemand env U registry target
      goalFunction goalArgument goalOutput B atom)
    (member : atom ∈ result.atoms) :
    ∃ execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body selection.row.attach τ anchor hu hv captured,
    ∃ sameAnnotation : (show WorldCertProvenance strata selection.row.attach.body from execution.ready.annotation) =
      .legacy selection.row.body.certificate selection.bodyAnnotation.certificate,
      let next := selection.programState execution sameAnnotation continuation member sourceBelow
      next.programSize < annotationBudget ∧
      next.demand.readback next.right = continuation.readback (τ.cons anchor) := by
  obtain ⟨execution, sameAnnotation, _, _, _, _⟩ := selection.enterPrefixBodyWorldExact
    route provenance frame captured data within sponsored closed formed substitutions henv hscoped
    sourceBelow paid bank admitted
  exact ⟨execution, sameAnnotation, selection.bodySmaller, rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
