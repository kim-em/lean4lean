import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeBodyTransition
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyBodyTransition

/-! The existing native/legacy binder executions supply the same selected frame,
query and bank to the shared literal-term state. Only demand syntax changes. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable def RichPiRowBodyExecution.termProgramState
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {n m r : Nat} {table : List (Key n × Profile n)}
    {selectedKey : Key m} {selectedResult : Profile m} {atom : Atom m}
    {goalOutput : Atom r}
    (pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult)
    {row : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref domain) body pending.oldKey pending.oldResult}
    {parentEnvironment : WorldEnvironmentProvenance strata U environment}
    (execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body row τ anchor hu hv parentEnvironment)
    (continuation : RetainedTermDemand env U registry target goal goalOutput B atom)
    (member : atom ∈ selectedResult.atoms)
    (sourceBelow : sourceEnv ≤ env)
 :
    RetainedTermProgramState env U registry target strata P frontier goal goalOutput := by
  let original := Classical.choose (pending.output.atom member)
  have present := (Classical.choose_spec (pending.output.atom member)).1
  let action := Classical.choice (Classical.choose_spec (pending.output.atom member)).2
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
    left := σ.cons pending.oldKey.anchor
    right := τ.cons anchor
    available := available.push (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons)
    frame := execution.frame
    captured := execution.captured
    data := execution.data
    closed := execution.closed
    substitutions := execution.substitutions
    sourceBelow := sourceBelow
    relevant := relevant
    rank := n
    profile := pending.oldResult
    footprint := row.bodyFootprint
    program := .rich row.body
    annotation := .rich execution.ready.annotation
    within := execution.ready.within
    sponsored := execution.ready.sponsored
    resources := execution.resources
    selected := original
    member := present
    demand := .output (.code .refl action (row.body.formed.singleton_of_mem present)) continuation
    paid := execution.sponsored
    bank := execution.bank }

noncomputable def WorldLegacyPiSizedSelection.termProgramState
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
    (continuation : RetainedTermDemand env U registry target
      goal goalOutput B atom)
    (member : atom ∈ result.atoms)
    (sourceBelow : sourceEnv ≤ env) :
    RetainedTermProgramState env U registry target strata P frontier
      goal goalOutput := by
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

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
