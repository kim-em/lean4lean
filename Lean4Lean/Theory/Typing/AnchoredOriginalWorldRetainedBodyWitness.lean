import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandNormalization
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedBodyState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedLegacyBodyState

/-! A body edge retains its exact pending input conversion, original row and
actual binder execution. The after-state is the concrete state of that SAME
execution. Its source frame and resource table are tied to the before-state. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive RetainedBodyTransitionWitness
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput → Type where
  | native {A B : VExpr} {u v : VLevel} {hu : u.WF U} {hv : v.WF U}
      (expressionEq : before.expression = .forallE A B)
      {domain : EndpointRef before.sourceEnv U before.source A (.sort u)}
      {body : EndpointState before.sourceEnv U (A :: before.source) B (.sort v)}
      {n m : Nat} {support : Profile m} {table : List (Key n × Profile n)}
      {selectedTable : List (Key m × Profile m)} {key : Key m} {result : Profile m} {atom : Atom m}
      (path : GeneralOutputPath env U registry target before.selected
        (show Atom (m+1) from .pi nextDomain nextBody support selectedTable))
      (selected : (key, result) ∈ selectedTable)
      (admitted : Admitted env U registry target key anchor anchor)
      (pending : RankedPendingNativeRow env U registry target table relevant key result)
      (row : RichPiRowCertificate env U registry target before.locals before.left before.available relevant
        (.ref domain) body pending.oldKey pending.oldResult)
      (execution : RichPiRowBodyExecution (P := P) (context := before.context)
        before.controls frontier domain body row before.right anchor hu hv before.captured)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom)
      (member : atom ∈ result.atoms)
      (readback : continuation.readback (before.right.cons anchor) = before.demand.readback before.right)
      (normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        (expressionEq ▸ before.demand) (.body path selected member anchor admitted continuation))
      (worlds : execution.ready.annotation.worlds ⊆ before.annotation.certificate.worlds)
      (depth : ∀ policy, row.body.headDepth policy ≤ before.program.certificate.headDepth policy) :
      RetainedBodyTransitionWitness before
        (execution.programState pending continuation member before.sourceBelow)
  | legacy {A B : VExpr} {u v : VLevel} {hu : u.WF U} {hv : v.WF U}
      (expressionEq : before.expression = .forallE A B)
      {domain : EndpointRef before.sourceEnv U before.source A (.sort u)}
      {body : EndpointState before.sourceEnv U (A :: before.source) B (.sort v)}
      {m : Nat} {support : Profile m} {selectedTable : List (Key m × Profile m)}
      {key : Key m} {result : Profile m} {atom : Atom m}
      (path : GeneralOutputPath env U registry target before.selected
        (show Atom (m+1) from .pi nextDomain nextBody support selectedTable))
      (selected : (key, result) ∈ selectedTable)
      (admitted : Admitted env U registry target key anchor anchor)
      {budget : WorldPiDomainBudget strata}
      (selection : WorldLegacyPiSizedSelection env budget U registry target before.locals before.left A B
        before.available sizeBudget annotationBudget key result)
      (execution : RichPiRowBodyExecution (P := P) (context := before.context)
        before.controls frontier domain body selection.row.attach before.right anchor hu hv before.captured)
      (sameAnnotation : (show WorldCertProvenance strata selection.row.attach.body from execution.ready.annotation) =
        .legacy selection.row.body.certificate selection.bodyAnnotation.certificate)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom)
      (member : atom ∈ result.atoms)
      (readback : continuation.readback (before.right.cons anchor) = before.demand.readback before.right)
      (normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
        (expressionEq ▸ before.demand) (.body path selected member anchor admitted continuation))
      (worlds : execution.ready.annotation.worlds ⊆ before.annotation.certificate.worlds)
      (depth : ∀ policy, selection.row.body.certificate.headDepth policy ≤ before.program.certificate.headDepth policy) :
      RetainedBodyTransitionWitness before
        (selection.programState execution sameAnnotation continuation member before.sourceBelow)


/-- Execute an actually selected native body and retain the very same pending
row and binder execution in the edge certificate. -/
theorem enterNativeBodyStateWitness
    {goalRank : Nat} {goalOutput : Atom goalRank}
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    {A B : VExpr} {u v : VLevel} {hu : u.WF U} {hv : v.WF U}
    (expressionEq : before.expression = .forallE A B)
    {domainNode : EndpointState before.sourceEnv U before.source A (.sort u)}
    {body : EndpointState before.sourceEnv U (A :: before.source) B (.sort v)}
    {n m : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    {support result : Profile m} {nextTable : List (Key m × Profile m)}
    {key : Key m} {atom : Atom m} {anchor : VExpr}
    {domainCode : RichCert before.sourceEnv env U registry target domainNode before.locals before.left true ambient domainFootprint}
    {rows : RichRows before.sourceEnv env U registry target domainNode body before.locals before.left relevant ambient table rowFootprint}
    {guard : PiGuard env U target before.left A B prototypeDomain prototypeBody}
    (domainAnnotation : WorldCertProvenance strata domainCode)
    (rowsAnnotation : WorldRowsProvenance strata rows)
    (resources : (domainFootprint ++ rowFootprint).Available before.available)
    (route : PrefixRoute before.sourceEnv U before.source (.forallE A B)
      (before.node.cast expressionEq rfl) (.pi hu hv domainNode body))
    (included : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).worlds ⊆ before.annotation.certificate.worlds)
    (depth : ∀ policy, (RichPiProgramLeaf.native hu hv domainCode guard rows resources).headDepth policy ≤
      before.program.certificate.headDepth policy)
    (smaller : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).retainedSize < before.programSize)
    (sourcePath : GeneralOutputPath env U registry target (r := n+1) (n := m+1)
      (.pi prototypeDomain prototypeBody ambient table) (.pi nextDomain nextBody support nextTable))
    (inputPath : GeneralOutputPath env U registry target before.selected
      (show Atom (m+1) from .pi nextDomain nextBody support nextTable))
    (selected : (key, result) ∈ nextTable)
    (admitted : Admitted env U registry target key anchor anchor)
    (member : atom ∈ result.atoms)
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom)
    (readback : continuation.readback (before.right.cons anchor) = before.demand.readback before.right)
    (normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
      (expressionEq ▸ before.demand) (.body inputPath selected member anchor admitted continuation))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput, next.programSize < before.programSize ∧ Nonempty (RetainedBodyTransitionWitness before next) := by
  let originalState := before
  rcases before with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
    locals, left, right, available, frame, captured, data, closed, substitutions, sourceBelow,
    originalRelevant, rank, profile, footprint, program, annotation, within, sponsored, supplied,
    inputAtom, inputMember, demand, paid, bank⟩
  cases expressionEq
  dsimp only at domainCode rows route domainAnnotation rowsAnnotation resources included depth smaller inputPath readback
  obtain ⟨domain, same⟩ := (route.locate provenance.location).originalDomains.1
  cases same
  let ready : ControlledStoredQuery controls frontier (.certificate program.certificate) :=
    ⟨annotation.certificate, within, sponsored⟩
  obtain ⟨pending, row, execution, domainEq, bounded, bodyWorlds, bodyDepth⟩ :=
    enterSelectedNativeBodyWorld domainAnnotation rowsAnnotation resources route provenance
      frame captured data ready included depth _ smaller closed formed substitutions henv hscoped sourceBelow
      paid bank sourcePath selected admitted
  exact ⟨execution.programState pending continuation member sourceBelow, bounded,
    ⟨RetainedBodyTransitionWitness.native (before := originalState) rfl inputPath selected admitted pending row execution continuation member readback normalized bodyWorlds bodyDepth⟩⟩


/-- The legacy edge also computes its original binder execution; it never
accepts a completed body answer. -/
theorem enterLegacyBodyStateWitness
    {goalRank : Nat} {goalOutput : Atom goalRank}
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    {A B : VExpr} {u v : VLevel} {hu : u.WF U} {hv : v.WF U}
    (expressionEq : before.expression = .forallE A B)
    {domain : EndpointRef before.sourceEnv U before.source A (.sort u)}
    {body : EndpointState before.sourceEnv U (A :: before.source) B (.sort v)}
    {m : Nat} {support result : Profile m} {nextTable : List (Key m × Profile m)}
    {key : Key m} {atom : Atom m} {anchor : VExpr}
    {budget : WorldPiDomainBudget strata}
    (selection : WorldLegacyPiSizedSelection env budget U registry target before.locals before.left A B
      before.available sizeBudget before.programSize key result)
    (route : PrefixRoute before.sourceEnv U before.source (.forallE A B)
      (before.node.cast expressionEq rfl) (.pi hu hv (.ref domain) body))
    (within : WithinAbove before.controls.cutoff before.controls.fuel
      (fun control => budget.depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier budget.worlds)
    (worlds : budget.worlds ⊆ before.annotation.certificate.worlds)
    (depth : ∀ policy, budget.depth policy ≤ before.program.certificate.headDepth policy)
    (inputPath : GeneralOutputPath env U registry target before.selected
      (show Atom (m+1) from .pi nextDomain nextBody support nextTable))
    (selected : (key, result) ∈ nextTable)
    (admitted : Admitted env U registry target key anchor anchor)
    (member : atom ∈ result.atoms)
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom)
    (readback : continuation.readback (before.right.cons anchor) = before.demand.readback before.right)
    (normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
      (expressionEq ▸ before.demand) (.body inputPath selected member anchor admitted continuation))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < before.programSize ∧ Nonempty (RetainedBodyTransitionWitness before next) := by
  let originalState := before
  rcases before with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
    locals, left, right, available, frame, captured, data, closed, substitutions, sourceBelow,
    originalRelevant, rank, profile, footprint, program, annotation, controlled, paidQueries, supplied,
    inputAtom, inputMember, demand, paid, bank⟩
  cases expressionEq
  obtain ⟨execution, sameAnnotation, bounded, bodyWorlds, bodyDepth, bodyResources⟩ := selection.enterPrefixBodyWorldExact route
    provenance frame captured data within sponsored closed formed substitutions henv hscoped sourceBelow
    paid bank admitted
  exact ⟨selection.programState execution sameAnnotation continuation member sourceBelow, bounded,
    ⟨RetainedBodyTransitionWitness.legacy (before := originalState) rfl inputPath selected admitted
      selection execution sameAnnotation continuation member readback normalized
      (by
        change WorldCertProvenance.worlds (show WorldCertProvenance strata _ from execution.ready.annotation) ⊆ _
        rw [sameAnnotation]
        exact fun world hm => worlds (bodyWorlds hm))
      (fun policy => Nat.le_trans (bodyDepth policy) (depth policy))⟩⟩

theorem RetainedBodyTransitionWitness.readback
    (edge : RetainedBodyTransitionWitness before next) :
    next.demand.readback next.right = before.demand.readback before.right := by
  cases edge with
  | native _ _ _ _ _ _ _ _ _ same _ _ _ => exact same
  | legacy _ _ _ _ _ _ _ _ _ same _ _ _ => exact same

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
