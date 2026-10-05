import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeBodyTransition
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback

/-! Continue at the literal selected native body. The real binder execution
supplies the source frame and bank; ranked output operations remain pending
while the recursive program retains the exact stored body annotation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- The exact next program is a definition so a transition transcript can
retain its original pending row, binder execution, and selected atom together.
Its frame, certificate annotation and resource table are the execution's own. -/
noncomputable def RichPiRowBodyExecution.programState
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
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom)
    (member : atom ∈ selectedResult.atoms)
    (sourceBelow : sourceEnv ≤ env)
 :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput := by
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

theorem RichPiRowBodyExecution.nextProgramState
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
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom)
    (member : atom ∈ selectedResult.atoms)
    (sourceBelow : sourceEnv ≤ env)
    (budget : Nat)
    (smaller : sizeOf (show WorldCertProvenance strata row.body from execution.ready.annotation) < budget) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < budget ∧
      next.demand.readback next.right = continuation.readback (τ.cons anchor) := by
  exact ⟨execution.programState pending continuation member sourceBelow, smaller, rfl⟩

/-- Select and enter a literal native body from its original Pi provenance.
The original domain reference is derived from the located derivation. -/
theorem enterNativeBodyProgramState
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {n m : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    {nextAmbient : Profile m} {nextTable : List (Key m × Profile m)}
    {selectedKey : Key m} {selectedResult : Profile m}
    {domainCode : RichCert sourceEnv env U registry target domainNode locals σ true ambient domainFootprint}
    {rows : RichRows sourceEnv env U registry target domainNode body locals σ relevant ambient table rowFootprint}
    {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
    (domainAnnotation : WorldCertProvenance strata domainCode)
    (rowsAnnotation : WorldRowsProvenance strata rows)
    (resources : (domainFootprint ++ rowFootprint).Available available)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv domainNode body))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    {incoming : StoredOriginalQuery env U registry target}
    (ready : ControlledStoredQuery controls frontier incoming)
    (included : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).worlds ⊆ ready.annotation.worlds)
    (depth : ∀ policy, (RichPiProgramLeaf.native hu hv domainCode guard rows resources).headDepth policy ≤
      incoming.headDepth policy)
    (budget : Nat)
    (smaller : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).retainedSize < budget)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (path : GeneralOutputPath env U registry target
      (show Atom (n+1) from .pi prototypeDomain prototypeBody ambient table)
      (show Atom (m+1) from .pi nextDomain nextBody nextAmbient nextTable))
    (member : (selectedKey, selectedResult) ∈ nextTable)
    (admitted : Admitted env U registry target selectedKey anchor anchor)
    {atom : Atom m}
    (atomMember : atom ∈ selectedResult.atoms)
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < budget ∧
      next.demand.readback next.right = continuation.readback (τ.cons anchor) := by
  obtain ⟨domain, same⟩ := (route.locate provenance.location).originalDomains.1
  cases same
  obtain ⟨pending, row, execution, _, bodySize, _, _⟩ :=
    enterSelectedNativeBodyWorld domainAnnotation rowsAnnotation resources route provenance
      frame captured data ready included depth budget smaller closed formed substitutions
      henv hscoped sourceBelow paid bank path member admitted
  exact execution.nextProgramState pending continuation atomMember sourceBelow budget bodySize

/-- Select a native body while retaining the actual pending row and binder
execution that construct the next state. A caller compiler can consume those
same finite input adapters and packs through a typed transition transcript. -/
theorem enterSelectedNativeBodyProgram
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {n m : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    {nextAmbient : Profile m} {nextTable : List (Key m × Profile m)}
    {selectedKey : Key m} {selectedResult : Profile m}
    {domainCode : RichCert sourceEnv env U registry target (.ref domain) locals σ true ambient domainFootprint}
    {rows : RichRows sourceEnv env U registry target (.ref domain) body locals σ relevant ambient table rowFootprint}
    {guard : PiGuard env U target σ A B prototypeDomain prototypeBody}
    (domainAnnotation : WorldCertProvenance strata domainCode)
    (rowsAnnotation : WorldRowsProvenance strata rows)
    (resources : (domainFootprint ++ rowFootprint).Available available)
    (route : PrefixRoute sourceEnv U source (.forallE A B) node (.pi hu hv (.ref domain) body))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    {incoming : StoredOriginalQuery env U registry target}
    (ready : ControlledStoredQuery controls frontier incoming)
    (included : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).worlds ⊆ ready.annotation.worlds)
    (depth : ∀ policy, (RichPiProgramLeaf.native hu hv domainCode guard rows resources).headDepth policy ≤
      incoming.headDepth policy)
    (budget : Nat)
    (smaller : (WorldPiProgramLeafProvenance.native (hu := hu) (hv := hv)
      (guard := guard) (resources := resources) domainAnnotation rowsAnnotation).retainedSize < budget)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (path : GeneralOutputPath env U registry target
      (show Atom (n+1) from .pi prototypeDomain prototypeBody ambient table)
      (show Atom (m+1) from .pi nextDomain nextBody nextAmbient nextTable))
    (member : (selectedKey, selectedResult) ∈ nextTable)
    (admitted : Admitted env U registry target selectedKey anchor anchor)
    {atom : Atom m}
    (atomMember : atom ∈ selectedResult.atoms)
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom) :
    ∃ pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult,
    ∃ row : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref domain) body pending.oldKey pending.oldResult,
    ∃ execution : RichPiRowBodyExecution (P := P) (context := context)
      controls frontier domain body row τ anchor hu hv captured,
      HEq row.domain domainCode ∧
      let next := execution.programState pending continuation atomMember sourceBelow
      next.programSize < budget ∧
      next.demand.readback next.right = continuation.readback (τ.cons anchor) := by
  obtain ⟨pending, row, execution, sameDomain, bodySize, _, _⟩ :=
    enterSelectedNativeBodyWorld domainAnnotation rowsAnnotation resources route provenance
      frame captured data ready included depth budget smaller closed formed substitutions
      henv hscoped sourceBelow paid bank path member admitted
  exact ⟨pending, row, execution, sameDomain, bodySize, rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
