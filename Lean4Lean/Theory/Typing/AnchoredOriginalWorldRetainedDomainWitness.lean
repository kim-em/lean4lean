import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramDomain
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandNormalization

/-! Domain transitions preserve the exact caller scope, valuation, resource
table and generated frame. The witness retains the literal child program and
finite selected output path; it introduces no new binder interpretation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem domainPrefixedCall
    (frontier : List (World count)) (lower : WorldBelow count child parent) :
    CallBelow count (frontier ++ [child]) (frontier ++ [parent]) := by
  induction frontier with
  | nil => exact split_call (by intro world member; cases List.mem_singleton.mp member; exact lower)
  | cons world rest ih => exact ih.cons world

structure RetainedDomainOpening
    {goalRank : Nat} {goalOutput : Atom goalRank}
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) where
  domainExpression : VExpr
  bodyExpression : VExpr
  expressionEq : before.expression = .forallE domainExpression bodyExpression
  domainLevel : VLevel
  bodyLevel : VLevel
  domainWF : domainLevel.WF U
  bodyWF : bodyLevel.WF U
  domainNode : EndpointState before.sourceEnv U before.source domainExpression (.sort domainLevel)
  bodyNode : EndpointState before.sourceEnv U (domainExpression :: before.source) bodyExpression (.sort bodyLevel)
  route : PrefixRoute before.sourceEnv U before.source (.forallE domainExpression bodyExpression)
    (before.node.cast expressionEq rfl) (.pi domainWF bodyWF domainNode bodyNode)
  rank : Nat
  profile : Profile rank
  footprint : Footprint
  program : RetainedTypedProgram before.sourceEnv env U registry target domainNode before.locals before.left true profile footprint
  annotation : RetainedTypedProgramProvenance strata program
  within : WithinAbove before.controls.cutoff before.controls.fuel
    (fun control => program.certificate.stratifiedDepth (strata.headOrdinal registry) control)
  sponsored : Sponsored frontier annotation.certificate.worlds
  resources : footprint.Available before.available
  worlds : annotation.certificate.worlds ⊆ before.annotation.certificate.worlds
  depth : ∀ policy, program.certificate.headDepth policy ≤ before.program.certificate.headDepth policy
  selected : Atom rank
  member : selected ∈ profile.atoms
  nextRank : Nat
  requested : Atom nextRank
  prototypeDomain : VExpr
  prototypeBody : VExpr
  support : Profile nextRank
  rows : List (Key nextRank × Profile nextRank)
  inputPath : GeneralOutputPath env U registry target before.selected (show Atom (nextRank+1) from .pi prototypeDomain prototypeBody support rows)
  domainMember : requested ∈ support.atoms
  output : GeneralOutputPath env U registry target selected requested
  continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput domainExpression requested
  normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
    (expressionEq ▸ before.demand) (.domain inputPath domainMember continuation)
  readback : continuation.readback before.right = before.demand.readback before.right

noncomputable def RetainedDomainOpening.next
    {goalRank : Nat} {goalOutput : Atom goalRank}
    {before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (opening : RetainedDomainOpening before) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput := by
  rcases before with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
    locals, left, right, available, frame, captured, data, closed, substitutions, sourceBelow,
    originalRelevant, originalRank, originalProfile, originalFootprint, originalProgram, originalAnnotation,
    originalWithin, originalSponsored, originalResources, originalSelected, originalMember, demand, paid, bank⟩
  rcases opening with ⟨A, B, expressionEq, u, v, hu, hv, domainNode, bodyNode, route,
    rank, profile, footprint, program, annotation, within, sponsored, resources, worlds, depth,
    selected, member, nextRank, requested, prototypeDomain, prototypeBody, support, rows, inputPath, domainMember,
    output, continuation, normalized, readback⟩
  cases expressionEq
  have cost := Nat.lt_of_lt_of_le
    (binder_domain_cost (domainNode.dependencyOrigin controls.ordered)
      [bodyNode.dependencyOrigin controls.ordered] [] (frame.dependencyEnvironment controls.ordered))
    (route.dependency_cost_le controls.ordered (frame.dependencyEnvironment controls.ordered))
  have lower : WorldBelow strata.rules.length (originalCallWorld controls .fundamental domainNode captured)
      (originalCallWorld controls .fundamental node captured) :=
    original_child (richSchedule_strict cost _ _) _ _ _ _ _
  exact {
    sourceEnv := sourceEnv, source := source, context := context
    expression := A, assigned := .sort u, node := domainNode
    provenance := PrefixRoute.piDomainProvenance route provenance
    controls := controls, locals := locals, left := left, right := right
    available := available, frame := frame, captured := captured, data := data
    closed := closed, substitutions := substitutions, sourceBelow := sourceBelow
    relevant := true, rank := rank, profile := profile, footprint := footprint
    program := program, annotation := annotation
    within := within, sponsored := sponsored, resources := resources
    selected := selected, member := member, demand := .output output continuation
    paid := singletonSponsoredBelow paid lower
    bank := fun calls smaller => bank calls (smaller.trans (domainPrefixedCall frontier lower)) }

theorem RetainedDomainOpening.next_size (opening : RetainedDomainOpening before) :
    opening.next.programSize = opening.annotation.programSize := by
  rcases before with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases opening with ⟨_, _, same, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  cases same
  rfl

theorem RetainedDomainOpening.next_readback (opening : RetainedDomainOpening before) :
    opening.next.demand.readback opening.next.right = before.demand.readback before.right := by
  rcases before with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases opening with ⟨_, _, same, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, readback⟩
  cases same
  exact readback

inductive RetainedDomainTransitionWitness
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput → Type where
  | intro (opening : RetainedDomainOpening before)
      (smaller : opening.annotation.programSize < before.programSize) :
      RetainedDomainTransitionWitness before opening.next

theorem RetainedDomainTransitionWitness.readback (edge : RetainedDomainTransitionWitness before next) :
    next.demand.readback next.right = before.demand.readback before.right := by
  cases edge with
  | intro opening _ => exact opening.next_readback


/-- Execute a finite domain output action on the retained literal child. The
smaller original call, unchanged frame, and output State are constructed here. -/
theorem enterDomainProgramWitness
    {goalRank : Nat} {goalOutput : Atom goalRank}
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    {A B : VExpr} {u v : VLevel} {hu : u.WF U} {hv : v.WF U}
    (expressionEq : before.expression = .forallE A B)
    {domainNode : EndpointState before.sourceEnv U before.source A (.sort u)}
    {bodyNode : EndpointState before.sourceEnv U (A :: before.source) B (.sort v)}
    (route : PrefixRoute before.sourceEnv U before.source (.forallE A B)
      (before.node.cast expressionEq rfl) (.pi hu hv domainNode bodyNode))
    {n m : Nat} {profile : Profile n} {support : Profile m} {atom : Atom m}
    (program : RetainedTypedProgram before.sourceEnv env U registry target domainNode
      before.locals before.left true profile footprint)
    (annotation : RetainedTypedProgramProvenance strata program)
    (within : WithinAbove before.controls.cutoff before.controls.fuel
      (fun control => program.certificate.stratifiedDepth (strata.headOrdinal registry) control))
    (sponsored : Sponsored frontier annotation.certificate.worlds)
    (resources : footprint.Available before.available)
    (worlds : annotation.certificate.worlds ⊆ before.annotation.certificate.worlds)
    (depth : ∀ policy, program.certificate.headDepth policy ≤ before.program.certificate.headDepth policy)
    (smaller : annotation.programSize < before.programSize)
    (pending : PendingDomain env U registry target profile support)
    {rows : List (Key m × Profile m)}
    (inputPath : GeneralOutputPath env U registry target before.selected (show Atom (m+1) from .pi prototypeDomain prototypeBody support rows))
    (member : atom ∈ support.atoms)
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A atom)
    (readback : continuation.readback before.right = before.demand.readback before.right)
    (normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
      (expressionEq ▸ before.demand) (.domain inputPath member continuation)) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < before.programSize ∧ Nonempty (RetainedDomainTransitionWitness before next) := by
  obtain ⟨original, present, ⟨output⟩⟩ := pending.selectOriginal program.certificate.formed member
  let opening : RetainedDomainOpening before := {
    domainExpression := A, bodyExpression := B, expressionEq := expressionEq
    domainLevel := u, bodyLevel := v, domainWF := hu, bodyWF := hv
    domainNode := domainNode, bodyNode := bodyNode, route := route
    rank := n, profile := profile, footprint := footprint, program := program, annotation := annotation
    within := within, sponsored := sponsored, resources := resources, worlds := worlds, depth := depth
    selected := original, member := present, nextRank := m, requested := atom
    prototypeDomain := prototypeDomain, prototypeBody := prototypeBody, support := support, rows := rows
    inputPath := inputPath, domainMember := member
    output := output, continuation := continuation, normalized := normalized, readback := readback }
  exact ⟨opening.next, by rw [opening.next_size]; exact smaller, ⟨.intro opening smaller⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
