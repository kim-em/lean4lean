import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderSinglePi

/-! The two original Pi exposures of a genuine two-parameter header.  Both
locations and their context lineage are selected from the actual header proof. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem doubleHeaderDomain_eq
    (signature : ConstantTelescope expression) (domains : signature.domains = [C, D]) :
    expression = .forallE C (.forallE D signature.result) := by
  simpa only [domains, wrapForalls, List.foldr_cons, List.foldr_nil] using signature.type_eq

structure HeaderDoublePi
    {levels : List VLevel} {U : Nat}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (signature : ConstantTelescope (info.type.instL levels))
    (domains : signature.domains = [C, D]) where
  cu : VLevel
  firstV : VLevel
  dv : VLevel
  w : VLevel
  hcu : cu.WF U
  firstVWF : firstV.WF U
  hdv : dv.WF U
  hw : w.WF U
  firstDomain : EndpointRef origin.source U [] C (.sort cu)
  firstBody : EndpointState origin.source U [C] (.forallE D signature.result) (.sort firstV)
  secondDomain : EndpointRef origin.source U [C] D (.sort dv)
  body : EndpointState origin.source U [D, C] signature.result (.sort w)
  firstLocation : Located (origin.familyHeader levelsWF).reference (.ref firstDomain)
  firstLineage : firstLocation.contextDerivation .nil = .nil
  bodyLocation : Located (origin.familyHeader levelsWF).reference firstBody
  bodyLineage : bodyLocation.contextDerivation .nil = .cons .nil firstDomain
  secondLocation : Located (origin.familyHeader levelsWF).reference (.ref secondDomain)
  secondLineage : secondLocation.contextDerivation .nil = .cons .nil firstDomain
  outerRoute : PrefixRoute origin.source U [] (.forallE C (.forallE D signature.result))
    ((EndpointState.ref (origin.familyHeader levelsWF).reference).cast
      (doubleHeaderDomain_eq signature domains) rfl)
    (.pi hcu firstVWF (.ref firstDomain) firstBody)
  innerRoute : PrefixRoute origin.source U [C] (.forallE D signature.result) firstBody
    (.pi hdv hw (.ref secondDomain) body)

private theorem transport_context
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {first last : EndpointState sourceEnv U source expression assigned}
    (equal : first = last) (location : Located root first)
    (initial : ContextDerivation sourceEnv U rootSource) :
    (equal ▸ location).contextDerivation initial = location.contextDerivation initial := by
  cases equal
  rfl

private theorem doubleHeaderPiExists
    {levels : List VLevel} {U : Nat}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (signature : ConstantTelescope (info.type.instL levels))
    (domains : signature.domains = [C, D]) :
    Nonempty (HeaderDoublePi origin levelsWF signature domains) := by
  let outer := piPrefix ((Located.here (root := (origin.familyHeader levelsWF).reference)).castExpression
    (doubleHeaderDomain_eq signature domains))
  obtain ⟨firstDomain, firstEq⟩ := outer.view.location.originalDomains.1
  let firstLocation : Located (origin.familyHeader levelsWF).reference (.ref firstDomain) :=
    firstEq ▸ .piDomain outer.view.location
  have firstLineage : firstLocation.contextDerivation .nil = .nil := by
    cases firstLocation.contextDerivation .nil
    rfl
  let bodyLocation := Located.piBody outer.view.location
  have bodyLineage : bodyLocation.contextDerivation .nil = .cons .nil firstDomain := by
    change ContextDerivation.cons (outer.view.location.contextDerivation .nil)
      (Classical.choose outer.view.location.originalDomains.1) = _
    have same := EndpointState.ref.inj ((Classical.choose_spec outer.view.location.originalDomains.1).symm.trans firstEq)
    rw [same]
    cases outer.view.location.contextDerivation .nil
    rfl
  let inner := piPrefix bodyLocation
  obtain ⟨secondDomain, secondEq⟩ := inner.view.location.originalDomains.1
  let secondLocation : Located (origin.familyHeader levelsWF).reference (.ref secondDomain) :=
    secondEq ▸ .piDomain inner.view.location
  have secondLineage : secondLocation.contextDerivation .nil = .cons .nil firstDomain := by
    have same : secondLocation.contextDerivation .nil = inner.view.location.contextDerivation .nil := by
      exact transport_context secondEq (.piDomain inner.view.location) .nil
    rw [same, ← inner.location_eq, PrefixRoute.locate_contextDerivation]
    exact bodyLineage
  exact ⟨⟨outer.view.domainLevel, outer.view.bodyLevel, inner.view.domainLevel, inner.view.bodyLevel,
    outer.view.domainWF, outer.view.bodyWF, inner.view.domainWF, inner.view.bodyWF,
    firstDomain, outer.view.body, secondDomain, inner.view.body, firstLocation, firstLineage,
    bodyLocation, bodyLineage, secondLocation, secondLineage, firstEq ▸ outer.route, secondEq ▸ inner.route⟩⟩

noncomputable def _root_.Lean4Lean.VEnv.ConstantHeaderOrigin.doublePiSyntax
    {levels : List VLevel} {U : Nat}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (signature : ConstantTelescope (info.type.instL levels))
    (domains : signature.domains = [C, D]) :
    HeaderDoublePi origin levelsWF signature domains :=
  Classical.choice (doubleHeaderPiExists origin levelsWF signature domains)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
