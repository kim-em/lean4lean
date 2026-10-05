import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

private theorem located_node_context
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {a b : EndpointState sourceEnv U source expression assigned}
    (equal : a = b) (location : Located root a)
    (initial : ContextDerivation sourceEnv U rootSource) :
    (equal ▸ location).contextDerivation initial = location.contextDerivation initial := by
  cases equal
  rfl

/-- A finite telescope of actual destination header occurrences. Conversion
prefixes and dependent domain references are retained, never reified. -/
inductive OriginalConstructorSpine
    {sourceEnv : VEnv} {U : Nat}
    {header : EndpointRef sourceEnv U [] declaredType (.sort headerLevel)} (result : VExpr) :
    {source : List VExpr} → (context : ContextDerivation sourceEnv U source) →
    (domains : List VExpr) → {level : VLevel} →
    EndpointState sourceEnv U source (wrapForalls domains result) (.sort level) → Type where
  | terminal {context : ContextDerivation sourceEnv U source}
      {node : EndpointState sourceEnv U source result (.sort level)}
      (location : Located header node) (lineage : location.contextDerivation .nil = context) :
      OriginalConstructorSpine (header := header) result context [] node
  | binder {context : ContextDerivation sourceEnv U source}
      {domain : EndpointRef sourceEnv U source A (.sort u)}
      {body : EndpointState sourceEnv U (A :: source) (wrapForalls domains result) (.sort v)}
      {node : EndpointState sourceEnv U source (wrapForalls (A :: domains) result) (.sort level)}
      (hu : u.WF U) (hv : v.WF U)
      (route : PrefixRoute sourceEnv U source (.forallE A (wrapForalls domains result)) node
        (.pi hu hv (.ref domain) body))
      (location : Located header (.ref domain))
      (lineage : location.contextDerivation .nil = context)
      (child : OriginalConstructorSpine (header := header) result (.cons context domain) domains body) :
      OriginalConstructorSpine (header := header) result context (A :: domains) node

private theorem locationCastContext
    {header : EndpointRef sourceEnv U [] declaredType (.sort headerLevel)}
    {first second : EndpointState sourceEnv U source expression assigned}
    (same : first = second) (location : Located header first) :
    (same ▸ location).contextDerivation .nil = location.contextDerivation .nil := by
  cases same
  rfl

/-- Every literal telescope in an actual sorted header has a complete
original spine, including all conversion prefixes and the zero-binder case. -/
theorem originalConstructorSpine
    {sourceEnv : VEnv} {U : Nat}
    {header : EndpointRef sourceEnv U [] declaredType (.sort headerLevel)}
    {source : List VExpr} {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (wrapForalls domains result) (.sort level)}
    (location : Located header node) (lineage : location.contextDerivation .nil = context) :
    Nonempty (OriginalConstructorSpine (header := header) result context domains node) := by
  induction domains generalizing source level with
  | nil => exact ⟨.terminal location lineage⟩
  | cons A domains ih =>
    let selected := piPrefix location
    obtain ⟨domain, domainEq⟩ := selected.view.location.originalDomains.1
    let domainLocation : Located header (.ref domain) := domainEq ▸ .piDomain selected.view.location
    have selectedContext : selected.view.location.contextDerivation .nil = context := by
      rw [← selected.location_eq, PrefixRoute.locate_contextDerivation]
      exact lineage
    have domainLineage : domainLocation.contextDerivation .nil = context := by
      exact (locationCastContext domainEq (.piDomain selected.view.location)).trans selectedContext
    have bodyLineage : (Located.piBody selected.view.location).contextDerivation .nil =
        .cons context domain := by
      change ContextDerivation.cons (selected.view.location.contextDerivation .nil)
        (Classical.choose selected.view.location.originalDomains.1) = _
      rw [selectedContext]
      exact congrArg (ContextDerivation.cons context)
        (EndpointState.ref.inj ((Classical.choose_spec selected.view.location.originalDomains.1).symm.trans domainEq))
    obtain ⟨child⟩ := ih (.piBody selected.view.location) bodyLineage
    exact ⟨.binder selected.view.domainWF selected.view.bodyWF
      (domainEq ▸ selected.route) domainLocation domainLineage child⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
