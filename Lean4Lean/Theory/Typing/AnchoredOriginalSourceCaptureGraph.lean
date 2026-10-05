import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureSyntax
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericFamilyDeclaredPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupedFamilyReserve

/-! Recursive ORIGINAL source displays. A capture records a raw source
substitution and its actual owner occurrence, possibly in another original
environment. It does not assert a new source typing at the declared domain.
The separately retained generic frame validates its target realization. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- A map's semantic realization contains the actual generic frame, including
all queried owners in grouped slots. Its environment is never replaced by
an uncharged list of source declarations. -/
structure OriginalCaptureRealization
    {context : ContextDerivation sourceEnv U source}
    {raw : Subst} (graph : OriginalCaptureMap (common := common) context raw)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (left right : Subst) (available : Valuation) where
  frame : OriginalRichFrame sourceEnv env U registry target context locals
    (raw.comp left) (raw.comp right) available
  substitutions : Ctx.SubstEq env U target (raw.comp left) (raw.comp right) source

private theorem capture_comp (raw owner : Subst) (argument : VExpr) (common : Subst) :
    (raw.cons (argument.subst owner)).comp common =
      (raw.comp common).cons (argument.subst (owner.comp common)) := by
  funext index
  cases index with
  | zero => exact subst_subst
  | succ index => rfl

/-- A genuine same-source-expression bridge at an application. The right
side captures the application's OWN original codomain and argument; an
unrelated declared header codomain is deliberately absent. -/
theorem OriginalCaptureMap.application_result
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (argument : EndpointState sourceEnv U source a A)
    (argumentProvenance : EndpointProvenance context argument)
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (bodyProvenance : EndpointProvenance (.cons context domain) body)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (resultProvenance : EndpointProvenance context result) :
    ∃ left right : OriginalNestedDisplay U common ((B.inst a).subst raw) (.sort v),
      HEq left.node result ∧ HEq right.node body ∧
      left.raw = raw ∧ right.raw = raw.cons (a.subst raw) := by
  let captured := OriginalCaptureMap.capture graph domain graph argument argumentProvenance
  let left : OriginalNestedDisplay U common ((B.inst a).subst raw) (.sort v) := {
    sourceEnv := sourceEnv, source := source, sourceExpression := B.inst a, sourceType := .sort v
    context := context, node := result, provenance := resultProvenance, raw := raw, graph := graph
    expression_eq := rfl, type_eq := rfl }
  let right : OriginalNestedDisplay U common ((B.inst a).subst raw) (.sort v) := {
    sourceEnv := sourceEnv, source := A :: source, sourceExpression := B, sourceType := .sort v
    context := .cons context domain, node := body, provenance := bodyProvenance
    raw := raw.cons (a.subst raw), graph := captured
    expression_eq := by rw [subst_inst, inst_lift_cons]
    type_eq := rfl }
  exact ⟨left, right, HEq.rfl, HEq.rfl, rfl, rfl⟩

private theorem frame_castSubstitution_environment
    {context : ContextDerivation sourceEnv U source}
    (same : old = next)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals old old available)
    (ordered : sourceEnv.Ordered) :
    ((same ▸ frame) : OriginalRichFrame sourceEnv env U registry target context locals next next available).dependencyEnvironment ordered =
      frame.dependencyEnvironment ordered := by
  cases same
  rfl

/-- A real heterogeneous dependent capture. The previous source graph may
already contain arbitrarily many captures. Raw target typing of the next
slot comes from the selected row's actual admission and domain chain; no
source typing of the owner at the declared domain is assumed or reified. -/
theorem OriginalCaptureRealization.captureRow
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U common fieldExpression fieldType}
    {major : EndpointRef sourceEnv U common majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context headerRaw}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    (ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw)
    (owner : EndpointState ownerEnv U ownerSource argument assigned)
    (ownerProvenance : EndpointProvenance ownerContext owner)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (sourceOrdered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (headerBelow : headerEnv ≤ env)
    (tail : OriginalCaptureRealization graph env registry target locals commonSubst commonSubst available)
    (location : Located header (.ref domain))
    (steps : List (Dependency.GroupedHeaderStep headerOrdered sourceOrdered header field major))
    (ledger : tail.frame.dependencyEnvironment headerOrdered = Dependency.groupedHeaderEnvironment steps ownerInitial)
    (key : Key n) (result : Profile n)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals (headerRaw.comp commonSubst) available ownerInitial (argument.subst ownerRaw) key.anchor key.anchor)
    (input : (⟨entry.rank, entry.input⟩ : Need) = ⟨n, key.input⟩)
    (anchor : key.anchor = argument.subst (ownerRaw.comp commonSubst))
    (row : RichPiRowCertificate env U registry target locals (headerRaw.comp commonSubst) available
      relevant (.ref domain) body key result)
    (closed : available.AtomClosed) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals (headerRaw.comp commonSubst) available ownerInitial (argument.subst ownerRaw) key.anchor key.anchor,
      ∃ next : OriginalCaptureRealization (.capture graph domain ownerGraph owner ownerProvenance)
          env registry target (Locals.push locals) commonSubst commonSubst (available.push entries.needs),
        next.frame.dependencyEnvironment headerOrdered = entries.environment sourceOrdered headerOrdered
          ownerInitial (tail.frame.dependencyEnvironment headerOrdered) ∧
        next.frame.dependencyEnvironment headerOrdered =
          Dependency.groupedHeaderEnvironment (entries.ledgerStep sourceOrdered headerOrdered location :: steps) ownerInitial ∧
        Nonempty (RichCert headerEnv env U registry target body (Locals.push locals)
          ((headerRaw.cons (argument.subst ownerRaw)).comp commonSubst) relevant result row.bodyFootprint) ∧
        row.bodyFootprint.Available (available.push entries.needs) ∧
        (available.push entries.needs).AtomClosed ∧
        (⟨entry.rank, entry.input⟩ : Need) ∈ entries.needs ∧
        (∀ current ∈ entries, current.owner = entry.owner) := by
  obtain ⟨entries, nextFrame, environmentEq, ⟨certificate⟩, resources, nextClosed, coverage, whole, owners, reserve⟩ :=
    row.captureSuccessor henv formed sourceOrdered headerOrdered tail.frame key result entry input closed
  have realizationEq : (headerRaw.comp commonSubst).cons key.anchor =
      (headerRaw.cons (argument.subst ownerRaw)).comp commonSubst := by
    rw [capture_comp, anchor]
  have admitted := row.alignment.admission henv row.anchor
  obtain ⟨rawPair, _, _, _, _, _, _, _⟩ := admitted
  have substitutions : Ctx.SubstEq env U target
      ((headerRaw.comp commonSubst).cons key.anchor) ((headerRaw.comp commonSubst).cons key.anchor)
      (A :: headerSource) :=
    .cons tail.substitutions (domain.sound.defeq.mono headerBelow) rawPair
  let next : OriginalCaptureRealization (.capture graph domain ownerGraph owner ownerProvenance)
      env registry target (Locals.push locals) commonSubst commonSubst (available.push entries.needs) := {
    frame := realizationEq ▸ nextFrame
    substitutions := realizationEq ▸ substitutions }
  have computed : next.frame.dependencyEnvironment headerOrdered = entries.environment sourceOrdered headerOrdered
      ownerInitial (tail.frame.dependencyEnvironment headerOrdered) :=
    (frame_castSubstitution_environment realizationEq nextFrame headerOrdered).trans environmentEq
  refine ⟨entries, next, computed, ?_, ⟨realizationEq ▸ certificate⟩, resources, nextClosed, whole, owners⟩
  exact (computed.trans (tail.frame.group_environment sourceOrdered headerOrdered entries).symm).trans
    (tail.frame.group_ledger sourceOrdered headerOrdered location entries steps ledger)

/-- Both displayed sides are obtained from the actual application view,
including any original conversion prefix used to expose that application. -/
theorem AppView.nestedResult
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node} (view : AppView start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (graph : OriginalCaptureMap (common := common) (view.location.contextDerivation initial) raw) :
    ∃ left right : OriginalNestedDisplay U common ((view.codomainExpression.inst a).subst raw) (.sort view.bodyLevel),
      HEq left.node view.result ∧ HEq right.node view.codomain ∧
      left.raw = raw ∧ right.raw = raw.cons (a.subst raw) := by
  let domain := Classical.choose view.location.originalDomains.1
  exact graph.application_result domain view.argument (.ofLocation (.appArgument view.location) initial)
    view.codomain (.ofLocation (.appCodomain view.location) initial)
    view.result (.ofLocation (.appResult view.location) initial)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
