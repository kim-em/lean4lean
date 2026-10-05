import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionPrefixTransfer
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSeededFrame

/-! Interpret typed projection queries at their actual original inferred
types. The computed projection head supplies the original major and field
premises; original conversion children replay the field certificate in both
directions. No primitive-head restriction or outgoing metadata assumption
is imposed on the queried constructor argument.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure ProjectionQueryValue
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression assigned : VExpr) (demand : Profile n) where
  support : Profile n
  footprint : Footprint
  certificate : CodeCert env U registry target locals σ assigned support footprint
  resources : footprint.Available available
  typed : demand.HasType support
  code : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) support
  related : Related env U registry target (expression.subst σ) (expression.subst σ)
    (assigned.subst σ) demand support

private theorem codeUnion
    (left : TypeRelated env U registry target A A p)
    (right : TypeRelated env U registry target A A q) :
    TypeRelated env U registry target A A (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom member
  exact (List.mem_append.mp member).elim
    (fun h => left.singleton h) (fun h => right.singleton h)

/-- The assigned-type code is obtained from the original field child and
both traversals of the actual conversion prefix. -/
theorem ProjectionHead.assignedCode
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major assigned : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry head.route initial)
    (fieldFundamental : StateFundamental env registry initial head.field)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available)
    (certificate : CodeCert env U registry target locals σ assigned support footprint)
    (resources : footprint.Available available) :
    Nonempty (CodeTransferResult env U registry target locals σ σ available
      assigned assigned support) := by
  have fieldTransfer : GradedTransfer env U registry target locals σ σ available
      head.fieldType head.fieldType (.sort head.fieldLevel) := (fieldFundamental target locals σ σ available
    closed formed substitutions tails).1
  obtain ⟨natural⟩ := head.route.replayAcrossOriginal henv hscoped below initial closed formed
    substitutions tails.forward calls
    (fun certificate resources => certificate.transfer_graded henv hscoped formed closed
      fieldTransfer resources) certificate resources
  exact head.route.restoreOriginal henv hscoped below initial closed formed substitutions
    tails.forward calls natural

/-- Interpret a typed query at the original projection argument, including
all its conversion prefixes and finite wrappers. -/
theorem ProjectionObs.diagonalAt
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major assigned : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry head.route initial)
    (fieldFundamental : StateFundamental env registry initial head.field)
    (majorFundamental : DerivationFundamental env registry initial head.major)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available)
    (query : ProjectionObs env registry target node locals σ demand footprint)
    (resources : footprint.Available available) :
    Nonempty (ProjectionQueryValue env U registry target locals σ available
      (.proj name index major) assigned demand) := by
  induction query with
  | field nameEq member majorObservation fieldCertificate typed alignment =>
    have majorResources := fun i need member => resources i need (List.mem_append_left _ member)
    have fieldResources := fun i need member => resources i need (List.mem_append_right _ member)
    have majorTransfer : GradedTransfer env U registry target locals σ σ available
        major major (mkApps (.const name head.levels) (head.parameters ++ head.indices)) :=
      (majorFundamental.right henv hscoped target locals σ σ available
      closed formed substitutions tails).1
    obtain ⟨majorAnswer⟩ := majorTransfer majorObservation majorResources
    obtain ⟨code⟩ := head.assignedCode henv hscoped below initial calls fieldFundamental
      closed formed substitutions tails fieldCertificate fieldResources
    have fields := (majorAnswer.requestedRelated henv formed).projectRecord henv hscoped formed member
    exact ⟨{
      support := _, footprint := _, certificate := fieldCertificate, resources := fieldResources
      typed := typed, code := code.related
      related := by simpa only [nameEq, subst] using alignment.related henv typed code.related fields }⟩
  | @empty n =>
    exact ⟨{
      support := .empty, footprint := []
      certificate := .seed .empty (Profile.HasType.empty (Profile.WF.sort true))
      resources := fun _ _ member => nomatch member
      typed := Profile.HasType.empty Profile.WF.empty
      code := by cases n <;> intro Δ ρ future atom member <;> cases member
      related := by cases n <;> intro atom member <;> cases member }⟩
  | union left right ihLeft ihRight =>
    obtain ⟨first⟩ := ihLeft (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨second⟩ := ihRight (fun i need member => resources i need (List.mem_append_right _ member))
    have wf := first.typed.wf_type.union second.typed.wf_type
    have code := codeUnion first.code second.code
    have leftTyped := first.typed.enlarge (Profile.le_union_left _ _) wf
    have rightTyped := second.typed.enlarge (Profile.le_union_right _ _) wf
    exact ⟨{
      support := first.support.union second.support
      footprint := first.footprint ++ second.footprint
      certificate := .union first.certificate second.certificate
      resources := fun i need member => (List.mem_append.mp member).elim
        (first.resources i need) (second.resources i need)
      typed := leftTyped.union rightTyped, code := code
      related := (first.related.retag henv leftTyped code).union
        (second.related.retag henv rightTyped code) }⟩
  | view child change ih =>
    obtain ⟨answer⟩ := ih resources
    exact ⟨{
      support := change.mapType answer.support
      footprint := answer.footprint, certificate := .map change answer.certificate
      resources := answer.resources, typed := change.mapType_typed answer.typed
      code := change.codeMap henv hscoped answer.code
      related := change.termMap henv hscoped formed answer.related }⟩
  | unpad child ih =>
    obtain ⟨answer⟩ := ih resources
    exact ⟨{
      support := answer.support.down
      footprint := answer.footprint, certificate := .down answer.certificate
      resources := answer.resources, typed := answer.typed.pad_inv
      code := answer.code.down henv, related := answer.related.unpad henv formed }⟩
  | raise child bound ih =>
    obtain ⟨answer⟩ := ih resources
    exact ⟨{
      support := raiseProfile _ bound answer.support
      footprint := answer.footprint, certificate := answer.certificate.raise bound
      resources := answer.resources, typed := Profile.HasType.raise bound answer.typed
      code := TypeRelated.raise henv bound answer.code
      related := Related.raise henv bound answer.related }⟩

/-- The complete merged seed/cut query constructs the argument guard at its
actual inferred source type. All recursive obligations name original field,
major and conversion children, regardless of the eventual constructor domain. -/
theorem ProjectionSeededFrame.ofOriginalEndpointExact
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major A B : VExpr}
    (node : EndpointState sourceEnv U source (.proj name index major) A)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry (projectionHead node).route initial)
    (fieldFundamental : StateFundamental env registry initial (projectionHead node).field)
    (majorFundamental : DerivationFundamental env registry initial (projectionHead node).major)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available)
    (seed : ProjectionArgumentSeed env registry target node locals σ available)
    {result : Profile n} {required outside : Footprint}
    (collected : ProjectionFactoredArguments env registry target node locals σ available
      required outside (max n seed.rank))
    (outsideResources : outside.Available available)
    (body : CodeCert env U registry target (Locals.push locals)
      (σ.cons ((VExpr.proj name index major).subst σ)) B
      (raiseProfile collected.rank (Nat.le_trans (Nat.le_max_left _ _) collected.bound) result) required) :
    ∃ frame : ProjectionSeededFrame env registry target node locals σ available B result,
      frame.seed = seed ∧ frame.required = required ∧ frame.outside = outside ∧
      HEq frame.collected collected := by
  let combined := ProjectionObs.union
    (ProjectionObs.raise seed.query (Nat.le_trans (Nat.le_max_right _ _) collected.bound))
    collected.query
  have combinedResources : (seed.footprint ++ collected.footprint).Available available :=
    fun i need member => (List.mem_append.mp member).elim
      (seed.resources i need) (collected.resources i need)
  obtain ⟨answer⟩ := ProjectionObs.diagonalAt (projectionHead node) henv hscoped below initial
    calls fieldFundamental majorFundamental closed formed substitutions tails combined combinedResources
  have raw : env.HasType U target ((VExpr.proj name index major).subst σ) (A.subst σ) :=
    (node.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  exact ⟨{
    seed := seed, required := required, outside := outside, outsideResources := outsideResources
    collected := collected, support := answer.support, domainFootprint := answer.footprint
    domain := answer.certificate, domainResources := answer.resources
    guard := ⟨answer.typed, answer.certificate.formed, .refl, answer.code,
      ⟨raw, raw, _, answer.typed, answer.certificate.formed, answer.code,
        answer.related, answer.related⟩⟩
    body := body }, rfl, rfl, rfl, HEq.rfl⟩

theorem ProjectionSeededFrame.ofOriginalEndpoint
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {name : Name} {index : Nat} {major A B : VExpr}
    (node : EndpointState sourceEnv U source (.proj name index major) A)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U source)
    (calls : PrefixCall.Fundamentals env registry (projectionHead node).route initial)
    (fieldFundamental : StateFundamental env registry initial (projectionHead node).field)
    (majorFundamental : DerivationFundamental env registry initial (projectionHead node).major)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : TailPairedFits env registry target initial locals σ σ available)
    (seed : ProjectionArgumentSeed env registry target node locals σ available)
    {result : Profile n} {required outside : Footprint}
    (collected : ProjectionFactoredArguments env registry target node locals σ available
      required outside (max n seed.rank))
    (outsideResources : outside.Available available)
    (body : CodeCert env U registry target (Locals.push locals)
      (σ.cons ((VExpr.proj name index major).subst σ)) B
      (raiseProfile collected.rank (Nat.le_trans (Nat.le_max_left _ _) collected.bound) result) required) :
    Nonempty (ProjectionSeededFrame env registry target node locals σ available B result) := by
  obtain ⟨frame, _⟩ := ProjectionSeededFrame.ofOriginalEndpointExact node henv hscoped below
    initial calls fieldFundamental majorFundamental closed formed substitutions tails
    seed collected outsideResources body
  exact ⟨frame⟩

/-- Both semantic children are strictly smaller at the exact original
captured source context, even before counting any conversion prefix. -/
theorem ProjectionHead.children_schedule
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    {name : Name} {index : Nat} {major assigned : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (initial : ContextDerivation sourceEnv U source) :
    schedule .fundamental (Closure.close head.field.origin initial.closures).cost <
      schedule .fundamental (Closure.close node.origin initial.closures).cost ∧
    schedule .fundamental (Closure.close head.major.origin initial.closures).cost <
      schedule .fundamental (Closure.close node.origin initial.closures).cost := by
  have parent := Nat.mul_le_mul_right (1 + environmentCost initial.closures) head.route.weight_le
  constructor <;> apply schedule_strict
  · exact Nat.lt_of_lt_of_le
      (original_child_same_environment (Origin.rule_child (children := [head.field.origin, head.major.origin])
        (by simp)) initial.closures) parent
  · exact Nat.lt_of_lt_of_le
      (original_child_same_environment (Origin.rule_child (children := [head.field.origin, head.major.origin])
        (by simp)) initial.closures) parent

theorem ProjectionHead.conversion_schedule
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    {name : Name} {index : Nat} {major assigned : VExpr}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (initial : ContextDerivation sourceEnv U source)
    {callSource : List VExpr} {left right type : VExpr}
    {original : Derivation sourceEnv U callSource left right type}
    (call : PrefixCall head.route original) :
    schedule .fundamental
      (Closure.close original.origin (call.contextDerivation initial).closures).cost <
      schedule .fundamental (Closure.close node.origin initial.closures).cost := by
  apply schedule_strict
  rw [PrefixCall.contextDerivation_closures]
  exact call.cost_lt initial.closures

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
