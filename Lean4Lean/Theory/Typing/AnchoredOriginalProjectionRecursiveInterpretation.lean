import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionClosureInterpretation
import Lean4Lean.Theory.Typing.AnchoredAtomActionCode

/-! Recursive dependent projection interpretation. Projected field
certificates are interpreted recursively as rich source syntax. Only leaves
already in the hereditary core use fixed original F calls. Native Pi and
application nodes are not asserted to belong to this pilot fragment.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

mutual
/-- The finite exact-original leaf ledger for a projected type query. -/
inductive CodeCalls (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {target : List VExpr} :
    {source : List VExpr} → (context : ContextDerivation sourceEnv U source) →
    {expression assigned : VExpr} → {node : EndpointState sourceEnv U source expression assigned} →
    {locals : List Nat} → {σ : Subst} → {relevant : Bool} → {n : Nat} →
    {profile : Profile n} → {footprint : Footprint} →
    RichCert sourceEnv env U registry target node locals σ relevant profile footprint → Prop where
  | legacy (fundamental : StateSortableFundamental env registry context node) :
      CodeCalls env registry context (.legacy (node := node) certificate)
  | observe (calls : ValueCalls env registry context observation) :
      CodeCalls env registry context (.observe observation formed)
  | codeAction (calls : CodeCalls env registry context certificate) :
      CodeCalls env registry context (.observe (.action (.code certificate) action) formed)
  | route (calls : CodeCalls env registry context certificate) :
      CodeCalls env registry context (.route path certificate)
  | union (first : CodeCalls env registry context left) (second : CodeCalls env registry context right) :
      CodeCalls env registry context (.union left right)
  | pad (calls : CodeCalls env registry context certificate) :
      CodeCalls env registry context (.pad certificate)
  | down (calls : CodeCalls env registry context certificate) :
      CodeCalls env registry context (.down certificate)
  | map (calls : CodeCalls env registry context certificate) :
      CodeCalls env registry context (.map view certificate)
  | support (calls : CodeCalls env registry context certificate) :
      CodeCalls env registry context (.support action certificate)
  | select (calls : CodeCalls env registry context certificate) :
      CodeCalls env registry context (.select certificate member)

inductive ValueCalls (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {target : List VExpr} :
    {source : List VExpr} → (context : ContextDerivation sourceEnv U source) →
    {expression assigned : VExpr} → {node : EndpointState sourceEnv U source expression assigned} →
    {locals : List Nat} → {σ : Subst} → {n : Nat} →
    {profile : Profile n} → {footprint : Footprint} →
    RichObs sourceEnv env U registry target node locals σ profile footprint → Prop where
  | legacy (fundamental : StateHereditaryFundamental env registry context node) :
      ValueCalls env registry context (.legacy (node := node) observation)
  | projection {source : List VExpr} {context : ContextDerivation sourceEnv U source}
      {name : Name} {index : Nat} {value assigned : VExpr}
      {node : EndpointState sourceEnv U source (.proj name index value) assigned}
      {head : ProjectionHead node} {record : RecordData (Profile n)}
      {request : DataRequest (Profile n)}
      {locals : List Nat} {σ : Subst} {support : Profile n}
      {majorFootprint fieldFootprint : Footprint}
      {nameEq : record.family.name = name} {member : (index, request) ∈ record.fields}
      {majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major))
        locals σ (.singleton (n := n + 1) (.record record)) majorFootprint}
      {fieldCode : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint}
      {typed : request.input.HasType support}
      {alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ)}
      (major : ValueCalls env registry context majorQuery)
      (field : CodeCalls env registry context fieldCode) :
      ValueCalls env registry context
        (.projection head nameEq member majorQuery fieldCode typed alignment)
  | route (calls : ValueCalls env registry context observation) :
      ValueCalls env registry context (.route path observation)
  | action (calls : ValueCalls env registry context observation) :
      ValueCalls env registry context (.action observation action)
  | select (calls : ValueCalls env registry context observation) :
      ValueCalls env registry context (.select observation member)
end

/-- The exposed natural type is enough to interpret a value request and
extract sortable code. Ambient source-type coherence remains a separate
obligation when a caller asks for its particular assigned type. -/
structure ValueSemantics (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (value : VExpr) (demand : Profile n) where
  type : VExpr
  support : Profile n
  typed : demand.HasType support
  formed : support.HasType (.sort true)
  code : TypeRelated env U registry target type type support
  related : Related env U registry target value value type demand support

mutual
theorem CodeCalls.interpret
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression assigned}
    {certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (calls : CodeCalls env registry context certificate)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target context locals σ σ available)
    (resources : footprint.Available available) :
    TypeRelated env U registry target (expression.subst σ) (expression.subst σ) profile := by
  match calls with
  | .legacy (certificate := source) fundamental =>
    obtain ⟨answer⟩ := fundamental target locals σ σ available closed formed substitutions tails source resources
    exact answer.related
  | .observe (formed := sortFormed) valueCalls =>
    obtain ⟨value⟩ := valueCalls.interpret henv hscoped closed formed substitutions tails resources
    exact value.related.code_of_sortable henv hscoped formed sortFormed
  | .codeAction (certificate := certificate) (action := action) child =>
    exact (action.toCode certificate.formed).codeMap henv hscoped
      (child.interpret henv hscoped closed formed substitutions tails resources)
  | .route child => exact child.interpret henv hscoped closed formed substitutions tails resources
  | .union first second =>
    have left := first.interpret henv hscoped closed formed substitutions tails
      (fun index need member => resources index need (List.mem_append_left _ member))
    have right := second.interpret henv hscoped closed formed substitutions tails
      (fun index need member => resources index need (List.mem_append_right _ member))
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim (fun h => left.singleton h) (fun h => right.singleton h)
  | .pad child => exact (child.interpret henv hscoped closed formed substitutions tails resources).pad henv
  | .down child => exact (child.interpret henv hscoped closed formed substitutions tails resources).down henv
  | .map (view := view) child =>
    exact view.codeMap henv hscoped (child.interpret henv hscoped closed formed substitutions tails resources)
  | .support (action := action) child =>
    exact action.codeMap henv hscoped (child.interpret henv hscoped closed formed substitutions tails resources)
  | .select (member := member) child =>
    exact (child.interpret henv hscoped closed formed substitutions tails resources).singleton member
termination_by sizeOf certificate

theorem ValueCalls.interpret
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression assigned}
    {observation : RichObs sourceEnv env U registry target node locals σ profile footprint}
    (calls : ValueCalls env registry context observation)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target context locals σ σ available)
    (resources : footprint.Available available) :
    Nonempty (ValueSemantics env U registry target (expression.subst σ) profile) := by
  match calls with
  | .legacy (observation := source) fundamental =>
    obtain ⟨answer⟩ := fundamental target locals σ σ available closed formed substitutions tails source resources
    exact ⟨⟨_, _, answer.requestedTyped, answer.requestedCertificate.formed,
      answer.typeCode.lower henv answer.bound, answer.requestedRelated henv formed⟩⟩
  | .projection (head := head) (nameEq := nameEq) (member := member)
      (fieldCode := fieldCode) (typed := typed) (alignment := alignment) majorCalls fieldCalls =>
    obtain ⟨major⟩ := majorCalls.interpret henv hscoped closed formed substitutions tails
      (fun index need member => resources index need (List.mem_append_left _ member))
    have field := fieldCalls.interpret henv hscoped closed formed substitutions tails
      (fun index need member => resources index need (List.mem_append_right _ member))
    have projected := major.related.projectRecord henv hscoped formed member
    exact ⟨⟨_, _, typed, fieldCode.formed, field, by
      simpa only [nameEq, subst] using alignment.related henv typed field projected⟩⟩
  | .route child => exact child.interpret henv hscoped closed formed substitutions tails resources
  | .action (action := action) child =>
    obtain ⟨value⟩ := child.interpret henv hscoped closed formed substitutions tails resources
    exact ⟨⟨_, _, action.typed value.typed, action.support.preservesSort value.formed,
      action.support.codeMap henv hscoped value.code,
      action.termMap henv hscoped formed value.typed value.related⟩⟩
  | .select (member := member) child =>
    obtain ⟨value⟩ := child.interpret henv hscoped closed formed substitutions tails resources
    exact ⟨⟨_, _, value.typed.singleton_of_mem member, value.formed, value.code,
      value.related.singleton_of_mem member⟩⟩
termination_by sizeOf observation
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
