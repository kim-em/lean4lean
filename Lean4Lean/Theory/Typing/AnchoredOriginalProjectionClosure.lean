import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSubstitution

/-! One retained original projection leaf under a known source instantiation.
The template's source typing and field certificate stay in the original
binder context. The captured argument is an actual original endpoint; finite
query replacements and their leaves are retained alongside it. In particular
this file never constructs an original typing for a substituted projection.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

def RichArgumentSupply.footprint
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available needs) : Footprint :=
  match supply with
  | .nil => []
  | .cons value tail => value.footprint ++ tail.footprint

theorem RichArgumentSupply.available {available : Valuation}
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available needs) :
    supply.footprint.Available available := by
  induction supply with
  | nil => intro _ _ member; cases member
  | cons value tail ih =>
    intro index need member
    exact (List.mem_append.mp member).elim (value.resources index need) (ih index need)

/-- The query uses the original projection's source context. `argument`
and `domain` are retained separately because lookup must charge both original
closures, even when their raw expressions happen to coincide. -/
structure InstantiatedProjectionLeaf
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {A argumentExpression major assigned : VExpr} {domainLevel : VLevel}
    (domain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argument : EndpointRef sourceEnv U source argumentExpression A)
    (template : EndpointRef sourceEnv U (A :: source) (.proj name index major) assigned)
    (context : ContextDerivation sourceEnv U source)
    (locals : List Nat) (σ : Subst) (available : Valuation) (demand : Profile n) where
  head : ProjectionHead (.ref template)
  record : RecordData (Profile n)
  request : DataRequest (Profile n)
  requested : request.input = demand
  nameEq : record.family.name = name
  member : (index, request) ∈ record.fields
  majorFootprint : Footprint
  majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major)) (Locals.push locals)
    (σ.cons (argumentExpression.subst σ)) (.singleton (n := n + 1) (.record record)) majorFootprint
  support : Profile n
  fieldFootprint : Footprint
  fieldCode : RichCert sourceEnv env U registry target head.field (Locals.push locals)
    (σ.cons (argumentExpression.subst σ)) true support fieldFootprint
  typed : demand.HasType support
  alignment : DomainChain env U registry target demand request.domain
    (head.fieldType.subst (σ.cons (argumentExpression.subst σ)))
  captureRank : Nat
  packed : Profile captureRank
  outside : Footprint
  pack : BinderPack captureRank packed (majorFootprint ++ fieldFootprint) outside
  outsideAvailable : outside.Available available
  replacements : RichArgumentSupply sourceEnv env U registry target (.ref argument) locals σ available
    ((majorFootprint ++ fieldFootprint).localNeeds ++
      (majorFootprint ++ fieldFootprint).localNeeds.flatMap Need.singletons)

namespace InstantiatedProjectionLeaf
variable {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
  {registry : CanonicalHead.Registry} {A argumentExpression major assigned : VExpr}
  {domainLevel : VLevel} {name : Name} {index : Nat}
  {domain : EndpointRef sourceEnv U source A (.sort domainLevel)}
  {argument : EndpointRef sourceEnv U source argumentExpression A}
  {template : EndpointRef sourceEnv U (A :: source) (.proj name index major) assigned}
  {context : ContextDerivation sourceEnv U source} {locals : List Nat} {σ : Subst}
  {available : Valuation} {n : Nat} {demand : Profile n}

def footprint
    (leaf : InstantiatedProjectionLeaf sourceEnv env U registry target domain argument template context
      locals σ available demand) : Footprint := leaf.outside ++ leaf.replacements.footprint

theorem resources
    (leaf : InstantiatedProjectionLeaf sourceEnv env U registry target domain argument template context
      locals σ available demand) : leaf.footprint.Available available := by
  intro index need member
  exact (List.mem_append.mp member).elim (leaf.outsideAvailable index need)
    (leaf.replacements.available index need)

def query
    (leaf : InstantiatedProjectionLeaf sourceEnv env U registry target domain argument template context
      locals σ available demand) :
    RichObs sourceEnv env U registry target (.ref template) (Locals.push locals)
      (σ.cons (argumentExpression.subst σ)) demand (leaf.majorFootprint ++ leaf.fieldFootprint) := by
  have query := RichObs.projection leaf.head leaf.nameEq leaf.member leaf.majorQuery leaf.fieldCode
    (leaf.requested.symm ▸ leaf.typed) (leaf.requested.symm ▸ leaf.alignment)
  simpa only [leaf.requested] using query

/-- The same original projected leaf can be used as a formation query. The
finite captured resources do not change and no legacy erasure is involved. -/
def certificate
    (leaf : InstantiatedProjectionLeaf sourceEnv env U registry target domain argument template context
      locals σ available demand) (formed : demand.HasType (.sort relevant)) :
    RichCert sourceEnv env U registry target (.ref template) (Locals.push locals)
      (σ.cons (argumentExpression.subst σ)) relevant demand (leaf.majorFootprint ++ leaf.fieldFootprint) :=
  .observe leaf.query formed

/-- Realizing the displayed substituted projection gives exactly the raw
term used by the retained template query. -/
theorem realizesProjection
    (leaf : InstantiatedProjectionLeaf sourceEnv env U registry target domain argument template context
      locals σ available demand) :
    ((VExpr.proj name index major).inst argumentExpression).subst σ =
      (VExpr.proj name index major).subst (σ.cons (argumentExpression.subst σ)) := by
  simp only [subst_inst, inst_lift_cons]

/-- The frozen request's declared-field endpoint is unchanged by retaining
the source action on both the projection template and its field certificate. -/
theorem realizesField
    (leaf : InstantiatedProjectionLeaf sourceEnv env U registry target domain argument template context
      locals σ available demand) :
    (leaf.head.fieldType.inst argumentExpression).subst σ =
      leaf.head.fieldType.subst (σ.cons (argumentExpression.subst σ)) := by
  simp only [subst_inst, inst_lift_cons]

/-- Raw soundness is derived from the two original references. It is an
output theorem, never a source semantic premise for the suspended query. -/
theorem sound
    (leaf : InstantiatedProjectionLeaf sourceEnv env U registry target domain argument template context
      locals σ available demand) (henv : sourceEnv.Ordered)
    (formed : OnCtx source (sourceEnv.IsType U)) :
    sourceEnv.HasType U source ((VExpr.proj name index major).inst argumentExpression)
      (assigned.inst argumentExpression) :=
  IsDefEq.instDF henv formed template.sound.defeq argument.sound.defeq

end InstantiatedProjectionLeaf

/-- Construct the retained leaf directly from its original projection
constructor and the finite binder replacement list. There is no endpoint for
the instantiated projection among the input arguments. -/
def retainProjectionInst
    (context : ContextDerivation sourceEnv U source)
    (domain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argument : EndpointRef sourceEnv U source argumentExpression A)
    (template : EndpointRef sourceEnv U (A :: source) (.proj name index major) assigned)
    (head : ProjectionHead (.ref template))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (majorQuery : RichObs sourceEnv env U registry target (.ref (.right head.major)) (Locals.push locals)
      (σ.cons (argumentExpression.subst σ)) (.singleton (n := n + 1) (.record record)) majorFootprint)
    (fieldCode : RichCert sourceEnv env U registry target head.field (Locals.push locals)
      (σ.cons (argumentExpression.subst σ)) true support fieldFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain
      (head.fieldType.subst (σ.cons (argumentExpression.subst σ))))
    (pack : BinderPack captureRank packed (majorFootprint ++ fieldFootprint) outside)
    (outsideAvailable : outside.Available available)
    (replacements : RichArgumentSupply sourceEnv env U registry target (.ref argument) locals σ available
      ((majorFootprint ++ fieldFootprint).localNeeds ++
        (majorFootprint ++ fieldFootprint).localNeeds.flatMap Need.singletons)) :
    InstantiatedProjectionLeaf sourceEnv env U registry target domain argument template context
      locals σ available request.input :=
  ⟨head, record, request, rfl, nameEq, member, majorFootprint, majorQuery, support,
    fieldFootprint, fieldCode, typed, alignment, captureRank, packed, outside, pack, outsideAvailable, replacements⟩

/-- For an actual original beta rule the captured projection template and
the actual instantiated child fit below its existing product reserve. The
proof retains both argument and domain closures in the source environment. -/
theorem retainedProjection_beta_schedule
    (hu : u.WF U) (hv : v.WF U)
    (domain : Derivation sourceEnv U source A A (.sort u))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort v))
    (body : Derivation sourceEnv U (A :: source) (.proj name index major) (.proj name index major) B)
    (argument : Derivation sourceEnv U source a a A)
    (result : Derivation sourceEnv U source (B.inst a) (B.inst a) (.sort v))
    (instantiated : Derivation sourceEnv U source
      ((VExpr.proj name index major).inst a) ((VExpr.proj name index major).inst a) (B.inst a))
    (captured : List Closure) :
    schedule .coherence
      ((Closure.close instantiated.origin captured).cost +
        (Closure.close body.origin
          (.bundle (.close argument.origin captured) (.close domain.origin captured) :: captured)).cost) <
      schedule .fundamental
        ((Closure.close (Derivation.beta hu hv domain codomain body argument result instantiated).origin captured).cost) :=
  Derivation.beta_comparison_schedule hu hv domain codomain body argument result instantiated captured

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
