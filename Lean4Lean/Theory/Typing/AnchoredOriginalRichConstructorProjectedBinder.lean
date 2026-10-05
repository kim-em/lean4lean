import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyProjectedBinder
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorPlanResult
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichProjectedDomain

/-! A captured value keeps its natural request domain while an actual
projected declaration-domain certificate supplies the binder alignment.
The same rich projected child enters both the native constructor plan and its
native Pi type certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- This step obtains the rich domain child from an actual prior record
slot. The only recursive source result is the genuine remaining constructor
plan; no domain code, guard, or alignment is a caller-supplied oracle. -/
theorem RichConstructorPlanResult.projectedBinder
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource (.proj recordName index (.bvar slot)) (.sort u)}
    {body : EndpointState headerEnv U ((.proj recordName index (.bvar slot)) :: headerSource) B (.sort v)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (hu : u.WF U) (hv : v.WF U)
    (domainAt : signature.domains[arguments.length]? = some (.proj recordName index (.bvar slot)))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (frame : OriginalRichFrame headerEnv env U registry target context (List.range arguments.length) σ τ available)
    (lookup : Lookup headerSource slot S)
    (head : ProjectionHead (.ref domain))
    (sortField : head.fieldType = .sort sortLevel) (sortRelevant : Relevant sortLevel true)
    (owner : HeaderOwner field major)
    (substitutions : Ctx.SubstEq env U target ownerLeft ownerRight owner.source)
    (value : RichBinderValue sourceEnv env U registry target owner.node ownerLocals ownerLeft ownerRight
      ownerAvailable (input : Profile n))
    (family : FamilyData (Profile n)) (familyName : family.name = recordName)
    (familyRelevant : family.relevant = true)
    (same : owner.assigned.subst ownerLeft = .proj recordName index (σ slot))
    (needed : majorNeed (fieldRecord family familyRelevant index
      (fieldRequest head σ value.support (.sort true))) ∈ available slot)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (child : RichConstructorPlanResult env U registry target header name levels signature (.cons context domain)
      body (σ.cons (owner.expression.subst ownerLeft)) (arguments ++ [owner.expression.subst ownerLeft])
      (available.push needs) (output : Atom n)) :
    Nonempty (RichConstructorPlanResult env U registry target header name levels signature context
      (.pi hu hv (.ref domain) body) σ arguments available
      (n := n + 1) (.fn (owner.seedKey ownerLeft input) output)) := by
  obtain ⟨alignment⟩ := frame.projectedDomainAlignment henv hscoped formed lookup head sortField sortRelevant
    owner value family familyName familyRelevant same needed
  exact RichConstructorPlanResult.binder hu hv domainAt location lineage alignment.aligned.certificate
    alignment.aligned.resources (alignment.lambdaGuard henv sourceBelow formed substitutions)
    needs bounded covered child

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
