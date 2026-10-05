import Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQueryData
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationTypeRouteSide
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze
import Lean4Lean.Theory.Typing.AnchoredOriginalRichOutputReplay

/-! Shared application packing data and finite query operations. Recursive
replay implementations depend on these declarations, not conversely. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)

noncomputable def applicationCaptureCapacity : Nat :=
  environmentCost (Closure.bundle (.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered))
    (.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) :: frame.dependencyEnvironment ordered)

noncomputable def applicationReplayLimit : Nat :=
  richSchedule .fundamental
    (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost

structure ApplicationBackwardQueries (relevant : Bool) (profile : Profile n) where
  reply : BoundedGeneratedQueryReply (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
    (applicationBodyDisplay initial domain body function argument result hu hv location (.identity _)) σ τ profile
    (applicationCaptureCapacity initial domain body function argument result hu hv location frame ordered)
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target body reply.answer.reply.locals
    ((Subst.id.cons (a.subst .id)).comp σ) relevant profile footprint
  resources : footprint.Available reply.answer.reply.available
  queries : CapturedArgumentQueries (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
    source σ τ a (applicationCaptureCapacity initial domain body function argument result hu hv location frame ordered)
    footprint.localNeeds

end

structure RichTypedBinderPack
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (left right : VExpr) (required : Footprint) (minimum : Nat) where
  rank : Nat
  bound : minimum ≤ rank
  input : Profile rank
  support : Profile rank
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true support footprint
  resources : footprint.Available available
  typed : input.HasType support
  code : TypeRelated env U registry target (A.subst σ) (A.subst σ) support
  related : Related env U registry target left right (A.subst σ) input support
  outside : Footprint
  pack : BinderPack rank input required outside
  external : outside.Available available

structure GeneratedApplicationPiRequest
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (argument : VExpr) (relevant : Bool) (profile : Profile n) where
  rank : Nat
  bound : n ≤ rank
  key : Key rank
  support : Profile rank
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target (.pi hu hv (.ref domain) body) locals σ
    relevant (Profile.pi (A.subst σ) (B.subst σ.lift) support [(key, raiseProfile rank bound profile)]) footprint
  resources : footprint.Available available
  admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ)
  anchor_eq : key.anchor = argument.subst σ

noncomputable def RichGradedResult.raiseRequest
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : RichGradedResult sourceEnv env U registry target node locals σ available (input : Profile n))
    (bound : n ≤ k) :
    RichGradedResult sourceEnv env U registry target node locals σ available (raiseProfile k bound input) := by
  let N := max answer.rank k
  let raised := answer.raiseTo henv hscoped formed N (Nat.le_max_left _ _)
  refine ⟨N, Nat.le_max_right _ _, raised.raw, raised.footprint, raised.observation, ?_, raised.resources, raised.live⟩
  simpa only [raised, RichGradedResult.raiseTo, raiseProfile_trans] using raised.adapter

private theorem argumentSupplyLookup
    {available : Valuation}
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available needs)
    (member : need ∈ needs) :
    Nonempty (RichGradedResult sourceEnv env U registry target node locals σ available need.profile) := by
  induction supply with
  | nil => cases member
  | cons value tail ih =>
    rcases List.mem_cons.mp member with same | member
    · cases same; exact ⟨value⟩
    · exact ih member

/-- The exact syntactic binder pack computes its whole argument query from
its finite actual replacements. External variables contribute no input atom. -/
theorem binderPackArgumentQuery
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (pack : BinderPack n input required outside)
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available required.localNeeds) :
    Nonempty (RichGradedResult sourceEnv env U registry target node locals σ available input) := by
  have get := fun need (member : (0, need) ∈ required) => argumentSupplyLookup supply (Footprint.mem_localNeeds.mpr member)
  clear supply
  induction pack with
  | nil => exact ⟨.empty⟩
  | external index need rest ih =>
    exact ih (fun wanted member => get wanted (List.mem_cons_of_mem _ member))
  | «local» need bound rest ih =>
    obtain ⟨tail⟩ := ih (fun wanted member => get wanted (List.mem_cons_of_mem _ member))
    obtain ⟨headQuery⟩ := get need List.mem_cons_self
    let head := headQuery.raiseRequest henv hscoped formed bound
    have result := head.union henv hscoped formed tail
    simpa only [Need.atGrade, dif_pos bound] using Nonempty.intro result


structure GeneratedApplicationPackedRequest
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (argument : EndpointState sourceEnv U source a A)
    (hu : u.WF U) (hv : v.WF U)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (relevant : Bool) (profile : Profile n) where
  request : GeneratedApplicationPiRequest domain body hu hv env registry target locals σ available a relevant profile
  argumentQuery : RichGradedResult sourceEnv env U registry target argument locals σ available request.key.input
  domainFootprint : Footprint
  domainCertificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true request.support domainFootprint
  domainResources : domainFootprint.Available available
  inputTyped : request.key.input.HasType request.support
  domainRelated : TypeRelated env U registry target (A.subst σ) (A.subst σ) request.support


section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {ordered : sourceEnv.Ordered}

noncomputable def applicationDomainDisplay : OriginalNestedDisplay U source A (.sort u) :=
  OriginalNestedDisplay.identity (frame.captureBase substitutions) (.ref domain)
    (.ofLocation (.appDomain location) initial)

noncomputable def applicationArgumentFormationDisplay :
    OriginalNestedDisplay U source A (.sort argument.typeFormation.level) :=
  OriginalNestedDisplay.identity (frame.captureBase substitutions) argument.typeFormation.node
    (.ofLocation (.assignedFormation (.appArgument location)) initial)

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
