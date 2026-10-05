import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationBackwardDemand
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationAssignedPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidSpineInitialization
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCallerHeaderUniverse

/-! Two actual backward application steps. The demanded final parameter is
packed first. Its exact assigned comparison survives the conversion route
of the first application, and the next pack is built at that SAME selected
frame before the whole request is transferred to the genuine header. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source E (.sort u))
  (body : EndpointState sourceEnv U (E :: source) F (.sort v))
  (function : EndpointState sourceEnv U source (.app (.const name levels) a) (.forallE E F))
  (argument : EndpointState sourceEnv U source p E)
  (result : EndpointState sourceEnv U source (F.inst p) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (frame : OriginalRichFrame sourceEnv env U registry target
    (location.contextDerivation initial) locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)

/-- This packet records the real selected frames and requests, including the
intermediate C relation needed for the dependent second domain. -/
structure WorldTwoParameterBackward
    {strata : EquationStratification env} (P : VEnv → Prop)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (profile : Profile n) (relevant : Bool)
    (extraQuery : RichGradedResult sourceEnv env U registry target argument locals σ available (extra : Profile m))
    (info : VConstant) {queryLevels : List VLevel} (queryWF : ∀ level ∈ queryLevels, level.WF U) where
  second : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile
  secondReady : second.Controlled controls frontier
  extraBound : extraQuery.rank ≤ second.request.rank
  extraIncluded : ∀ atom ∈ (raiseProfile second.request.rank extraBound extraQuery.raw).atoms,
    atom ∈ second.request.key.input.atoms
  secondValue : RichSupportedValue sourceEnv env U registry target argument locals σ τ available second.request.key.input
  secondSupport : secondValue.support = second.request.support
  secondValueReady : ControlledStoredQuery controls frontier (.certificate secondValue.certificate)
  secondAdmission : RankedData.RequestAdmission env U (relations env U registry second.request.rank) target
    second.parameterRequest (p.subst σ) (p.subst τ)
  A : VExpr
  B : VExpr
  firstU : VLevel
  firstV : VLevel
  firstHu : firstU.WF U
  firstHv : firstV.WF U
  firstDomain : EndpointRef sourceEnv U source A (.sort firstU)
  firstBody : EndpointState sourceEnv U (A :: source) B (.sort firstV)
  firstFunction : EndpointState sourceEnv U source (.const name levels) (.forallE A B)
  firstArgument : EndpointState sourceEnv U source a A
  firstResult : EndpointState sourceEnv U source (B.inst a) (.sort firstV)
  route : PrefixRoute sourceEnv U source (.app (.const name levels) a) function
    (.app firstHu firstHv (.ref firstDomain) firstBody firstFunction firstArgument firstResult)
  bodyReply : AmbientBoundedParameterReply (frame.captureBase substitutions) (frame.captureBase substitutions).initialCaps
    ((VExpr.forallE E F).subst σ)
    (originalPrefixDisplay initial (.appFunction location) (.identity _) route).formationDisplay σ τ
    (Profile.pi (E.subst σ) (F.subst σ.lift) second.request.support
      [(second.request.key, raiseProfile second.request.rank second.request.bound profile)])
    (environmentCost baselineEnvironment)
  bodyData : WorldParameterReplyData (P := P) controls baseline frontier bodyReply
  selected : WorldAssignedQuery (registry := registry) (target := target)
    (context := (route.locate (.appFunction location)).contextDerivation initial)
    P controls baseline frontier
    (.app firstHu firstHv (.ref firstDomain) firstBody firstFunction firstArgument firstResult) σ τ relevant
    (Profile.pi (E.subst σ) (F.subst σ.lift) second.request.support
      [(second.request.key, raiseProfile second.request.rank second.request.bound profile)])
  selectedLocals : selected.locals = locals
  selectedAvailable : ∀ index need, need ∈ selected.available index → need ∈ available index
  first : GeneratedApplicationPackedRequest firstDomain firstBody firstArgument firstHu firstHv env registry target
    selected.locals σ selected.available relevant
    (Profile.pi (E.subst σ) (F.subst σ.lift) second.request.support
      [(second.request.key, raiseProfile second.request.rank second.request.bound profile)])
  firstReady : first.Controlled controls frontier
  firstValue : RichSupportedValue sourceEnv env U registry target firstArgument selected.locals σ τ selected.available
    first.request.key.input
  firstSupport : firstValue.support = first.request.support
  firstValueReady : ControlledStoredQuery controls frontier (.certificate firstValue.certificate)
  firstAdmission : RankedData.RequestAdmission env U (relations env U registry first.request.rank) target
    first.parameterRequest (a.subst σ) (a.subst τ)
  origin : ConstantHeaderOrigin sourceEnv name info
  headerReply : AmbientBoundedParameterReply (selected.frame.captureBase selected.substitutions)
    (selected.frame.captureBase selected.substitutions).initialCaps
    ((VExpr.forallE A B).subst σ)
    (RetainedHeaderUniverse.display origin queryWF source) σ τ
    (Profile.pi (A.subst σ) (B.subst σ.lift) first.request.support
      [(first.request.key, raiseProfile first.request.rank first.request.bound
        (Profile.pi (E.subst σ) (F.subst σ.lift) second.request.support
          [(second.request.key, raiseProfile second.request.rank second.request.bound profile)]))])
    (environmentCost ([] : List Closure))
  headerData : WorldParameterReplyData (P := P) (controls.atHeader origin) .nil frontier headerReply

/-- Demandful P packing, actual route C, A packing and genuine header
transport are performed with proper calls below the given outer application.
No intermediate reply, row, declared-domain equality or final family answer
is supplied by the caller. -/
theorem twoParameterBackwardWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (frameData : WorldUnaryFrameData P controls frontier frame captured)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (certificate : RichCert sourceEnv env U registry target result locals σ
      relevant (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (certificateReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (extraQuery : RichGradedResult sourceEnv env U registry target argument locals σ available (extra : Profile m))
    (extraReady : ControlledStoredQuery controls frontier (.observation extraQuery.observation))
    (lookup : env.constants name = some info)
    (queryWF : ∀ level ∈ queryLevels, level.WF U)
    (queryEquivalent : List.Forall₂ (· ≈ ·) queryLevels levels)
    (sourceClosed : ∀ source, source ≤ env → P source) :
    Nonempty (WorldTwoParameterBackward initial domain body function argument result hu hv location frame substitutions
      P controls baseline frontier profile relevant extraQuery info queryWF) := by
  obtain ⟨second, ⟨secondReady⟩, ⟨extraBound, extraIncluded⟩,
      ⟨secondValue, secondSupport, ⟨secondValueReady⟩⟩, secondAdmission, outerReply, ⟨outerData⟩⟩ :=
    applicationBackwardDemandWorld initial domain body function argument result hu hv location frame substitutions
      controls captured frontier frameData baseline capacity covered henv hscoped formed closed sponsored unaryBank replayBank
      certificate resources certificateReady extraQuery extraReady
  obtain ⟨⟨A, B, firstU, firstV, firstHu, firstHv, firstDomain, firstBody, firstFunction,
      firstArgument, firstResult, firstLocation, prefixEq, _cost⟩, route, firstLocationEq⟩ :=
    applicationPrefix (Located.appFunction location)
  obtain ⟨firstDomain, rfl⟩ := firstLocation.originalDomains.1
  let natural := EndpointState.app firstHu firstHv (.ref firstDomain) firstBody firstFunction firstArgument firstResult
  obtain ⟨bodyReply, ⟨bodyData⟩⟩ := outerReply.functionPrefixWorld initial domain body function argument result
    hu hv location (.identity _) natural route controls baseline frontier outerData henv
    second.request.certificate.formed sponsored replayBank
  let display := originalPrefixDisplay initial (.appFunction location) (.identity _) route
  obtain ⟨selected, localsEq, availableEq, _sameFrame⟩ := WorldAssignedQuery.ofReply (display := display)
    henv controls baseline frontier bodyReply bodyData second.request.certificate.formed
  have selectedLocals : selected.locals = locals := localsEq.trans bodyReply.reply.answer.reply.locals_eq
  have selectedAvailable : ∀ index need, need ∈ selected.available index → need ∈ available index := by
    rw [availableEq]
    exact bodyReply.reply.answer.capped.availableBound
  have selectedExists : ∃ next : WorldAssignedQuery (registry := registry) (target := target)
      (context := (route.locate (.appFunction location)).contextDerivation initial)
      P controls baseline frontier natural σ τ relevant
      (Profile.pi (E.subst σ) (F.subst σ.lift) second.request.support
        [(second.request.key, raiseProfile second.request.rank second.request.bound profile)]),
      next.locals = locals ∧ ∀ index need, need ∈ next.available index → need ∈ available index := by
    rw [route.locate_contextDerivation (Located.appFunction location) initial]
    exact ⟨selected, selectedLocals, selectedAvailable⟩
  obtain ⟨selected, selectedLocals, selectedAvailable⟩ := selectedExists
  have functionCost : (Closure.close (function.dependencyOrigin controls.ordered) baselineEnvironment).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin
        controls.ordered) baselineEnvironment).cost := by
    apply Nat.lt_of_lt_of_le _ (application_cost_le_captured _ _ _ _ _ _)
    exact binder_other_cost (by simp) _
  have naturalCost := Nat.lt_of_le_of_lt (route.dependency_cost_le controls.ordered baselineEnvironment) functionCost
  have naturalBelow : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental natural baseline)
      (originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline) :=
    original_child (richSchedule_strict naturalCost _ _) _ _ _ _ _
  have naturalPaid := singletonSponsoredBelow sponsored naturalBelow
  have naturalFunding : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental natural baseline])
      (frontier ++ [originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline]) := by
    have split := split_call (fun child member => by cases List.mem_singleton.mp member; exact naturalBelow)
    have prepend : ∀ rest, CallBelow strata.rules.length
        (rest ++ [originalCallWorld controls .fundamental natural baseline])
        (rest ++ [originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline]) := by
      intro rest
      induction rest with
      | nil => exact split
      | cons world rest ih => exact ih.cons world
    exact prepend frontier
  have naturalUnary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental natural baseline]) :=
    fun retained lower => unaryBank retained (lower.trans naturalFunding)
  have naturalReplay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental natural baseline]) :=
    fun retained lower => replayBank retained (lower.trans naturalFunding)
  obtain ⟨first, ⟨firstReady⟩, ⟨firstValue, firstSupport, ⟨firstValueReady⟩⟩,
      firstAdmission, firstReply, ⟨firstData⟩⟩ :=
    applicationBackwardStepWorld initial firstDomain firstBody firstFunction firstArgument firstResult firstHu firstHv
      (route.locate (.appFunction location)) selected.frame selected.substitutions controls selected.captured frontier
      selected.frameData baseline selected.capacity selected.covered henv hscoped formed selected.closed
      naturalPaid naturalUnary naturalReplay selected.certificate selected.resources selected.certificateReady
  have below : sourceEnv ≤ env := (frameData.generation substitutions).erase.ambientGenerated.ambient.1.below
  obtain ⟨origin, headerReply, ⟨headerData⟩⟩ := callerConstantRetainedHeaderWorld
    initial firstDomain firstBody firstFunction firstArgument firstResult firstHu firstHv
      (route.locate (.appFunction location)) (.identity _) controls baseline frontier firstReply firstData
      lookup queryWF queryEquivalent henv hscoped formed below first.request.certificate.formed sourceClosed
      naturalPaid naturalReplay naturalUnary
  exact ⟨⟨second, secondReady, extraBound, extraIncluded, secondValue, secondSupport, secondValueReady, secondAdmission,
    A, B, firstU, firstV, firstHu, firstHv, firstDomain, firstBody, firstFunction, firstArgument, firstResult, route,
    bodyReply, bodyData, selected, selectedLocals, selectedAvailable, first, firstReady,
    firstValue, firstSupport, firstValueReady, firstAdmission, origin, headerReply, headerData⟩⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
