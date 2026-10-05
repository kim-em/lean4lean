import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterBackward
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterHeaderComposition
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCallerFamilyApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidSpineForward
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyArgumentMerge

/-! Reconstruct the dependent two-parameter family from the actual backward
packet. Both declared requests are extracted from the same genuine header;
its inner domain is evaluated at the first packed anchor. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private bareFamilyWorld from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyApplication
open private moveQueryFrame restoreQueryRoute from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidSpineForward
open private RichGradedResult.raiseRequest_controlled from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyArgumentMerge
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source E (.sort u)}
  {body : EndpointState sourceEnv U (E :: source) F (.sort v)}
  {function : EndpointState sourceEnv U source (.app (.const name levels) a) (.forallE E F)}
  {argument : EndpointState sourceEnv U source p E}
  {result : EndpointState sourceEnv U source (F.inst p) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target
    (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {strata : EquationStratification env} {P : VEnv → Prop}
  {controls : OriginalWorldControls strata sourceEnv}
  {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
  {frontier : List (World strata.rules.length)}
  {extraQuery : RichGradedResult sourceEnv env U registry target argument locals σ available (extra : Profile m)}
  {queryLevels : List VLevel}
  {queryWF : ∀ level ∈ queryLevels, level.WF U}
  (packet : WorldTwoParameterBackward initial domain body function argument result hu hv location frame substitutions
    P controls baseline frontier (profile : Profile n) relevant extraQuery info queryWF)

def WorldTwoParameterBackward.firstDeclared (C : VExpr) : DataRequest (Profile packet.first.request.rank) :=
  ⟨⟨C.subst σ, packet.first.request.key.anchor, packet.first.request.key.input⟩, packet.first.request.support⟩

theorem WorldTwoParameterBackward.secondBound : packet.second.request.rank ≤ packet.first.request.rank :=
  Nat.le_trans (Nat.le_succ _) packet.first.request.bound

def WorldTwoParameterBackward.secondDeclared (D : VExpr) : DataRequest (Profile packet.first.request.rank) :=
  ⟨⟨D.subst (σ.cons packet.first.request.key.anchor), p.subst σ,
    raiseProfile packet.first.request.rank packet.secondBound packet.second.request.key.input⟩,
    raiseProfile packet.first.request.rank packet.secondBound packet.second.request.support⟩

/-- All domain matching is computed from the retained intermediate C reply,
its exact anchor and the actual whole-header relation. -/
theorem WorldTwoParameterBackward.headerPlanWorld
    (signature : ConstantTelescope (info.type.instL queryLevels))
    (domains : signature.domains = [C,D])
    (resultSort : signature.result = .sort level) (relevance : Relevant level familyRelevant)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline])) :
    RankedData.RequestAdmission env U (relations env U registry packet.first.request.rank) target
      (packet.firstDeclared C) (a.subst σ) (a.subst τ) ∧
    RankedData.RequestAdmission env U (relations env U registry packet.first.request.rank) target
      (packet.secondDeclared D) (p.subst σ) (p.subst τ) ∧
    ∃ plan : RichFamilyPlanResult env U registry target (packet.origin.familyHeader queryWF).reference
        name queryLevels signature .nil (.ref (packet.origin.familyHeader queryWF).reference) σ [] (fun _ => [])
        (n := packet.first.request.rank+3)
        (.fn (Key.pad (Key.pad (packet.firstDeclared C).toKeyData))
          (.fn (Key.pad (packet.secondDeclared D).toKeyData)
            (.family ⟨name, queryLevels, familyRelevant, [packet.firstDeclared C,packet.secondDeclared D]⟩))),
      Nonempty (plan.WorldControlled (controls.atHeader packet.origin) frontier) := by
  have headerBelow := originalClosedHeader_below controls packet.origin
    (.ref (packet.origin.familyHeader queryWF).reference)
    (.app hu hv (.ref domain) body function argument result) baseline .expressionReindex .fundamental
  have headerPaid := singletonSponsoredBelow paid headerBelow
  have headerFunding : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld (controls.atHeader packet.origin) .expressionReindex
        (.ref (packet.origin.familyHeader queryWF).reference) .nil])
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]) := by
    have split := split_call (fun child member => by cases List.mem_singleton.mp member; exact headerBelow)
    have prepend : ∀ rest, CallBelow strata.rules.length
        (rest ++ [originalCallWorld (controls.atHeader packet.origin) .expressionReindex
          (.ref (packet.origin.familyHeader queryWF).reference) .nil])
        (rest ++ [originalCallWorld controls .fundamental
          (.app hu hv (.ref domain) body function argument result) baseline]) := by
      intro rest
      induction rest with
      | nil => exact split
      | cons world rest ih => exact ih.cons world
    exact prepend frontier
  have headerBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld (controls.atHeader packet.origin) .expressionReindex
        (.ref (packet.origin.familyHeader queryWF).reference) .nil]) :=
    fun retained lower => unary retained (lower.trans headerFunding)
  have below : sourceEnv ≤ env :=
    (packet.selected.frameData.generation packet.selected.substitutions).erase.ambientGenerated.ambient.1.below
  have firstAdmission : RankedData.RequestAdmission env U (relations env U registry packet.first.request.rank) target
      (⟨⟨packet.A.subst σ, packet.first.request.key.anchor, packet.first.request.key.input⟩,
        packet.first.request.support⟩ : DataRequest (Profile packet.first.request.rank))
      packet.first.request.key.anchor (a.subst τ) := by
    simpa only [packet.first.request.anchor_eq, GeneratedApplicationPackedRequest.parameterRequest] using packet.firstAdmission
  have firstAdmitted : Admitted env U registry target packet.first.request.key
      packet.first.request.key.anchor packet.first.request.key.anchor := by
    simpa only [packet.first.request.anchor_eq] using packet.first.request.admitted
  have bodyDisplayed :
      ((packet.B.inst a).subst Subst.id).subst σ =
        (packet.B.subst σ.lift).inst packet.first.request.key.anchor := by
    change ((packet.B.inst a).subst Subst.id).subst σ = _
    rw [subst_id, packet.first.request.anchor_eq, subst_inst]
  obtain ⟨firstDeclared, secondDeclared, plan, ready⟩ := packet.headerReply.twoParameterHeaderPlanFromReplyWorld
    packet.origin queryWF (controls.atHeader packet.origin) frontier signature domains resultSort relevance
    packet.first.request.bound packet.headerData henv hscoped below formed packet.first.request.certificate.formed
    firstAdmission firstAdmitted packet.bodyReply packet.bodyData bodyDisplayed packet.secondAdmission headerPaid headerBank
  refine ⟨?_, secondDeclared, plan, ready⟩
  simpa only [WorldTwoParameterBackward.firstDeclared, packet.first.request.anchor_eq] using firstDeclared


/-- The returned caller certificate retains the exact demanded parameter
profiles and the plan built at its genuinely selected declaration header. -/
structure WorldTwoParameterFamilyResult
    (signature : ConstantTelescope (info.type.instL queryLevels))
    (C D : VExpr) (familyRelevant : Bool) where
  firstAdmission : RankedData.RequestAdmission env U (relations env U registry packet.first.request.rank) target
    (packet.firstDeclared C) (a.subst σ) (a.subst τ)
  secondAdmission : RankedData.RequestAdmission env U (relations env U registry packet.first.request.rank) target
    (packet.secondDeclared D) (p.subst σ) (p.subst τ)
  plan : RichFamilyPlanResult env U registry target (packet.origin.familyHeader queryWF).reference
    name queryLevels signature .nil (.ref (packet.origin.familyHeader queryWF).reference) σ [] (fun _ => [])
    (n := packet.first.request.rank+3)
    (.fn (Key.pad (Key.pad (packet.firstDeclared C).toKeyData))
      (.fn (Key.pad (packet.secondDeclared D).toKeyData)
        (.family ⟨name, queryLevels, familyRelevant, [packet.firstDeclared C,packet.secondDeclared D]⟩)))
  planReady : plan.WorldControlled (controls.atHeader packet.origin) frontier
  query : RichGradedResult sourceEnv env U registry target
    (.app hu hv (.ref domain) body function argument result) locals σ available
    (.singleton (n := packet.first.request.rank+1)
      (.family ⟨name, queryLevels, familyRelevant, [packet.firstDeclared C,packet.secondDeclared D]⟩))
  queryReady : ControlledStoredQuery controls frontier (.observation query.observation)
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target
    (.app hu hv (.ref domain) body function argument result) locals σ familyRelevant
    (.singleton (n := packet.first.request.rank+1)
      (.family ⟨name, queryLevels, familyRelevant, [packet.firstDeclared C,packet.secondDeclared D]⟩)) footprint
  resources : footprint.Available available
  certificateReady : ControlledStoredQuery controls frontier (.certificate certificate)

/-- The actual P observer survives both packing grades in the terminal
request. In particular a nonempty function demand cannot disappear merely
because the initial result certificate or another parameter was empty. -/
theorem WorldTwoParameterBackward.extraInSecond (D : VExpr) :
    ∃ bound : extraQuery.rank ≤ packet.first.request.rank,
      ∀ atom ∈ (raiseProfile packet.first.request.rank bound extraQuery.raw).atoms,
        atom ∈ (packet.secondDeclared D).input.atoms := by
  refine ⟨Nat.le_trans packet.extraBound packet.secondBound, ?_⟩
  have included := raiseProfile_subset packet.secondBound packet.extraIncluded
  simpa only [WorldTwoParameterBackward.secondDeclared, raiseProfile_trans] using included

/-- Rebuild the genuine caller constant and both actual application nodes.
The original first-application prefix and the SAME packed argument queries
are preserved; no physical-origin or family-code answer is assumed. -/
theorem WorldTwoParameterBackward.callerFamilyWorld
    (signature : ConstantTelescope (info.type.instL queryLevels))
    (domains : signature.domains = [C,D])
    (resultSort : signature.result = .sort level) (relevance : Relevant level familyRelevant)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (queryLength : queryLevels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (queryEquivalent : List.Forall₂ (· ≈ ·) queryLevels levels)
    (typeClosed : info.type.Closed)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline])) :
    Nonempty (WorldTwoParameterFamilyResult packet signature C D familyRelevant) := by
  obtain ⟨firstAdmission, secondAdmission, plan, ⟨planReady⟩⟩ := packet.headerPlanWorld
    signature domains resultSort relevance henv hscoped formed paid unary
  let firstRequest := packet.firstDeclared C
  let secondRequest := packet.secondDeclared D
  let family : Atom (packet.first.request.rank+1) :=
    .family ⟨name, queryLevels, familyRelevant, [firstRequest, secondRequest]⟩
  let atCaller : plan.WorldControlled controls frontier := {
    plan := planReady.plan, planWithin := planReady.planWithin, planSponsored := planReady.planSponsored
    code := ControlledStoredQuery.recontrol controls planReady.code rfl rfl }
  obtain ⟨constantObservation, ⟨constantReady⟩⟩ := bareFamilyWorld controls frontier
    packet.origin lookup notDefinition notNative notQuotient queryWF queryLength levelsWF queryEquivalent
    signature typeClosed plan atCaller
    (.app hu hv (.ref domain) body function argument result) baseline .fundamental paid
    (node := packet.firstFunction) (locals := locals) (σ := σ)
  have firstAnchor : firstRequest.anchor = a.subst σ := packet.first.request.anchor_eq
  have secondAnchor : secondRequest.anchor = p.subst σ := rfl
  have firstAdmitted := Admitted.left_diagonal firstAdmission.toAdmission
  have firstPadded := Admitted.pad henv (Admitted.pad henv firstAdmitted)
  have firstAnchorAdmitted : Admitted env U registry target (Key.pad (Key.pad firstRequest.toKeyData))
      (Key.pad (Key.pad firstRequest.toKeyData)).anchor (Key.pad (Key.pad firstRequest.toKeyData)).anchor := by
    change Admitted env U registry target (Key.pad (Key.pad firstRequest.toKeyData))
      (a.subst σ) (a.subst σ) at firstPadded
    simpa only [Key.pad, firstAnchor] using firstPadded
  have secondAdmitted := Admitted.left_diagonal secondAdmission.toAdmission
  have secondPadded := Admitted.pad henv secondAdmitted
  have secondAnchorAdmitted : Admitted env U registry target (Key.pad secondRequest.toKeyData)
      (Key.pad secondRequest.toKeyData).anchor (Key.pad secondRequest.toKeyData).anchor := by
    change Admitted env U registry target (Key.pad secondRequest.toKeyData)
      (p.subst σ) (p.subst σ) at secondPadded
    simpa only [Key.pad, secondAnchor] using secondPadded
  let constantQuery : RichGradedResult sourceEnv env U registry target packet.firstFunction locals σ available
      (Profile.fn (Key.pad (Key.pad firstRequest.toKeyData)) (.fn (Key.pad secondRequest.toKeyData) family)) := {
    rank := packet.first.request.rank+3
    bound := Nat.le_refl _
    raw := Profile.fn (Key.pad (Key.pad firstRequest.toKeyData)) (.fn (Key.pad secondRequest.toKeyData) family)
    footprint := []
    observation := constantObservation
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := fun _ _ member => nomatch member
    live := Profile.Live.singleton_iff.mpr ⟨firstAnchorAdmitted, secondAnchorAdmitted, trivial⟩ }
  obtain ⟨firstArgument, ⟨firstArgumentReady⟩⟩ := moveQueryFrame packet.first.argumentQuery packet.firstReady.argument
    packet.selectedLocals packet.selectedAvailable
  let firstTwice := (firstArgument.pad henv hscoped formed).pad henv hscoped formed
  obtain ⟨firstOnceReady⟩ := firstArgumentReady.raise (Nat.le_max_left firstArgument.rank (packet.first.request.rank+1))
  obtain ⟨firstTwiceReady⟩ := firstOnceReady.raise
    (Nat.le_max_left (max firstArgument.rank (packet.first.request.rank+1)) (packet.first.request.rank+2))
  obtain ⟨firstApplied, firstAppliedReady, _, _, _⟩ := RichGradedResult.appControlled
    henv hscoped formed closed (.ref packet.firstDomain) packet.firstBody packet.firstResult
    packet.firstHu packet.firstHv constantQuery firstTwice (.refl _) firstPadded controls
    constantReady firstTwiceReady
  obtain ⟨functionReady⟩ := restoreQueryRoute packet.route firstApplied firstAppliedReady
  let functionQuery := firstApplied.restoreRoute packet.route
  let secondRaised := packet.second.argumentQuery.raiseRequest henv hscoped formed packet.secondBound
  obtain ⟨secondRaisedReady⟩ := packet.secondReady.argument.raise
    (Nat.le_max_left packet.second.argumentQuery.rank packet.first.request.rank)
  let secondPaddedQuery := secondRaised.pad henv hscoped formed
  obtain ⟨secondPaddedReady⟩ := secondRaisedReady.raise
    (Nat.le_max_left secondRaised.rank (packet.first.request.rank+1))
  obtain ⟨query, queryReady, _, _, _⟩ := RichGradedResult.appControlled
    henv hscoped formed closed (.ref domain) body result hu hv functionQuery secondPaddedQuery
    (.refl _) secondPadded controls functionReady secondPaddedReady
  have sorted : (Profile.singleton family).HasType (.sort familyRelevant) := by
    refine ⟨?_, Profile.WF.sort (n := packet.first.request.rank+1) familyRelevant, ?_⟩
    · intro atom member
      cases List.mem_singleton.mp member
      change ∀ request ∈ [firstRequest, secondRequest], request.input.WF ∧ request.support.WF
      intro request member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨firstAdmission.2.2.1.wf_value, firstAdmission.2.2.2.1.wf_value⟩
      · cases List.mem_singleton.mp member
        exact ⟨secondAdmission.2.2.1.wf_value, secondAdmission.2.2.2.1.wf_value⟩
    · intro atom member
      cases List.mem_singleton.mp member
      exact ⟨_, List.mem_singleton_self _, rfl⟩
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ := query.code_controlled henv controls queryReady sorted
  exact ⟨⟨firstAdmission, secondAdmission, plan, planReady, query, queryReady,
    footprint, certificate, resources, certificateReady⟩⟩

end
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


/-- Complete demandful two-parameter reconstruction from the incoming result
certificate and actual additional P query, using only the proper outer banks. -/
theorem twoParameterFamilyWorld
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
    (sourceClosed : ∀ source, source ≤ env → P source)
    (signature : ConstantTelescope (info.type.instL queryLevels))
    (domains : signature.domains = [C,D])
    (resultSort : signature.result = .sort level) (relevance : Relevant level familyRelevant)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (queryLength : queryLevels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (typeClosed : info.type.Closed) :
    ∃ packet : WorldTwoParameterBackward initial domain body function argument result hu hv location frame substitutions
      P controls baseline frontier profile relevant extraQuery info queryWF,
      Nonempty (WorldTwoParameterFamilyResult packet signature C D familyRelevant) := by
  obtain ⟨packet⟩ := twoParameterBackwardWorld initial domain body function argument result hu hv location frame substitutions
    controls captured frontier frameData baseline capacity covered henv hscoped formed closed sponsored unaryBank replayBank
    certificate resources certificateReady extraQuery extraReady lookup queryWF queryEquivalent sourceClosed
  exact ⟨packet, packet.callerFamilyWorld signature domains resultSort relevance lookup notDefinition notNative notQuotient
    queryLength levelsWF queryEquivalent typeClosed henv hscoped formed closed sponsored unaryBank⟩

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
