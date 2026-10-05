import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeConstantOpening
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeApplicationRankedArgument

/-! Execute the retained native constant application through the actual
ranked row input program. The source row remains unchanged; admission and
caller resources are computed from the selected row, including pad/down. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem nativeRankedConstantBodyOutputWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    {original : List (Key n × Profile n)} {selectedKey : Key m} {selectedResult : Profile m}
    (pending : RankedPendingNativeRow env U registry target original rowRelevant selectedKey selectedResult)
    {callerσ : Subst} {index : Nat}
    {root : EndpointRef owner.selected.origin.source U rootSource rootExpression rootType}
    (initial : ContextDerivation owner.selected.origin.source U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (controls : OriginalWorldControls strata owner.selected.origin.source)
    (domain : EndpointRef owner.selected.origin.source U source D (.sort outerLevel))
    (domainLocation : Located root (.ref domain))
    {appDomain : EndpointState owner.selected.origin.source U (D :: source) A (.sort u)}
    {appBody : EndpointState owner.selected.origin.source U (A :: D :: source) B (.sort v)}
    {function : EndpointState owner.selected.origin.source U (D :: source) (.const name levels) (.forallE A B)}
    {argument : EndpointState owner.selected.origin.source U (D :: source) (.bvar 0) A}
    {result : EndpointState owner.selected.origin.source U (D :: source) (B.inst (.bvar 0)) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (bodyLocation : Located root (.app hu hv appDomain appBody function argument result))
    (bodyContext : bodyLocation.contextDerivation initial =
      .cons (domainLocation.contextDerivation initial) domain)
    (outerWF : outerLevel.WF U)
    (frame : OriginalRichFrame owner.selected.origin.source env U registry target (domainLocation.contextDerivation initial)
      locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (certificate : RichCert owner.selected.origin.source env U registry target (.ref domain) locals σ true (support : Profile n) domainFootprint)
    (domainResources : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ D (pending.oldKey : Key n) support)
    (fn : RichObs owner.selected.origin.source env U registry target function (Locals.push locals)
      (σ.cons pending.oldKey.anchor) (Profile.fn (key : Key n) output) fnFootprint)
    (arg : RichObs owner.selected.origin.source env U registry target argument (Locals.push locals)
      (σ.cons pending.oldKey.anchor) (rawInput : Profile n) argFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (oldAdmission : Admitted env U registry target key pending.oldKey.anchor pending.oldKey.anchor)
    (pack : BinderPack n packed (fnFootprint ++ argFootprint) outside)
    (coverage : packed.atoms ⊆ pending.oldKey.input.atoms)
    (resources : outside.Available available)
    (domainReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (fnReady : ControlledStoredQuery controls frontier (.observation fn))
    (argReady : ControlledStoredQuery controls frontier (.observation arg))
    (selectedAdmission : Admitted env U registry target selectedKey (callerσ index) (callerσ index))
    (piBody : EndpointState owner.selected.origin.source U (D :: source) (.app (.const name levels) (.bvar 0)) (.sort resultLevel))
    (bodyRoute : PrefixRoute owner.selected.origin.source U (D :: source) (.app (.const name levels) (.bvar 0)) piBody
      (.app hu hv appDomain appBody function argument result))
    (resultWF : resultLevel.WF U)
    (sourceBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi outerWF resultWF (.ref domain) piBody) captured]))
    (sourceSponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi outerWF resultWF (.ref domain) piBody) captured])
    {callerContext : ContextDerivation callerEnv U callerSource}
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      callerLocals callerσ callerτ callerAvailable)
    (callerOrdered : callerEnv.Ordered) (callerClosed : callerAvailable.AtomClosed)
    (callerDomain : EndpointState callerEnv U callerSource callerA (.sort callerU))
    (callerBody : EndpointState callerEnv U (callerA :: callerSource) callerB (.sort callerV))
    (callerFunction : EndpointState callerEnv U callerSource (.const name nextLevels) (.forallE callerA callerB))
    (callerArgument : EndpointState callerEnv U callerSource (.bvar index) callerA)
    (callerResult : EndpointState callerEnv U callerSource (callerB.inst (.bvar index)) (.sort callerV))
    (callerHU : callerU.WF U) (callerHV : callerV.WF U)
    (exposed : Need.mk m selectedKey.input ∈ callerAvailable index)
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (fundingCaller : EndpointState fundingEnv U fundingSource fundingExpression fundingAssigned)
    (callerControls : OriginalWorldControls strata fundingEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (callerPaid : Sponsored frontier [originalCallWorld callerControls .fundamental fundingCaller baseline])
    (sourceReady : P owner.selected.origin.source)
    (masked : WithinAbove callerControls.cutoff callerControls.fuel
      (headDepth owner.selected.ordinal
        (fun control => fn.stratifiedDepth (strata.headOrdinal registry) control)))
    (callerBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld callerControls .fundamental fundingCaller baseline]))
    (path : GeneralOutputPath env U registry target output (requestedOutput : Atom requestedRank))
    (requestedSorted : (Profile.singleton requestedOutput).HasType (.sort requestedRelevant)) :
    ∃ footprint, ∃ code : RichCert callerEnv env U registry target
        (.app callerHU callerHV callerDomain callerBody callerFunction callerArgument callerResult)
        callerLocals callerσ requestedRelevant (.singleton requestedOutput) footprint,
    ∃ ready : ControlledStoredQuery callerControls frontier (.certificate code),
      footprint.Available callerAvailable ∧
      TypeRelated env U registry target (.app (.const name levels) pending.oldKey.anchor)
        (.app (.const name nextLevels) (callerσ index)) (.singleton requestedOutput) := by
  obtain ⟨flag, sorted, ⟨action⟩⟩ := GeneralOutputPath.codeAtOutput henv path requestedSorted
  have outerAdmission := pending.oldAdmission henv hscoped formed guard.anchor selectedAdmission
  obtain ⟨answer⟩ := nativeApplicationAdmissionWorld initial henv hscoped owner.selected.origin.sourceBelow
    controls domain domainLocation hu hv bodyLocation bodyContext outerWF frame captured frontier data
    closed formed substitutions certificate domainResources guard fn arg adapter oldAdmission pack coverage resources
    domainReady fnReady argReady outerAdmission piBody bodyRoute resultWF sourceBank sourceSponsored
  obtain ⟨packet, annotation, nameEq, ownerEq, worlds, depth⟩ :=
    canonicalConstSiteOfFunctionAnnotated owner function fn fnReady.annotation
  obtain ⟨callerArg, callerArgReady, _, _, _⟩ := RichGradedResult.replayRankedNativeBinderArgument pending answer.argumentValue.rightQuery
    pack coverage closed henv hscoped formed callerOrdered callerFrame callerArgument exposed callerControls frontier
  have ownerSource : packet.owner.selected.origin.source = owner.selected.origin.source := by
    cases nameEq
    cases eq_of_heq ownerEq
    rfl
  have ownerOrdinal : packet.owner.selected.ordinal = owner.selected.ordinal := by
    cases nameEq
    cases eq_of_heq ownerEq
    rfl
  have packetSource : P packet.owner.selected.origin.source := ownerSource.symm ▸ sourceReady
  have packetBound : WithinAbove callerControls.cutoff callerControls.fuel packet.chargeDepth := by
    intro control active
    have smaller := depth (stratifiedHeadPolicy (strata.headOrdinal registry) control)
    have bound := masked control active
    change headDepth packet.owner.selected.ordinal
      (fun k => packet.query.stratifiedDepth (strata.headOrdinal registry) k) control ≤ _
    rw [ownerOrdinal]
    by_cases lower : control < owner.selected.ordinal
    · simp only [headDepth, if_pos lower]
      exact Nat.zero_le _
    · simp only [headDepth, if_neg lower] at bound ⊢
      exact Nat.le_trans (Nat.add_le_add_right smaller _) bound
  obtain ⟨footprint, code, ready, available⟩ := packet.compileApplicationLevelsControlled equal annotation
    henv hscoped formed callerClosed fundingCaller callerControls baseline frontier callerPaid packetSource
    (fun world member => fnReady.sponsored world (worlds member)) packetBound callerBank
    (domain := callerDomain) (body := callerBody) (function := callerFunction) (result := callerResult)
    callerHU callerHV callerArg callerArgReady adapter
    (by simpa only [subst] using answer.admitted) sorted
  have semantic := answer.applicationCode henv hscoped formed sorted
  simp only [subst, Subst.cons] at semantic
  have anchors := EqUpToLevels.refl (CtxStrong.strong henv formed).levelWF
    (answer.paired.2.1.strong henv formed)
  have constSame : EqUpToLevels U (.const name levels) (.const name levels) :=
    .const packet.levelsWF packet.levelsWF (Lean4Lean.List.Forall₂.rfl fun _ _ => rfl)
  have related := semantic.levels henv (.app constSame anchors.1) (.app equal anchors.2)
  obtain ⟨nextFootprint, next, annotation, nextResources, worlds, depth⟩ :=
    code.codeAction_worlds_depth ready.annotation action available
  refine ⟨nextFootprint, next, ⟨annotation, ?_, ?_⟩, nextResources, action.codeMap henv hscoped related⟩
  · intro control active
    exact Nat.le_trans (depth _) (ready.within control active)
  · intro world member
    exact ready.sponsored world (worlds member)

theorem canonicalNativeRankedConstantBodyOutputWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    {original : List (Key n × Profile n)} {selectedKey : Key m} {selectedResult : Profile m}
    (pending : RankedPendingNativeRow env U registry target original rowRelevant selectedKey selectedResult)
    {callerσ : Subst} {index : Nat}
    {root : EndpointRef owner.selected.origin.source U rootSource rootExpression rootType}
    (initial : ContextDerivation owner.selected.origin.source U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (frontier : List (World strata.rules.length))
    (domain : EndpointRef owner.selected.origin.source U [] D (.sort outerLevel))
    (domainLocation : Located root (.ref domain))
    {appDomain : EndpointState owner.selected.origin.source U [D] A (.sort u)}
    {appBody : EndpointState owner.selected.origin.source U (A :: [D]) B (.sort v)}
    {function : EndpointState owner.selected.origin.source U [D] (.const name levels) (.forallE A B)}
    {argument : EndpointState owner.selected.origin.source U [D] (.bvar 0) A}
    {result : EndpointState owner.selected.origin.source U [D] (B.inst (.bvar 0)) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (bodyLocation : Located root (.app hu hv appDomain appBody function argument result))
    (bodyContext : bodyLocation.contextDerivation initial =
      .cons (domainLocation.contextDerivation initial) domain)
    (outerWF : outerLevel.WF U)
    (formed : OnCtx target (env.IsType U))
    (certificate : RichCert owner.selected.origin.source env U registry target (.ref domain) [] σ true (support : Profile n) domainFootprint)
    (domainResources : domainFootprint.Available (fun _ => []))
    (guard : LambdaGuard env U registry target σ D (pending.oldKey : Key n) support)
    (fn : RichObs owner.selected.origin.source env U registry target function (Locals.push [])
      (σ.cons pending.oldKey.anchor) (Profile.fn (key : Key n) output) fnFootprint)
    (arg : RichObs owner.selected.origin.source env U registry target argument (Locals.push [])
      (σ.cons pending.oldKey.anchor) (rawInput : Profile n) argFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (oldAdmission : Admitted env U registry target key pending.oldKey.anchor pending.oldKey.anchor)
    (pack : BinderPack n packed (fnFootprint ++ argFootprint) outside)
    (coverage : packed.atoms ⊆ pending.oldKey.input.atoms)
    (resources : outside.Available (fun _ => []))
    (domainAnnotation : WorldCertProvenance strata certificate)
    (fnAnnotation : WorldObsProvenance strata fn)
    (argAnnotation : WorldObsProvenance strata arg)
    (domainSponsored : Sponsored frontier domainAnnotation.worlds)
    (fnSponsored : Sponsored frontier fnAnnotation.worlds)
    (argSponsored : Sponsored frontier argAnnotation.worlds)
    (selectedAdmission : Admitted env U registry target selectedKey (callerσ index) (callerσ index))
    (piBody : EndpointState owner.selected.origin.source U [D] (.app (.const name levels) (.bvar 0)) (.sort resultLevel))
    (bodyRoute : PrefixRoute owner.selected.origin.source U [D] (.app (.const name levels) (.bvar 0)) piBody
      (.app hu hv appDomain appBody function argument result))
    (resultWF : resultLevel.WF U)
    {callerContext : ContextDerivation callerEnv U callerSource}
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      callerLocals callerσ callerτ callerAvailable)
    (callerOrdered : callerEnv.Ordered) (callerClosed : callerAvailable.AtomClosed)
    (callerDomain : EndpointState callerEnv U callerSource callerA (.sort callerU))
    (callerBody : EndpointState callerEnv U (callerA :: callerSource) callerB (.sort callerV))
    (callerFunction : EndpointState callerEnv U callerSource (.const name nextLevels) (.forallE callerA callerB))
    (callerArgument : EndpointState callerEnv U callerSource (.bvar index) callerA)
    (callerResult : EndpointState callerEnv U callerSource (callerB.inst (.bvar index)) (.sort callerV))
    (callerHU : callerU.WF U) (callerHV : callerV.WF U)
    (exposed : Need.mk m selectedKey.input ∈ callerAvailable index)
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (fundingCaller : EndpointState fundingEnv U fundingSource fundingExpression fundingAssigned)
    (callerControls : OriginalWorldControls strata fundingEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (callerPaid : Sponsored frontier [originalCallWorld callerControls .fundamental fundingCaller baseline])
    (sourceReady : P owner.selected.origin.source)
    (masked : WithinAbove callerControls.cutoff callerControls.fuel
      (headDepth owner.selected.ordinal
        (fun control => max (certificate.stratifiedDepth (strata.headOrdinal registry) control)
          (max (fn.stratifiedDepth (strata.headOrdinal registry) control)
            (arg.stratifiedDepth (strata.headOrdinal registry) control)))))
    (callerBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld callerControls .fundamental fundingCaller baseline]))
    (path : GeneralOutputPath env U registry target output (requestedOutput : Atom requestedRank))
    (requestedSorted : (Profile.singleton requestedOutput).HasType (.sort requestedRelevant)) :
    ∃ footprint, ∃ code : RichCert callerEnv env U registry target
        (.app callerHU callerHV callerDomain callerBody callerFunction callerArgument callerResult)
        callerLocals callerσ requestedRelevant (.singleton requestedOutput) footprint,
    ∃ ready : ControlledStoredQuery callerControls frontier (.certificate code),
      footprint.Available callerAvailable ∧
      TypeRelated env U registry target (.app (.const name levels) pending.oldKey.anchor)
        (.app (.const name nextLevels) (callerσ index)) (.singleton requestedOutput) := by
  let fuel := fun control => max (certificate.stratifiedDepth (strata.headOrdinal registry) control)
    (max (fn.stratifiedDepth (strata.headOrdinal registry) control)
      (arg.stratifiedDepth (strata.headOrdinal registry) control))
  let controls := canonicalQueryControls owner.selected fuel
  let sourcePi := EndpointState.pi outerWF resultWF (.ref domain) piBody
  obtain ⟨nilData, sourceSponsored, sourceBank⟩ := canonicalNilOpeningBank (registry := registry) (target := target) owner sourcePi σ fuel
    fundingCaller callerControls baseline frontier callerPaid sourceReady masked callerBank
  have contextNil : domainLocation.contextDerivation initial = .nil := by
    cases domainLocation.contextDerivation initial
    rfl
  have prepared : ∃ frame : OriginalRichFrame owner.selected.origin.source env U registry target
      (domainLocation.contextDerivation initial) [] σ σ (fun _ => []),
    ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
    Nonempty (WorldUnaryFrameData P controls frontier frame captured) ∧
    Sponsored frontier [originalCallWorld controls .fundamental sourcePi captured] ∧
    WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental sourcePi captured]) := by
    rw [contextNil]
    exact ⟨.nil, .nil, ⟨nilData⟩, sourceSponsored, sourceBank⟩
  obtain ⟨frame, captured, ⟨data⟩, paid, bank⟩ := prepared
  have closed : Valuation.AtomClosed (fun _ => []) := by
    intro index need member
    cases member
  let domainReady : ControlledStoredQuery controls frontier (.certificate certificate) := {
    annotation := domainAnnotation
    within := fun control active => Nat.le_max_left _ _
    sponsored := domainSponsored }
  let fnReady : ControlledStoredQuery controls frontier (.observation fn) := {
    annotation := fnAnnotation
    within := fun control active => Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    sponsored := fnSponsored }
  let argReady : ControlledStoredQuery controls frontier (.observation arg) := {
    annotation := argAnnotation
    within := fun control active => Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
    sponsored := argSponsored }
  have fnMasked : WithinAbove callerControls.cutoff callerControls.fuel
      (headDepth owner.selected.ordinal
        (fun control => fn.stratifiedDepth (strata.headOrdinal registry) control)) := by
    intro control active
    have bound := masked control active
    by_cases lower : control < owner.selected.ordinal
    · simp only [headDepth, if_pos lower]
      exact Nat.zero_le _
    · simp only [headDepth, if_neg lower] at bound ⊢
      exact Nat.le_trans (Nat.add_le_add_right
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) _) bound
  exact nativeRankedConstantBodyOutputWorld owner pending initial henv hscoped controls domain domainLocation
    hu hv bodyLocation bodyContext outerWF frame captured frontier data closed formed .nil
    certificate domainResources guard fn arg adapter oldAdmission pack coverage resources
    domainReady fnReady argReady selectedAdmission piBody bodyRoute resultWF bank paid
    callerFrame callerOrdered callerClosed callerDomain callerBody callerFunction callerArgument callerResult
    callerHU callerHV exposed equal fundingCaller callerControls baseline callerPaid
    sourceReady fnMasked callerBank path requestedSorted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
