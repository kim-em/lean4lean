import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeApplicationAdmission
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeApplicationArgument
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRichConstantApplication
import Lean4Lean.Theory.Typing.AnchoredLevels
import Lean4Lean.Theory.Typing.AnchoredOriginalOutputPathCode
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

/-! Productive source-to-caller compilation of the retained native constant
application row. It computes admission using actual source children, compiles
the returned variable query using the caller's exposed Need, and opens the
closed constant at the caller's actual universe instance. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem nativeConstantBodyCodeWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
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
    (guard : LambdaGuard env U registry target σ D (outerKey : Key n) support)
    (fn : RichObs owner.selected.origin.source env U registry target function (Locals.push locals)
      (σ.cons outerKey.anchor) (Profile.fn (key : Key n) output) fnFootprint)
    (arg : RichObs owner.selected.origin.source env U registry target argument (Locals.push locals)
      (σ.cons outerKey.anchor) (rawInput : Profile n) argFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (oldAdmission : Admitted env U registry target key outerKey.anchor outerKey.anchor)
    (pack : BinderPack n packed (fnFootprint ++ argFootprint) outside)
    (coverage : packed.atoms ⊆ outerKey.input.atoms)
    (resources : outside.Available available)
    (domainReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (fnReady : ControlledStoredQuery controls frontier (.observation fn))
    (argReady : ControlledStoredQuery controls frontier (.observation arg))
    (outerAdmission : Admitted env U registry target outerKey (callerσ index) (callerσ index))
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
    (exposedInput : Profile n)
    (inputAdapter : GeneralNormalProfileAdapter env U registry target exposedInput outerKey.input)
    (exposed : Need.mk n exposedInput ∈ callerAvailable index)
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
    (sorted : (Profile.singleton output).HasType (.sort relevant)) :
    ∃ footprint, ∃ code : RichCert callerEnv env U registry target
        (.app callerHU callerHV callerDomain callerBody callerFunction callerArgument callerResult)
        callerLocals callerσ relevant (.singleton output) footprint,
    ∃ ready : ControlledStoredQuery callerControls frontier (.certificate code),
      footprint.Available callerAvailable ∧
      TypeRelated env U registry target (.app (.const name levels) outerKey.anchor)
        (.app (.const name nextLevels) (callerσ index)) (.singleton output) := by
  obtain ⟨answer⟩ := nativeApplicationAdmissionWorld initial henv hscoped owner.selected.origin.sourceBelow
    controls domain domainLocation hu hv bodyLocation bodyContext outerWF frame captured frontier data
    closed formed substitutions certificate domainResources guard fn arg adapter oldAdmission pack coverage resources
    domainReady fnReady argReady outerAdmission piBody bodyRoute resultWF sourceBank sourceSponsored
  obtain ⟨packet, annotation, nameEq, ownerEq, worlds, depth⟩ :=
    canonicalConstSiteOfFunctionAnnotated owner function fn fnReady.annotation
  obtain ⟨callerArg, callerArgReady, _, _, _⟩ := answer.argumentValue.rightQuery.replayNativeBinderArgumentAdapted
    pack coverage closed henv hscoped formed callerOrdered callerFrame callerArgument exposedInput inputAdapter exposed callerControls frontier
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
  exact ⟨footprint, code, ready, available,
    semantic.levels henv (.app constSame anchors.1) (.app equal anchors.2)⟩

/-- Execute the retained body/output path on the SAME reconstructed caller certificate.
The selected output may have a different grade; only the actual finite code action is replayed. -/
theorem nativeConstantBodyOutputWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
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
    (guard : LambdaGuard env U registry target σ D (outerKey : Key n) support)
    (fn : RichObs owner.selected.origin.source env U registry target function (Locals.push locals)
      (σ.cons outerKey.anchor) (Profile.fn (key : Key n) output) fnFootprint)
    (arg : RichObs owner.selected.origin.source env U registry target argument (Locals.push locals)
      (σ.cons outerKey.anchor) (rawInput : Profile n) argFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (oldAdmission : Admitted env U registry target key outerKey.anchor outerKey.anchor)
    (pack : BinderPack n packed (fnFootprint ++ argFootprint) outside)
    (coverage : packed.atoms ⊆ outerKey.input.atoms)
    (resources : outside.Available available)
    (domainReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (fnReady : ControlledStoredQuery controls frontier (.observation fn))
    (argReady : ControlledStoredQuery controls frontier (.observation arg))
    (outerAdmission : Admitted env U registry target outerKey (callerσ index) (callerσ index))
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
    (exposedInput : Profile n)
    (inputAdapter : GeneralNormalProfileAdapter env U registry target exposedInput outerKey.input)
    (exposed : Need.mk n exposedInput ∈ callerAvailable index)
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
      TypeRelated env U registry target (.app (.const name levels) outerKey.anchor)
        (.app (.const name nextLevels) (callerσ index)) (.singleton requestedOutput) := by
  obtain ⟨flag, sorted, ⟨action⟩⟩ := GeneralOutputPath.codeAtOutput henv path requestedSorted
  obtain ⟨footprint, code, ready, resources, related⟩ := nativeConstantBodyCodeWorld owner initial henv hscoped
    controls domain domainLocation hu hv bodyLocation bodyContext outerWF frame captured frontier data
    closed formed substitutions certificate domainResources guard fn arg adapter oldAdmission pack coverage resources
    domainReady fnReady argReady outerAdmission piBody bodyRoute resultWF sourceBank sourceSponsored
    callerFrame callerOrdered callerClosed callerDomain callerBody callerFunction callerArgument callerResult
    callerHU callerHV exposedInput inputAdapter exposed equal fundingCaller callerControls baseline callerPaid
    sourceReady masked callerBank sorted
  obtain ⟨nextFootprint, next, annotation, nextResources, worlds, depth⟩ :=
    code.codeAction_worlds_depth ready.annotation action resources
  refine ⟨nextFootprint, next, ⟨annotation, ?_, ?_⟩, nextResources, action.codeMap henv hscoped related⟩
  · intro control active
    exact Nat.le_trans (depth _) (ready.within control active)
  · intro world member
    exact ready.sponsored world (worlds member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
