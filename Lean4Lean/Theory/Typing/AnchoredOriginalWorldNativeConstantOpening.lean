import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeConstantBody
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCanonicalQueryOpening

/-! The canonical entry derives the native source calls from the enclosing
call bank. The original input queries determine the child fuel; the caller's
masked charge pays the actual original proof and its empty source frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem canonicalNilOpeningBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (node : EndpointState owner.selected.origin.source U [] expression assigned)
    (realization : Subst)
    (fuel : Nat → Nat)
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sourceReady : P owner.selected.origin.source)
    (masked : WithinAbove controls.cutoff controls.fuel (headDepth owner.selected.ordinal fuel))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline])) :
    let childControls := canonicalQueryControls owner.selected fuel
    let frame : OriginalRichFrame owner.selected.origin.source env U registry target .nil
      [] realization realization (fun _ => []) := .nil
    ∃ _ : WorldUnaryFrameData P childControls frontier frame .nil,
    Sponsored frontier [originalCallWorld childControls .fundamental node .nil] ∧
    WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld childControls .fundamental node .nil]) := by
  dsimp only
  let childControls := canonicalQueryControls owner.selected fuel
  let frame : OriginalRichFrame owner.selected.origin.source env U registry target .nil
    [] realization realization (fun _ => []) := .nil
  let childWorld := originalCallWorld childControls .fundamental node .nil
  have lower : WorldBelow strata.rules.length childWorld
      (originalCallWorld controls .fundamental caller baseline) := by
    apply Below.root
      (openingDecrease owner.selected.ordinal_pos owner.selected.ordinal_le controls.cutoffBound
        masked controls.ordered.constantCount
        (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)
        owner.selected.origin.ordered.constantCount
        (richSchedule .fundamental (Closure.close (node.dependencyOrigin owner.selected.origin.ordered) []).cost))
    intro value member
    cases member
  have sponsored : Sponsored frontier [childWorld] := by
    intro value member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, paid⟩ := callerPaid _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans lower paid⟩
  have funded : CallBelow strata.rules.length (frontier ++ [childWorld])
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]) := by
    have step : CallBelow strata.rules.length [childWorld]
        [originalCallWorld controls .fundamental caller baseline] :=
      split_call (by intro value member; cases List.mem_singleton.mp member; exact lower)
    have appendLower : ∀ sponsors : List (World strata.rules.length),
        CallBelow strata.rules.length (sponsors ++ [childWorld])
          (sponsors ++ [originalCallWorld controls .fundamental caller baseline]) := by
      intro sponsors
      induction sponsors with
      | nil => exact step
      | cons world rest ih => exact ih.cons world
    exact appendLower frontier
  have data : WorldUnaryFrameData P childControls frontier frame .nil := by
    refine ⟨?_, ?_, ?_, .nil childControls, ?_⟩
    · simpa only [frame, OriginalRichFrame.Ambient, OriginalRichFrame.nil,
        RawOriginalRichFrame.Ambient, and_true] using owner.selected.origin.sourceBelow
    · simpa only [frame, OriginalRichFrame.nil, RawOriginalRichFrame.AllSources, and_true] using sourceReady
    · intro query member
      simp only [frame, OriginalRichFrame.nil, RawOriginalRichFrame.storedQueries, List.not_mem_nil] at member
    · exact ⟨(fun _ _ member => nomatch member), rfl, rfl⟩
  exact ⟨data, sponsored, fun retained below => bank retained (below.trans funded)⟩

/-- The actual canonical native body entry uses only the enclosing bank.
The three original query depths determine its source controls and the strict opening. -/
theorem canonicalNativeConstantBodyOutputWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
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
    (guard : LambdaGuard env U registry target σ D (outerKey : Key n) support)
    (fn : RichObs owner.selected.origin.source env U registry target function (Locals.push [])
      (σ.cons outerKey.anchor) (Profile.fn (key : Key n) output) fnFootprint)
    (arg : RichObs owner.selected.origin.source env U registry target argument (Locals.push [])
      (σ.cons outerKey.anchor) (rawInput : Profile n) argFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (oldAdmission : Admitted env U registry target key outerKey.anchor outerKey.anchor)
    (pack : BinderPack n packed (fnFootprint ++ argFootprint) outside)
    (coverage : packed.atoms ⊆ outerKey.input.atoms)
    (resources : outside.Available (fun _ => []))
    (domainAnnotation : WorldCertProvenance strata certificate)
    (fnAnnotation : WorldObsProvenance strata fn)
    (argAnnotation : WorldObsProvenance strata arg)
    (domainSponsored : Sponsored frontier domainAnnotation.worlds)
    (fnSponsored : Sponsored frontier fnAnnotation.worlds)
    (argSponsored : Sponsored frontier argAnnotation.worlds)
    (outerAdmission : Admitted env U registry target outerKey (callerσ index) (callerσ index))
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
      TypeRelated env U registry target (.app (.const name levels) outerKey.anchor)
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
  exact nativeConstantBodyOutputWorld owner initial henv hscoped controls domain domainLocation
    hu hv bodyLocation bodyContext outerWF frame captured frontier data closed formed .nil
    certificate domainResources guard fn arg adapter oldAdmission pack coverage resources
    domainReady fnReady argReady outerAdmission piBody bodyRoute resultWF bank paid
    callerFrame callerOrdered callerClosed callerDomain callerBody callerFunction callerArgument callerResult
    callerHU callerHV exposedInput inputAdapter exposed equal fundingCaller callerControls baseline callerPaid
    sourceReady fnMasked callerBank path requestedSorted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
