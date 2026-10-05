import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeBodyExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeConstantOpening

/-! A native body directly below a canonical recipe root is entered from the
single outer bank. The retained output path selects the literal old row;
caller binder resources supply its new anchor. The resulting body program is
strictly smaller than the stored native table. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem canonicalRecipeRootBodyFromBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    {root : EndpointRef owner.selected.origin.source U rootSource rootExpression rootType}
    (initial : ContextDerivation owner.selected.origin.source U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (domain : EndpointRef owner.selected.origin.source U [] A (.sort u))
    (body : EndpointState owner.selected.origin.source U [A] B (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.pi hu hv (.ref domain) body))
    (closedRoot : (VExpr.forallE A B).Closed)
    (expressionEq : EqUpToLevels U (.forallE A B) (.forallE callerA callerB))
    {ambient : Profile n} {table : List (Key n × Profile n)}
    (domainCode : RichCert owner.selected.origin.source env U registry target (.ref domain)
      [] realization true ambient domainFootprint)
    (guard : PiGuard env U target realization A B prototypeDomain prototypeBody)
    (rows : RichRows owner.selected.origin.source env U registry target (.ref domain) body
      [] realization relevant ambient table rowFootprint)
    (resources : (domainFootprint ++ rowFootprint).Available (fun _ => []))
    (domainAnnotation : WorldCertProvenance strata domainCode)
    (rowsAnnotation : WorldRowsProvenance strata rows)
    (storedControls : OriginalWorldControls strata owner.selected.origin.source)
    (provenance : EndpointProvenance (.nil : ContextDerivation owner.selected.origin.source U [])
      (.pi hu hv (.ref domain) body))
    {m : Nat} {selectedSupport : Profile m} {selectedRows : List (Key m × Profile m)}
    {selectedKey : Key m} {selectedResult : Profile m}
    (path : GeneralOutputPath env U registry target
      (show Atom (n+1) from .pi prototypeDomain prototypeBody ambient table)
      (show Atom (m+1) from .pi nextDomain nextBody selectedSupport selectedRows))
    (selected : (selectedKey, selectedResult) ∈ selectedRows)
    {callerσ callerτ : Subst}
    (anchorEq : selectedKey.anchor = callerσ 0)
    {callerContext : ContextDerivation callerEnv U (callerA :: callerSource)}
    (caller : EndpointState callerEnv U (callerA :: callerSource) callerB callerAssigned)
    (callerControls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U callerEnvironment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld callerControls .fundamental caller baseline])
    (sourceReady : P owner.selected.origin.source)
    (domainPaid : Sponsored frontier domainAnnotation.worlds)
    (rowsPaid : Sponsored frontier rowsAnnotation.worlds)
    (sitePaid : Sponsored frontier
      (WorldQuerySite.empty (registry := registry) (target := target) storedControls provenance realization).worlds)
    (masked : WithinAbove callerControls.cutoff callerControls.fuel
      (headDepth owner.selected.ordinal
        (fun control => max (domainCode.stratifiedDepth (strata.headOrdinal registry) control)
          (rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))))
    (callerFrame : OriginalRichFrame callerEnv env U registry target callerContext
      (Locals.push callerLocals) callerσ callerτ callerAvailable)
    (callerSubstitutions : Ctx.SubstEq env U target callerσ callerτ (callerA :: callerSource))
    (callerResource : Need.mk m selectedKey.input ∈ callerAvailable 0)
    (formed : OnCtx target (env.IsType U))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld callerControls .fundamental caller baseline])) :
    let fuel := fun control => max (domainCode.stratifiedDepth (strata.headOrdinal registry) control)
      (rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
    let controls := canonicalQueryControls owner.selected fuel
    ∃ pending : RankedPendingNativeRow env U registry target table relevant selectedKey selectedResult,
    ∃ row : RichPiRowCertificate env U registry target [] realization (fun _ => []) relevant
      (.ref domain) body pending.oldKey pending.oldResult,
    ∃ frame : OriginalRichFrame owner.selected.origin.source env U registry target
      ((Located.piDomain location).contextDerivation initial) [] realization realization (fun _ => []),
    ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
      HEq captured (WorldEnvironmentProvenance.nil : WorldEnvironmentProvenance strata U []) ∧
      Nonempty (RichPiRowBodyExecution (P := P)
        (context := (Located.piDomain location).contextDerivation initial)
        controls frontier domain body row realization (callerτ 0) hu hv captured) ∧
      HEq row.domain domainCode ∧ sizeOf row.body < sizeOf rows ∧
      TypeRelated env U registry target (callerB.subst callerσ) (callerB.subst callerτ) selectedResult := by
  dsimp only
  let fuel := fun control => max (domainCode.stratifiedDepth (strata.headOrdinal registry) control)
    (rows.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
  let controls := canonicalQueryControls owner.selected fuel
  let sourcePi := EndpointState.pi hu hv (.ref domain) body
  obtain ⟨nilData, sourcePaid, sourceBank⟩ := canonicalNilOpeningBank (registry := registry) (target := target)
    owner sourcePi realization fuel caller callerControls baseline frontier callerPaid sourceReady masked bank
  have contextNil : (Located.piDomain location).contextDerivation initial = .nil := by
    cases (Located.piDomain location).contextDerivation initial
    rfl
  have prepared : ∃ frame : OriginalRichFrame owner.selected.origin.source env U registry target
      ((Located.piDomain location).contextDerivation initial) [] realization realization (fun _ => []),
    ∃ captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered),
      HEq captured (WorldEnvironmentProvenance.nil : WorldEnvironmentProvenance strata U []) ∧
      Nonempty (WorldUnaryFrameData P controls frontier frame captured) ∧
      Sponsored frontier [originalCallWorld controls .fundamental sourcePi captured] ∧
      WorldBoundedUnaryCallBank env U registry strata P
        (frontier ++ [originalCallWorld controls .fundamental sourcePi captured]) := by
    rw [contextNil]
    exact ⟨.nil, .nil, HEq.rfl, ⟨nilData⟩, sourcePaid, sourceBank⟩
  obtain ⟨frame, captured, emptyEnvironment, ⟨data⟩, paid, sourceBank⟩ := prepared
  have bodyContext : (Located.piBody location).contextDerivation initial =
      .cons ((Located.piDomain location).contextDerivation initial) domain := by
    change ContextDerivation.cons (location.contextDerivation initial) (Classical.choose location.originalDomains.1) = _
    exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
      (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
  let domainReady : ControlledStoredQuery controls frontier (.certificate domainCode) := {
    annotation := domainAnnotation
    within := fun _ _ => Nat.le_max_left _ _
    sponsored := domainPaid }
  obtain ⟨pending, row, rowReady, sameDomain, smaller, bodyWorlds, depth⟩ :=
    rowsAnnotation.pathNativeCursor domainCode domainReady
      (fun i need member => resources i need (List.mem_append_left _ member))
      (fun i need member => resources i need (List.mem_append_right _ member))
      (fun _ _ => Nat.le_max_right _ _) rowsPaid path selected
  let certificate := RichCert.pi hu hv domainCode guard rows
  let certificateAnnotation : WorldCertProvenance strata certificate :=
    .pi hu hv domainCode guard rows domainAnnotation rowsAnnotation
  let original : RichCodeRecipe env U registry target callerSource callerLocals callerσ.tail
      (.forallE callerA callerB) relevant (.pi prototypeDomain prototypeBody ambient table) [] :=
    .root callerSource callerLocals callerσ.tail owner sourcePi closedRoot expressionEq realization certificate resources
  let originalAnnotation : WorldCodeRecipeProvenance strata original :=
    .root callerSource callerLocals callerσ.tail owner sourcePi closedRoot expressionEq realization certificate resources
      certificateAnnotation storedControls provenance
  let change := GeneralOutputPath.codeAtInput path certificate.formed
  let parent := RichCodeRecipe.action change original
  let annotation : WorldCodeRecipeProvenance strata parent := .action change originalAnnotation
  have annotationPaid : Sponsored frontier annotation.worlds := by
    change Sponsored frontier
      ((WorldQuerySite.empty (registry := registry) (target := target) storedControls provenance realization).worlds ++
        (domainAnnotation.worlds ++ rowsAnnotation.worlds))
    intro world member
    rcases List.mem_append.mp member with member | member
    · exact sitePaid world member
    · rcases List.mem_append.mp member with member | member
      · exact domainPaid world member
      · exact rowsPaid world member
  have bounded : WithinAbove callerControls.cutoff callerControls.fuel
      (fun control => parent.stratifiedDepth (strata.headOrdinal registry) control) := by
    intro control active
    simpa only [parent, original, certificate, RichCodeRecipe.stratifiedDepth,
      RichCodeRecipe.headDepth, RichCert.headDepth, stratifiedHeadPolicy,
      owner.headOrdinal_eq, RichCert.stratifiedDepth, headDepth] using masked control active
  have callerResources : Footprint.Available
      ((0, Need.mk m selectedKey.input) :: Footprint.sourceLift (.skip .refl) []) callerAvailable := by
    intro index need member
    cases List.mem_singleton.mp member
    exact callerResource
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by
    intro index need member
    cases member
  obtain ⟨execution, code⟩ := annotation.enterPendingBodyFromBank selected anchorEq caller
    callerControls baseline frontier callerPaid sourceReady annotationPaid bounded callerFrame
    callerSubstitutions callerResources bank initial henv hscoped owner.selected.origin.sourceBelow
    controls domain (.piDomain location) body (.piBody location) bodyContext hu hv frame captured data
    sourceBank paid emptyClosed formed .nil pending row rowReady
  exact ⟨pending, row, frame, captured, emptyEnvironment, execution, sameDomain, smaller, code⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
