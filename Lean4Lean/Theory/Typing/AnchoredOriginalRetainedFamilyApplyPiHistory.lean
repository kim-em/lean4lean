import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyInitialRoute
import Lean4Lean.Theory.Typing.AnchoredOriginalIndependentFamilyHeader
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationRouteSide
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiHistoryGeneration

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private transportRouteFrame from Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationRouteSide
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem transport_sourceGenerated
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight graph frame.realization.frame.raw) :
    SourceCaptureGenerated P base caps commonLeft commonRight (equal ▸ graph)
      (transportRouteFrame equal frame).realization.frame.raw := by
  cases equal
  exact generated

private theorem closed_sourceGenerated
    (context : ContextDerivation sourceEnv U []) (common : List VExpr)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (left right : Subst) (below : sourceEnv ≤ env) (source : P sourceEnv) :
    SourceCaptureGenerated P base caps left right (closedCaptureGraph context common)
      (closedTypeRouteFrame context common env registry target left right).realization.frame.raw := by
  cases context
  exact .empty common left right below source

namespace RetainedHeaderUniverse

/-- Literal Pi extraction follows the actual retained header original,
including its conversion prefix and independently retained domain proof. -/
noncomputable def nativeSide
    (origin : ConstantHeaderOrigin sourceEnv name info)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    (shape : info.type.instL levels = .forallE A B) (common : List VExpr) :
    OriginalPiTypeRouteSide U common :=
  let selected := piPrefix ((Located.here (root := (origin.familyHeader levelsWF).reference)).castExpression shape)
  { sourceEnv := origin.source, source := [], A := A, B := B
    u := selected.view.domainLevel, v := selected.view.bodyLevel
    hu := selected.view.domainWF, hv := selected.view.bodyWF
    domain := selected.view.domain, body := selected.view.body
    rootSource := [], rootExpression := info.type.instL levels
    rootType := .sort (origin.familyHeader levelsWF).level
    root := (origin.familyHeader levelsWF).reference, initial := .nil
    location := selected.view.location, raw := .id
    graph := closedCaptureGraph (selected.view.location.contextDerivation .nil) common }

noncomputable def nativeFrame
    (origin : ConstantHeaderOrigin sourceEnv name info)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    (shape : info.type.instL levels = .forallE A B) (common : List VExpr)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    OriginalTypeRouteFrame env registry target (nativeSide origin levelsWF shape common).graph left right :=
  closedTypeRouteFrame ((nativeSide origin levelsWF shape common).location.contextDerivation .nil)
    common env registry target left right

theorem nativeFrame_environment
    (origin : ConstantHeaderOrigin sourceEnv name info)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    (shape : info.type.instL levels = .forallE A B) (common : List VExpr)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    (nativeFrame origin levelsWF shape common env registry target left right).realization.frame.dependencyEnvironment
      origin.ordered = [] := closedTypeRouteFrame_environment _ common origin.ordered

end RetainedHeaderUniverse

/-- A consumed incoming family query supplies the nonempty retained
telescope. Its first actual source application now has a whole-Pi history
to the literal Pi in that SAME header. No normalized registration header or
completed domain comparison is an input. -/
theorem retainedFirstFamilyApplyPiHistoryForHeader
    {U : Nat} {P : VEnv → Prop} {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (seed : IndependentFamilyHeader env U registry target name levels)
    (cursor : RichFamilyPlanConsumption major (seed.origin.familyHeader seed.seedWF).reference
      env registry target locals σ available name seed.seed seed.signature
      (argument :: arguments) (n := n+1) (.family demand))
    {base : OriginalCaptureBase env U registry target}
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight graph frame.realization.frame.raw)
    (headerSource : P seed.origin.source) :
    ∃ A domains, seed.signature.domains = A :: domains ∧
      ∃ shape : seed.info.type.instL seed.seed =
          .forallE A (wrapForalls domains seed.signature.result),
      let left := assignedFamilyRouteSide major initial graph 0 rfl
      let right := RetainedHeaderUniverse.nativeSide seed.origin seed.seedWF shape common
      ∃ history : OriginalApplyPiHistory env registry target commonLeft commonRight left right,
        history.AmbientGenerated base caps ∧
        history.whole.SourceGenerated P base caps ∧
        SourceCaptureGenerated P base caps commonLeft commonRight right.graph
          history.headerFrame.realization.frame.raw ∧
        history.sourceFrame = assignedFamilyRouteFrame major initial graph 0 rfl frame ∧
        history.final = [] ∧
        right.sourceEnv ≤ env ∧
        right.A = A ∧ right.B = wrapForalls domains seed.signature.result := by
  have saturated := cursor.saturated henv hscoped formed
  cases domainsEq : seed.signature.domains with
  | nil => simp only [domainsEq, List.length_nil, List.length_cons] at saturated; omega
  | cons A domains =>
    have shape : seed.info.type.instL seed.seed =
        .forallE A (wrapForalls domains seed.signature.result) := by
      simpa only [domainsEq, wrapForalls, List.foldr_cons] using seed.signature.type_eq
    let left := assignedFamilyRouteSide major initial graph 0 rfl
    let sourceFrame := assignedFamilyRouteFrame major initial graph 0 rfl frame
    have sourceGenerated : SourceCaptureGenerated P base caps commonLeft commonRight left.graph
        sourceFrame.realization.frame.raw := transport_sourceGenerated _ frame generated
    obtain ⟨selection, ledger, rootBound, equivalent, initialRoute, initialGenerated, _reserve⟩ :=
      retainedFamilyInitialRouteAt left.initial (.appFunction left.location) left.graph sourceFrame ordered below
        seed.origin seed.below seed.seedWF seed.equivalent caps sourceGenerated headerSource
    let right := RetainedHeaderUniverse.nativeSide seed.origin seed.seedWF shape common
    let headerFrame := RetainedHeaderUniverse.nativeFrame seed.origin seed.seedWF
      shape common env registry target commonLeft commonRight
    have headerGenerated : SourceCaptureGenerated P base caps commonLeft commonRight right.graph
        headerFrame.realization.frame.raw :=
      closed_sourceGenerated _ common caps commonLeft commonRight
        (seed.origin.sourceBelow.trans seed.below) headerSource
    let first := RawGeneratedTypeRoute.same left.pi.display
      (OriginalNestedDisplay.ofOccurrence left.initial (.appFunction left.location) left.graph).formationDisplay
      ordered ordered (sourceFrame.realization.frame.dependencyEnvironment ordered) sourceFrame
    have firstGenerated : first.SourceGenerated P base caps := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
      · rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨below, below⟩
      · rw [RawGeneratedTypeRoute.AllSources.eq_def]
        exact ⟨generated.sources.1.source, generated.sources.1.source, trivial⟩
      · intro boxed member
        rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
        subst boxed
        exact sourceGenerated
    have rightShape : seed.info.type.instL seed.seed =
        (VExpr.forallE right.A right.B).subst right.raw := shape.trans subst_id.symm
    let last := RawGeneratedTypeRoute.sameExpression
      (RetainedHeaderUniverse.display seed.origin seed.seedWF common) right.display rightShape
      seed.origin.ordered seed.origin.ordered [] headerFrame
    have lastGenerated : last.SourceGenerated P base caps :=
      RetainedHeaderUniverse.sourceGenerated_same _ _ _ _ _ _ _
        (seed.origin.sourceBelow.trans seed.below) (seed.origin.sourceBelow.trans seed.below)
        headerSource headerSource headerGenerated
    let selected := piPrefix
      ((Located.here (root := (seed.origin.familyHeader seed.seedWF).reference)).castExpression shape)
    let domain := Classical.choose selected.view.location.originalDomains.1
    have domainEq := Classical.choose_spec selected.view.location.originalDomains.1
    let history : OriginalApplyPiHistory env registry target commonLeft commonRight left right :=
      ⟨ordered, seed.origin.ordered, below, domain, domainEq, sourceFrame, headerFrame,
        first.trans (initialRoute.trans last)⟩
    have wholeGenerated : history.whole.SourceGenerated P base caps :=
      RetainedHeaderUniverse.sourceGenerated_trans firstGenerated
        (RetainedHeaderUniverse.sourceGenerated_trans initialGenerated lastGenerated)
    exact ⟨A, domains, rfl, shape, history,
      ⟨sourceGenerated.ambientGenerated, headerGenerated.ambientGenerated, wholeGenerated.ambientGenerated⟩,
      wholeGenerated, headerGenerated, rfl,
      RetainedHeaderUniverse.nativeFrame_environment _ _ _ _ _ _ _ _ _,
      seed.origin.sourceBelow.trans seed.below, rfl, rfl⟩


/-- Compatibility for a retained seed with an independent nominal root. -/
theorem retainedFirstFamilyApplyPiHistoryAt
    {U : Nat} {P : VEnv → Prop} {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    {seedRoot : EndpointRef seedEnv U seedSource seedExpression seedType}
    (seed : RetainedRichFamilySeed seedRoot env registry target name levels)
    (seedBelow : seedEnv ≤ env)
    (cursor : RichFamilyPlanConsumption major (seed.origin.familyHeader seed.seedWF).reference
      env registry target locals σ available name seed.seed seed.signature
      (argument :: arguments) (n := n+1) (.family demand))
    {base : OriginalCaptureBase env U registry target}
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight graph frame.realization.frame.raw)
    (headerSource : P seed.origin.source) :
    ∃ A domains, seed.signature.domains = A :: domains ∧
      ∃ shape : seed.info.type.instL seed.seed =
          .forallE A (wrapForalls domains seed.signature.result),
      let left := assignedFamilyRouteSide major initial graph 0 rfl
      let right := RetainedHeaderUniverse.nativeSide seed.origin seed.seedWF shape common
      ∃ history : OriginalApplyPiHistory env registry target commonLeft commonRight left right,
        history.AmbientGenerated base caps ∧
        history.whole.SourceGenerated P base caps ∧
        SourceCaptureGenerated P base caps commonLeft commonRight right.graph
          history.headerFrame.realization.frame.raw ∧
        history.sourceFrame = assignedFamilyRouteFrame major initial graph 0 rfl frame ∧
        history.final = [] ∧
        right.sourceEnv ≤ env ∧
        right.A = A ∧ right.B = wrapForalls domains seed.signature.result := by
  let header : IndependentFamilyHeader env U registry target name levels := {
    registrationEnv := env, ordered := henv, below := VEnv.LE.rfl
    info := seed.info, origin := seed.origin.extend seedBelow, lookup := seed.lookup
    notDefinition := seed.notDefinition, notNative := seed.notNative, notQuotient := seed.notQuotient
    seed := seed.seed, seedWF := seed.seedWF, seedLength := seed.seedLength
    levelsWF := seed.levelsWF, equivalent := seed.equivalent
    signature := seed.signature, typeClosed := seed.typeClosed, rank := seed.rank, atom := seed.atom
    typeRealization := seed.typeRealization, typeSupport := seed.typeSupport
    typeCertificate := seed.typeCertificate, typed := seed.typed
    planRealization := seed.planRealization, plan := seed.plan }
  exact retainedFirstFamilyApplyPiHistoryForHeader henv hscoped formed major initial graph frame
    ordered below header cursor generated headerSource


/-- Compatibility with a retained seed from the caller source. -/
theorem retainedFirstFamilyApplyPiHistory
    {U : Nat} {P : VEnv → Prop} {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (consumed : RetainedRichFamilyConsumption major env registry target locals σ available
      name levels (argument :: arguments) (n := n+1) (.family demand))
    {base : OriginalCaptureBase env U registry target}
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight graph frame.realization.frame.raw)
    (headerSource : P consumed.seed.origin.source) :
    ∃ A domains, consumed.seed.signature.domains = A :: domains ∧
      ∃ shape : consumed.seed.info.type.instL consumed.seed.seed =
          .forallE A (wrapForalls domains consumed.seed.signature.result),
      let left := assignedFamilyRouteSide major initial graph 0 rfl
      let right := RetainedHeaderUniverse.nativeSide consumed.seed.origin consumed.seed.seedWF shape common
      ∃ history : OriginalApplyPiHistory env registry target commonLeft commonRight left right,
        history.AmbientGenerated base caps ∧
        history.whole.SourceGenerated P base caps ∧
        SourceCaptureGenerated P base caps commonLeft commonRight right.graph
          history.headerFrame.realization.frame.raw ∧
        history.sourceFrame = assignedFamilyRouteFrame major initial graph 0 rfl frame ∧
        history.final = [] ∧
        right.sourceEnv ≤ env ∧
        right.A = A ∧ right.B = wrapForalls domains consumed.seed.signature.result := by
  exact retainedFirstFamilyApplyPiHistoryAt henv hscoped formed major initial graph frame ordered below
    consumed.seed below consumed.cursor generated headerSource

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
