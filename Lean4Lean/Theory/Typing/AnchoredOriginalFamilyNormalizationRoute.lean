import Lean4Lean.Theory.Typing.AnchoredOriginalClosedTypeRouteData
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationDispatch
import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteGeneration

/-! Retain the actual closed declaration normalization as finite original
route data. Neither its assigned expression nor the caller's requested
profile is restricted to a literal universe. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

private theorem route_trans_reserve
    (first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate)
    (second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final) :
    (first.trans second).reserve = first.reserve ++ second.reserve := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

private theorem route_typedEquality_reserve
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B assigned)
    (left : OriginalNestedDisplay U common expression (.sort level))
    (same : expression = A.subst raw)
    (leftOrdered : left.sourceEnv.Ordered) (ordered : sourceEnv.Ordered)
    (below : sourceEnv ≤ env) (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
    (RawGeneratedTypeRoute.typedEquality graph original left same leftOrdered ordered below initial frame).reserve =
      [.bundle (.close (left.node.dependencyOrigin leftOrdered) initial)
        (.close (original.dependencyOrigin ordered) (frame.realization.frame.dependencyEnvironment ordered)),
       .close (original.dependencyOrigin ordered) (frame.realization.frame.dependencyEnvironment ordered)] := by
  rw [RawGeneratedTypeRoute.reserve.eq_def]

/-- The native Pi retains the actual right normalization root and its
selected original domain/body children. Its closed baseline is computed. -/
noncomputable def normalizedFamilyRouteSide
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (positive : 0 < info.nparams) (common : List VExpr) : OriginalPiTypeRouteSide U common :=
  let head := normalizedFamilyPrefix packet positive
  {
    sourceEnv := packet.origin.base, source := []
    A := head.domainExpression, B := head.bodyExpression
    u := head.selected.view.domainLevel, v := head.selected.view.bodyLevel
    hu := head.selected.view.domainWF, hv := head.selected.view.bodyWF
    domain := head.selected.view.domain, body := head.selected.view.body
    rootSource := [], rootExpression := packet.shape.normalized.instL levels
    rootType := packet.shape.assigned.instL levels
    root := .right packet.instantiated.normalization, initial := .nil
    location := head.selected.view.location
    raw := .id
    graph := closedCaptureGraph (head.selected.view.location.contextDerivation .nil) common }

/-- Keep the selected declaration header itself as the sorted witness for
normalization. Equality of registry lookups changes only the display index. -/
noncomputable def RichHeaderSelection.normalizationDisplay
    {info : VProjectionInfo}
    {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (common : List VExpr) :
    OriginalNestedDisplay U common
      (((selectProjectionParameters ordered registered selection.seedWF).origin.family.type.instL selection.seed).subst .id)
      (.sort selection.header.level) where
  sourceEnv := selection.header.source
  source := []
  sourceExpression := selection.info.type.instL selection.seed
  sourceType := .sort selection.header.level
  context := .nil
  node := .ref (.left selection.header.original)
  provenance := .ofLocation .here .nil
  raw := .id
  graph := closedCaptureGraph .nil common
  expression_eq := by
    have same : selection.info =
        (selectProjectionParameters ordered registered selection.seedWF).origin.family.toVConstant :=
      Option.some.inj (selection.lookup.symm.trans
        (selectProjectionParameters ordered registered selection.seedWF).origin.familyPresent)
    rw [same]
  type_eq := rfl

noncomputable def RichHeaderSelection.normalizationFrame
    {info : VProjectionInfo}
    {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (common : List VExpr)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (left right : Subst) :
    OriginalTypeRouteFrame env registry target (selection.normalizationDisplay registered common).graph left right :=
  closedTypeRouteFrame .nil common env registry target left right

noncomputable def normalizedFamilyRouteFrame
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (positive : 0 < info.nparams) (common : List VExpr)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (left right : Subst) :
    OriginalTypeRouteFrame env registry target (normalizedFamilyRouteSide packet positive common).graph left right :=
  closedTypeRouteFrame ((normalizedFamilyPrefix packet positive).selected.view.location.contextDerivation .nil)
    common env registry target left right

theorem normalizedFamilyRouteSide_domain
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (positive : 0 < info.nparams) (common : List VExpr) :
    (normalizedFamilyRouteSide packet positive common).domain =
      .ref (normalizedFamilyPrefix packet positive).domainOriginal :=
  (normalizedFamilyPrefix packet positive).domain_eq

theorem normalizedFamilyRouteFrame_capped
    (packet : OriginalProjectionParameters sourceEnv U name info levels)
    (positive : 0 < info.nparams) (common : List VExpr)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps)
    (left right : Subst) :
    CappedCaptureGenerated base caps left right (normalizedFamilyRouteSide packet positive common).graph
      (normalizedFamilyRouteFrame packet positive common env registry target left right).realization.frame.raw :=
  closedTypeRouteFrame_capped _ common caps left right

/-- At a primitive constant the assigned seed header is closed. Its actual
formation occurrence can therefore enter the selected earlier header at
the identical source expression, under any retained caller capture map. -/
noncomputable def RichHeaderSelection.assignedHeaderRoute
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression (selection.info.type.instL selection.seed)}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
    RawGeneratedTypeRoute env registry target commonLeft commonRight
      (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
      (selection.normalizationDisplay registered common)
      (frame.realization.frame.dependencyEnvironment ordered)
      ((selection.normalizationFrame registered common env registry target commonLeft commonRight).realization.frame.dependencyEnvironment
        selection.header.ordered) :=
  .sameExpression (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
    (selection.normalizationDisplay registered common) (by
      have same : selection.info =
          (selectProjectionParameters ordered registered selection.seedWF).origin.family.toVConstant :=
        Option.some.inj (selection.lookup.symm.trans
          (selectProjectionParameters ordered registered selection.seedWF).origin.familyPresent)
      rw [(ordered.closedC selection.lookup).instL.subst_eq (σ := raw) .zero, subst_id]
      rw [same])
    ordered selection.header.ordered (frame.realization.frame.dependencyEnvironment ordered)
    (selection.normalizationFrame registered common env registry target commonLeft commonRight)

theorem RichHeaderSelection.assignedHeaderRoute_generated
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression (selection.info.type.instL selection.seed)}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps) :
    (selection.assignedHeaderRoute registered initial location graph frame).Generated base caps := by
  apply RawGeneratedTypeRoute.sameExpression_generated
  exact closedTypeRouteFrame_capped .nil common caps commonLeft commonRight

/-- The first declaration route is produced from the stored earlier
header and the actual normalization equality. The equality may have an
arbitrary assigned expression; the selected header supplies its genuine
sorted source witness to the finite typed-equality step. -/
noncomputable def RichHeaderSelection.normalizationRoute
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    let packet := selectProjectionParameters ordered registered selection.seedWF
    RawGeneratedTypeRoute env registry target left right
      (selection.normalizationDisplay registered common)
      (normalizedFamilyRouteSide packet positive common).display []
      ((normalizedFamilyRouteFrame packet positive common env registry target left right).realization.frame.dependencyEnvironment
        packet.origin.baseOrdered) :=
  let packet := selectProjectionParameters ordered registered selection.seedWF
  let graph := closedCaptureGraph (ContextDerivation.nil (env := packet.origin.base) (U := U)) common
  let normalizationFrame := closedTypeRouteFrame .nil common env registry target left right
  let header := selection.normalizationDisplay registered common
  let side := normalizedFamilyRouteSide packet positive common
  .trans
    (.typedEquality graph packet.instantiated.normalization header rfl selection.header.ordered
      packet.origin.baseOrdered (packet.origin.baseBelow.trans below) [] normalizationFrame)
    (.sameExpression (graph.typeEqualityDisplay packet.instantiated.normalization false) side.display
      (congrArg (fun expression => expression.subst Subst.id) (normalizedFamilyPrefix packet positive).shape)
      packet.origin.baseOrdered packet.origin.baseOrdered
      (normalizationFrame.realization.frame.dependencyEnvironment packet.origin.baseOrdered)
      (normalizedFamilyRouteFrame packet positive common env registry target left right))

theorem RichHeaderSelection.normalizationRoute_generated
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (below : sourceEnv ≤ env) (common : List VExpr)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps) (left right : Subst) :
    (selection.normalizationRoute registered positive below common registry target left right).Generated base caps := by
  let packet := selectProjectionParameters ordered registered selection.seedWF
  have last := RawGeneratedTypeRoute.sameExpression_generated
    ((closedCaptureGraph (ContextDerivation.nil (env := packet.origin.base) (U := U)) common).typeEqualityDisplay
      packet.instantiated.normalization false)
    (normalizedFamilyRouteSide packet positive common).display
    (congrArg (fun expression => expression.subst Subst.id) (normalizedFamilyPrefix packet positive).shape)
    packet.origin.baseOrdered packet.origin.baseOrdered
    ((closedTypeRouteFrame (ContextDerivation.nil (U := U)) common env registry target left right).realization.frame.dependencyEnvironment
      packet.origin.baseOrdered)
    (normalizedFamilyRouteFrame packet positive common env registry target left right)
    (normalizedFamilyRouteFrame_capped packet positive common caps left right (base := base))
  refine ⟨?_, ?_⟩
  · rw [normalizationRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
    refine ⟨?_, last.wellFormed⟩
    rw [RawGeneratedTypeRoute.WellFormed.eq_def]
    trivial
  · intro boxed member
    rw [normalizationRoute, RawGeneratedTypeRoute.frames.eq_def] at member
    rcases List.mem_append.mp member with first | final
    · rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at first
      subst boxed
      exact closedTypeRouteFrame_capped .nil common caps left right
    · exact last.frames boxed final

theorem RichHeaderSelection.normalizationRoute_reserve
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (below : sourceEnv ≤ env) (common : List VExpr)
    (registry : CanonicalHead.Registry) (target : List VExpr) (left right : Subst) :
    let packet := selectProjectionParameters ordered registered selection.seedWF
    let header := Closure.close (selection.header.original.dependencyOrigin selection.header.ordered) []
    let normalizer := Closure.close (packet.instantiated.normalization.dependencyOrigin packet.origin.baseOrdered) []
    let native := Closure.close ((normalizedFamilyRouteSide packet positive common).display.node.dependencyOrigin
      packet.origin.baseOrdered) []
    (selection.normalizationRoute registered positive below common registry target left right).reserve =
      [.bundle header normalizer, normalizer, .bundle normalizer native] := by
  dsimp only
  rw [normalizationRoute, route_trans_reserve, route_typedEquality_reserve,
    RawGeneratedTypeRoute.sameExpression_reserve]
  simp only [normalizedFamilyRouteFrame, closedTypeRouteFrame_environment,
    RichHeaderSelection.normalizationDisplay, EndpointState.dependencyOrigin,
    EndpointRef.dependencyOrigin, OriginalCaptureMap.typeEqualityDisplay,
    originalTypeRouteSide, List.cons_append, List.nil_append]
  simp only [normalizedFamilyRouteSide, OriginalPiTypeRouteSide.display,
    OriginalNestedDisplay.ofOccurrence, closedTypeRouteFrame_environment]

/-- Connect an actual constant's assigned formation directly to the native
normalized declaration Pi. All intermediate frames are computed closed
frames; the caller supplies no normalized query or semantic alignment. -/
noncomputable def RichHeaderSelection.initialNormalizationRoute
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (below : sourceEnv ≤ env)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression (selection.info.type.instL selection.seed)}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
    let packet := selectProjectionParameters ordered registered selection.seedWF
    RawGeneratedTypeRoute env registry target commonLeft commonRight
      (OriginalNestedDisplay.ofOccurrence initial location graph).formationDisplay
      (normalizedFamilyRouteSide packet positive common).display
      (frame.realization.frame.dependencyEnvironment ordered)
      ((normalizedFamilyRouteFrame packet positive common env registry target commonLeft commonRight).realization.frame.dependencyEnvironment
        packet.origin.baseOrdered) :=
  .trans (selection.assignedHeaderRoute registered initial location graph frame)
    (selection.normalizationRoute registered positive below common registry target commonLeft commonRight)

theorem RichHeaderSelection.initialNormalizationRoute_generated
    {info : VProjectionInfo} {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (positive : 0 < info.nparams)
    (below : sourceEnv ≤ env)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression (selection.info.type.instL selection.seed)}
    (initial : ContextDerivation sourceEnv U rootSource) (location : Located root node)
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    {base : OriginalCaptureBase env U registry target} (caps : CaptureCaps) :
    (selection.initialNormalizationRoute registered positive below initial location graph frame).Generated base caps := by
  have first := selection.assignedHeaderRoute_generated registered initial location graph frame caps (base := base)
  have second := selection.normalizationRoute_generated registered positive below common caps commonLeft commonRight
    (base := base)
  refine ⟨?_, ?_⟩
  · rw [initialNormalizationRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
    exact ⟨first.wellFormed, second.wellFormed⟩
  · intro boxed member
    rw [initialNormalizationRoute, RawGeneratedTypeRoute.frames.eq_def] at member
    rcases List.mem_append.mp member with earlier | later
    · exact first.frames boxed earlier
    · exact second.frames boxed later

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
