import Lean4Lean.Theory.Typing.AnchoredOriginalCaptureFootprint
import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalEtaProjections

/-! Projection queries retained at actual original endpoints. A whole cut
keeps its complete query and recovers the original projection rule through
its finite conversion route. The rule's stored source major may differ from
the displayed major; its actual equality is retained rather than replaced
by a synthesized canonical typing.

This is the origin part of the typed-query producer. It does not identify a
frozen record-field domain with the original assigned field type, nor assert
that an arbitrary current observer admits the eventual record query policy.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

/-- Every field is extracted from the actual original projection head.
The incoming assigned type is connected to that head by the retained route. -/
structure ProjectionHead
    (node : EndpointState sourceEnv U source (.proj name index displayedMajor) assigned) where
  info : VProjectionInfo
  registered : sourceEnv.projections name info
  levels : List VLevel
  levelsWF : ∀ level ∈ levels, level.WF U
  levelCount : levels.length = info.uvars
  parameters : List VExpr
  parameterCount : parameters.length = info.nparams
  indices : List VExpr
  indexCount : indices.length = info.nindices
  sourceMajor : VExpr
  fieldType : VExpr
  selected : info.fieldType name levels parameters index sourceMajor = some fieldType
  fieldLevel : VLevel
  fieldWF : fieldLevel.WF U
  field : EndpointState sourceEnv U source fieldType (.sort fieldLevel)
  major : Derivation sourceEnv U source sourceMajor displayedMajor
    (mkApps (.const name levels) (parameters ++ indices))
  closed : info.ctorType.Closed
  relevance : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero
  route : PrefixRoute sourceEnv U source (.proj name index displayedMajor) node
    (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
      field major closed relevance)

/-- Construct the projection node from an original endpoint. No projection
metadata, domain alignment, or fresh original proof is supplied by the caller. -/
noncomputable def projectionHead
    (node : EndpointState sourceEnv U source (.proj name index displayedMajor) assigned) :
    ProjectionHead node := by
  obtain ⟨type, head, route, normal⟩ := prefixHead node
  cases head with
  | ref reference => exact (reference.primitive_atomic normal).elim
  | convert plan term => exact normal.elim
  | proj registered levelsWF levelCount parameterCount indexCount selected fieldWF
      field major closed relevance =>
    exact ⟨_, registered, _, levelsWF, levelCount, _, parameterCount, _, indexCount,
      _, _, selected, _, fieldWF, field, major, closed, relevance, route⟩

/-- The query is indexed by the cut's actual original assigned type. Its
observation is retained before reflection, including all finite wrappers. -/
structure OriginalProjectionQuery
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (node : EndpointState sourceEnv U source (.proj name index displayedMajor) assigned)
    (locals : List Nat) (realization : Subst) (demand : Profile n) (footprint : Footprint) where
  observation : Obs env U registry target locals realization
    (.proj name index displayedMajor) demand footprint
  head : ProjectionHead node

noncomputable def Obs.originalProjectionQuery
    (observation : Obs env U registry target locals realization
      (.proj name index displayedMajor) demand footprint)
    (node : EndpointState sourceEnv U source (.proj name index displayedMajor) assigned) :
    OriginalProjectionQuery env registry target node locals realization demand footprint :=
  ⟨observation, projectionHead node⟩

/-- A selected whole cut reconstructs its projection node without dropping
its original query or assigning a type to a substituted residual. In
particular `head.major` is the original equality Z→displayed-major↑. -/
noncomputable def WholeCutQuery.originalProjection
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : CutOriginAt root boundary argument baseDepth}
    {footprint : Footprint}
    (whole : WholeCutQuery (env := env) origin registry target σ demand footprint)
    (expression : argument = .proj name index major) :
    OriginalProjectionQuery env registry target
      (origin.view.cast (origin.expression_eq.trans
        (congrArg (fun (e : VExpr) => e.lift' (.skipN .refl origin.depth)) expression)) rfl)
      whole.locals whole.realization demand whole.footprint := by
  let equal := origin.expression_eq.trans
    (congrArg (fun (e : VExpr) => e.lift' (.skipN .refl origin.depth)) expression)
  have observation := whole.observation
  rw [equal] at observation
  exact Obs.originalProjectionQuery observation _

/-- The finite capture lookup supplies the entire actual projection query.
No additional observer or typing premise is requested at this step. -/
noncomputable def SelectedCapture.originalProjection
    (selected : SelectedCapture (env := env) root registry target locals σ arguments
      baseDepth budget before captureIndex inBounds need)
    (expression : arguments[arguments.length - 1 - captureIndex] = .proj name index major) :
    OriginalProjectionQuery env registry target
      (selected.origin.view.cast (selected.origin.expression_eq.trans
        (congrArg (fun (e : VExpr) => e.lift' (.skipN .refl selected.origin.depth)) expression)) rfl)
      selected.whole.locals selected.whole.realization need.profile selected.whole.footprint :=
  selected.whole.originalProjection expression

/-- Eta's constructor child supplies each actual projection endpoint. The
observer comes from its original finite constructor capture, with its grade
and footprint unchanged. This does not assert source record-join coverage. -/
noncomputable def etaOriginalProjectionQuery
    {info : VProjectionInfo}
    (constructor : Derivation sourceEnv U source
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map (fun index => .proj name index major)))
      (mkApps (.const info.ctorName levels)
        (parameters ++ (List.range info.numFields).map (fun index => .proj name index major)))
      (mkApps (.const name levels) parameters))
    (index : Nat) (bound : index < info.numFields)
    (observation : Obs env U registry target locals σ (.proj name index major) demand footprint) :
    OriginalProjectionQuery env registry target
      (etaProjectionArgument constructor index bound).node locals σ demand footprint :=
  Obs.originalProjectionQuery observation _

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
