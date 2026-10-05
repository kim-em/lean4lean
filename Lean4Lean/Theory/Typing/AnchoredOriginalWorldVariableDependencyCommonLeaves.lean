import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableCommonDependency
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyReindexData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyBindHead

/-! The common identity and fresh binder cases compute their input program
from the actual source generation. Captured source leaves are expanded before
any immutable common cap is used. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private noncomputable def pullCommonCaps
    {caps nextCaps : CaptureCaps} {rho : Lift}
    (program : VariableDependencyProgram env U registry target nextCaps (rho.liftVar index) profile)
    (capsTail : (fun i => nextCaps (rho.liftVar i)) = caps) :
    VariableDependencyProgram env U registry target caps index profile :=
  program.renameIndex (fun _ => index) (fun i need member fits => by
    have same := program.trace.indices member
    subst i
    have equal := congrFun capsTail index
    rw [← equal]
    exact fits)

/-- Identity retains the actual base frame. Every needed common leaf is
proved to belong to that base by source-generation expansion, including when
the incoming original variable lives behind captures or charged recipes. -/
theorem WorldGenerated.ReindexDependencyAt.identity
    {strata : EquationStratification env} {P : VEnv → Prop}
    (base : OriginalCaptureBase env U registry target)
    (ambient : base.frame.Ambient) (sources : base.frame.raw.AllSources P)
    (controls : OriginalWorldControls strata base.sourceEnv)
    (environment : WorldEnvironmentProvenance strata U (base.frame.dependencyEnvironment controls.ordered)) :
    (WorldGenerated.identity ambient sources controls environment).ReindexDependencyAt index := by
  intro frontier inRange replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline capacity covered
    callerSource callerExpression callerAssigned caller nextCommon nextLeft nextRight nextCaps rho insertion
    leftTail rightTail capsTail leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  obtain ⟨expanded⟩ := leftData.generation.commonVariableQuery henv hscoped formed
    leftData.hereditary.tablesClosed requested requestedAvailable (by
      simpa only [Subst.id, VExpr.lift'] using left.expression_eq.symm)
  let program := pullCommonCaps expanded capsTail
  let actual := WorldGenerated.identity ambient sources controls environment
  let realization : OriginalCaptureRealization (.identity base.context) env registry target
      base.locals base.left base.right base.available := ⟨base.frame, substitutions⟩
  refine ⟨{
    locals := base.locals, available := base.available, realization := realization
    generation := actual, replayable := replayable, controlled := ready, compatible := compatible
    hereditary := hereditary, capacity := fun _ => Nat.le_refl _, covered := Covered.refl _
    dependency := {
      rank := program.rank, bound := program.bound, raw := program.raw
      footprint := program.footprint, trace := program.trace, adapter := program.adapter
      resources := program.resources } }⟩

/-- Fresh binder zero installs precisely the finite source-derived program.
Its original tail, rich domain certificate, argument relation and immutable
reserve are retained by the actual bind-head producer. -/
theorem WorldGenerated.ReindexDependencyAt.bindHead
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {tail : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {controls : OriginalWorldControls strata sourceEnv}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph tail controls)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (tail.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (annotation : VExpr) (displayed : A.subst raw = annotation)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).ReindexDependencyAt 0 := by
  intro frontier inRange replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline destinationCapacity destinationCovered
    callerSource callerExpression callerAssigned caller nextCommon nextLeft nextRight nextCaps rho insertion
    leftTail rightTail capsTail leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  obtain ⟨expanded⟩ := leftData.generation.commonVariableQuery henv hscoped formed
    leftData.hereditary.tablesClosed requested requestedAvailable (by
      simpa only [Subst.lift, VExpr.lift'] using left.expression_eq.symm)
  let program := pullCommonCaps expanded capsTail
  simp only [RawOriginalRichFrame.Valid] at valid
  have tailSubstitutions := by
    cases substitutions with
    | cons tail _ _ => exact tail
  obtain ⟨leftEq, rightEq⟩ := generated.erase.capped.generated.realizations
  subst σ
  subst τ
  let tailFrame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available :=
    ⟨⟨tail, valid⟩, tailSubstitutions⟩
  exact realizeWorldBinderHeadDependency controls tailFrame generated baseline capacity domain annotation displayed
    certificate resources typed arguments needs bounded covered substitutions frontier replayable ready compatible hereditary program

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
