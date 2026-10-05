import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyReindexData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyTailRebuild
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistorySelection

/-! Actual suffix constructors consume recursive demands under the fixed
outer caller and rebuild the original source map with its immutable reserve. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

theorem WorldGenerated.ReindexDependencyAt.captureTail
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
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (lineage : location.contextDerivation initial = context)
    (query : RichObs sourceEnv env U registry target argument locals σ (rawInput : Profile k) argumentFootprint)
    (queryAvailable : argumentFootprint.Available available)
    (queryBound : n ≤ k)
    (queryAdapter : GeneralNormalProfileAdapter env U registry target rawInput (raiseProfile k queryBound (input : Profile n)))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (ih : generated.ReindexDependencyAt index) :
    (WorldGenerated.capture generated baseline capacity domain initial argument location lineage query queryAvailable
      queryBound queryAdapter certificate resources typed arguments needs bounded covered).ReindexDependencyAt (index + 1) := by
  cases lineage
  intro frontier inRange replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline destinationCapacity destinationCovered
    callerSource callerExpression callerAssigned caller nextCommon nextLeft nextRight nextCaps rho insertion
    leftTail rightTail capsTail leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  simp only [RawOriginalRichFrame.Valid] at valid
  have tailSubstitutions := by
    cases substitutions with
    | cons tail _ _ => exact tail
  obtain ⟨tailReady⟩ := ready.selectGeneration generated
    (fun _ present => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)) rfl rfl
  let tailHereditary : generated.Hereditary frontier :=
    ⟨hereditary.tablesClosed.1, hereditary.bases, hereditary.ready⟩
  obtain ⟨leftEq, rightEq⟩ := generated.erase.capped.generated.realizations
  subst σ
  subst τ
  let tailFrame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available :=
    ⟨⟨tail, valid⟩, tailSubstitutions⟩
  have tailCapacity : environmentCost (tail.dependencyEnvironment controls.ordered) ≤
      environmentCost (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment).closures := by
    change environmentCost (tail.dependencyEnvironment controls.ordered) ≤ environmentCost (_ ++ (_ :: tail.dependencyEnvironment controls.ordered))
    rw [merge_environmentCost_append]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have tailCovered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds destinationBaseline.worlds := by
    intro world member
    apply destinationCovered world
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))))
  obtain ⟨selected⟩ := ih frontier (Nat.lt_of_succ_lt_succ inRange) replayable.1 compatible tailReady tailHereditary valid tailSubstitutions
    destinationBaseline (Nat.le_trans tailCapacity destinationCapacity) tailCovered
    caller insertion leftTail rightTail capsTail left leftControls sameCutoff sameFuel
    leftBaseline leftFrame leftData henv hscoped formed requested requestedAvailable requestedReady sponsored bank unary
  exact rebuildWorldCaptureVariableDependency controls tailFrame generated baseline capacity domain initial argument location rfl
    query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered substitutions
    frontier replayable ready compatible hereditary selected.realization selected.generation selected.replayable
    selected.controlled selected.compatible selected.hereditary
    (Nat.le_trans (selected.capacity controls.ordered) capacity)
    (Covered.trans EquationControlMeasure.less_trans selected.covered replayable.2) selected.dependency

theorem WorldGenerated.ReindexDependencyAt.bindTail
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
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (ih : generated.ReindexDependencyAt index) :
    (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).ReindexDependencyAt (index + 1) := by
  intro frontier inRange replayable compatible ready hereditary valid substitutions
    destinationEnvironment destinationBaseline destinationCapacity destinationCovered
    callerSource callerExpression callerAssigned caller nextCommon nextLeft nextRight nextCaps rho insertion
    leftTail rightTail capsTail leftAssigned left leftControls sameCutoff sameFuel
    leftEnvironment leftBaseline leftLocals leftAvailable leftFrame leftData henv hscoped formed
    rank profile requestedFootprint requested requestedAvailable requestedReady sponsored bank unary
  simp only [RawOriginalRichFrame.Valid] at valid
  have tailSubstitutions := by
    cases substitutions with
    | cons tail _ _ => exact tail
  obtain ⟨tailReady⟩ := ready.selectGeneration generated
    (fun _ present => List.mem_cons_of_mem _ present) rfl rfl
  let tailHereditary : generated.Hereditary frontier :=
    ⟨hereditary.tablesClosed.1, hereditary.bases, hereditary.ready⟩
  obtain ⟨leftEq, rightEq⟩ := generated.erase.capped.generated.realizations
  subst σ
  subst τ
  let tailFrame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available :=
    ⟨⟨tail, valid⟩, tailSubstitutions⟩
  have tailCapacity : environmentCost (tail.dependencyEnvironment controls.ordered) ≤
      environmentCost (reservedBindWorldEnvironment controls domain baseline generated.environment).closures := by
    change environmentCost (tail.dependencyEnvironment controls.ordered) ≤ environmentCost (_ ++ (_ :: tail.dependencyEnvironment controls.ordered))
    rw [merge_environmentCost_append]
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have tailCovered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds destinationBaseline.worlds := by
    intro world member
    apply destinationCovered world
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)
  let skip : Ctx.Lift' (.skip .refl) common (annotation :: common) := .skip .refl
  have liftedLeft : Subst.lift_l ((Lift.skip .refl).comp rho) nextLeft = commonLeft := by
    calc
      _ = (Subst.lift_l rho nextLeft).tail := by funext i; simp [Subst.lift_l, Lift.liftVar_comp, Subst.tail]
      _ = _ := by rw [leftTail]; rfl
  have liftedRight : Subst.lift_l ((Lift.skip .refl).comp rho) nextRight = commonRight := by
    calc
      _ = (Subst.lift_l rho nextRight).tail := by funext i; simp [Subst.lift_l, Lift.liftVar_comp, Subst.tail]
      _ = _ := by rw [rightTail]; rfl
  have liftedCaps : (fun i => nextCaps (((Lift.skip .refl).comp rho).liftVar i)) = caps := by
    funext i
    simpa only [Lift.liftVar_comp, Lift.liftVar, CaptureCaps.push] using congrFun capsTail (i + 1)
  have expression : (raw index).lift' ((Lift.skip .refl).comp rho) = (raw.lift (index + 1)).lift' rho := by
    rw [lift'_comp]
    simp only [Subst.lift, lift_eq_lift']
  let inputDisplay : OriginalNestedDisplay U nextCommon ((raw index).lift' ((Lift.skip .refl).comp rho)) leftAssigned := {
    left with expression_eq := expression.trans left.expression_eq }
  let inputData : WorldCallFrameData (P := P) (base := base) (caps := nextCaps)
      (display := inputDisplay) leftControls leftBaseline frontier leftFrame :=
    ⟨leftData.generation, leftData.replayable, leftData.controlled, leftData.compatible,
      leftData.closed, leftData.capacity, leftData.covered, leftData.hereditary⟩
  obtain ⟨selected⟩ := ih frontier (Nat.lt_of_succ_lt_succ inRange) replayable.1 compatible tailReady tailHereditary valid tailSubstitutions
    destinationBaseline (Nat.le_trans tailCapacity destinationCapacity) tailCovered
    caller (skip.comp insertion) liftedLeft liftedRight liftedCaps inputDisplay leftControls sameCutoff sameFuel
    leftBaseline leftFrame inputData henv hscoped formed requested requestedAvailable requestedReady sponsored bank unary
  exact rebuildWorldBinderVariableDependency controls tailFrame generated baseline capacity domain annotation displayed
    certificate resources typed arguments needs bounded covered substitutions frontier replayable ready compatible hereditary
    selected.realization selected.generation selected.replayable selected.controlled selected.compatible selected.hereditary
    (Nat.le_trans (selected.capacity controls.ordered) capacity)
    (Covered.trans EquationControlMeasure.less_trans selected.covered replayable.2) selected.dependency

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
