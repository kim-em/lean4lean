import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandReindexData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureDemandScope
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistorySelection

/-! The actual ordinary-capture arm of variable-demand reconstruction. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem WorldGenerated.ReindexDemandAt.capture
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
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    (WorldGenerated.capture generated baseline capacity domain initial argument location lineage query queryAvailable
      queryBound queryAdapter certificate resources typed arguments needs bounded covered).ReindexDemandAt 0 := by
  cases lineage
  intro frontier replayable compatible ready hereditary valid substitutions
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
  let input : OriginalNestedDisplay U nextCommon (a.subst (raw.lift_r rho)) leftAssigned := {
    left with expression_eq := lift'_subst.symm.trans left.expression_eq }
  let inputData : WorldCallFrameData (P := P) (base := base) (caps := nextCaps)
      (display := input) leftControls leftBaseline frontier leftFrame :=
    ⟨leftData.generation, leftData.replayable, leftData.controlled, leftData.compatible,
      leftData.closed, leftData.capacity, leftData.covered, leftData.hereditary⟩
  exact reindexWorldOwnCaptureDemandUnder initial argument location domain controls tailFrame generated frontier tailReady
    replayable.1 compatible tailHereditary baseline capacity replayable.2 destinationBaseline
    destinationCapacity destinationCovered caller insertion leftTail rightTail capsTail input leftControls sameCutoff sameFuel
    leftBaseline leftFrame inputData henv hscoped formed requested requestedAvailable requestedReady sponsored bank unary

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
