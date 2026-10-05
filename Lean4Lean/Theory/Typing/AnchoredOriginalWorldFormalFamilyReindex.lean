import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFormalFamilyDestination
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations

/-! Replay the actual caller's family code onto the genuine formal family
original. Both recursive calls are computed below the enclosing projection.
The formal frame is the positive parameter-capture producer's frame, and its
retained worlds keep their actual sponsorship rather than a numeric surrogate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private from_right from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
open private inheritedCall from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordMajorBridge
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- The family's installed declaration stage pays the actual new original
root. Its captures are paid by their existing individual strict edges. -/
theorem ProjectionParameterOrigin.formalNode_below
    {strata : EquationStratification env}
    (origin : VEnv.ProjectionParameterOrigin sourceEnv name info)
    (controls : OriginalWorldControls strata sourceEnv)
    (node : EndpointState origin.types U formalSource expression assigned)
    (formalWorld : WorldEnvironmentProvenance strata U formalEnvironment)
    (caller : EndpointState sourceEnv U source callerExpression callerAssigned)
    (callerWorld : WorldEnvironmentProvenance strata U callerEnvironment)
    (phase parentPhase : RichPhase)
    (inherited : Sponsored [originalCallWorld controls parentPhase caller callerWorld] formalWorld.worlds) :
    WorldBelow strata.rules.length
      (originalCallWorld (controls.atHeader origin.constructorOrigin) phase node formalWorld)
      (originalCallWorld controls parentPhase caller callerWorld) := by
  apply Below.root
    (EquationControlMeasure.constantsDecrease (origin.types_count_lt controls.ordered) _ _ _ _ _)
  intro child member
  obtain ⟨parent, present, smaller⟩ := inherited child member
  cases List.mem_singleton.mp present
  exact smaller

section
variable
  {strata : EquationStratification env} {P : VEnv → Prop}
  {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
  {outer : EndpointState sourceEnv U source (.proj name field major) assigned}
  (head : ProjectionHead outer)
  (origin : VEnv.ProjectionParameterOrigin sourceEnv name info)
  {levels : List VLevel} {C D : VExpr}
  {signature : ConstantTelescope (origin.family.type.instL levels)}
  {domains : signature.domains = [C,D]}
  (destination : FormalFamilyDestination (U := U) origin signature domains)
  {callerNode : EndpointState sourceEnv U source (.app (.app (.const name levels) a) p) callerAssigned}
  (location : Located (.right head.major) callerNode)
  (initial : ContextDerivation sourceEnv U source)
  (callerGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) callerRaw)
  (formalGraph : OriginalCaptureMap (common := common) destination.context
    ((Subst.id.cons (a.subst callerRaw)).cons (p.subst callerRaw)))
  (controls : OriginalWorldControls strata sourceEnv)
  (callerWorld : WorldEnvironmentProvenance strata U callerEnvironment)
  (formalWorld : WorldEnvironmentProvenance strata U formalEnvironment)
  (frontier : List (World strata.rules.length)) (other : World strata.rules.length)

local notation "callerDisplay" => OriginalNestedDisplay.ofOccurrence initial location callerGraph
local notation "formalDisplay" => destination.display formalGraph
local notation "parentWorld" => originalCallWorld controls RichPhase.assignedComparison outer callerWorld
local notation "formalControls" => controls.atHeader origin.constructorOrigin

include head location

/-- Both R worlds genuinely replace the current projection world. This
guard uses the selected caller baseline and the immutable captured history
reserved by the actual formalization producer. -/
theorem FormalFamilyDestination.reindexFunding
    (inherited : Sponsored [parentWorld] formalWorld.worlds)
    (paid : Sponsored frontier [other, parentWorld]) :
    CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .expressionReindex callerNode callerWorld,
        originalCallWorld formalControls .expressionReindex destination.node formalWorld])
      (frontier ++ [other, parentWorld]) ∧
    Sponsored frontier
      [originalCallWorld controls .expressionReindex callerNode callerWorld,
        originalCallWorld formalControls .expressionReindex destination.node formalWorld] := by
  have callerBelow := ProjectionHead.parameter_below head location controls callerWorld .expressionReindex .assignedComparison
  have formalBelow := ProjectionParameterOrigin.formalNode_below origin controls destination.node
    formalWorld outer callerWorld .expressionReindex .assignedComparison inherited
  apply inheritedCall frontier (from_right ?_) paid
  · intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨parentWorld, by simp, callerBelow⟩
    · cases List.mem_singleton.mp member
      exact ⟨parentWorld, by simp, formalBelow⟩
  · intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact callerBelow
    · cases List.mem_singleton.mp member
      exact formalBelow

/-- Execute the proper caller-to-formal R and extract code on that SAME
selected formal frame. No requested family relation, right query, or strict
recursive guard is supplied. The finite capture frame and its sponsorship
are the intermediate output of declaration-cell capture construction. -/
theorem FormalFamilyDestination.reindexCallerCodeWorld
    (callerFrame : OriginalCaptureRealization callerGraph env registry target
      callerLocals commonLeft commonRight callerAvailable)
    (callerData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := callerDisplay) controls callerWorld frontier callerFrame)
    (formalFrame : OriginalCaptureRealization formalGraph env registry target
      formalLocals commonLeft commonRight formalAvailable)
    (formalData : WorldCallFrameData (P := P) (base := base) (caps := caps)
      (display := formalDisplay) formalControls formalWorld frontier formalFrame)
    (inherited : Sponsored [parentWorld] formalWorld.worlds)
    (paid : Sponsored frontier [other, parentWorld])
    (certificate : RichCert sourceEnv env U registry target callerNode callerLocals
      (callerRaw.comp commonLeft) relevant (profile : Profile n) footprint)
    (resources : footprint.Available callerAvailable)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (henv : env.Ordered)
    (bank : WorldBoundedCallBank env U registry strata P (frontier ++ [other, parentWorld])) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps formalDisplay commonLeft commonRight profile
        (environmentCost formalEnvironment),
    ∃ data : WorldGeneratedQueryReplyData (P := P) formalControls formalWorld frontier reply,
    ∃ outputFootprint,
    ∃ output : RichCert origin.types env U registry target destination.node
        reply.answer.reply.locals ((formalDisplay).raw.comp commonLeft) relevant profile outputFootprint,
    ∃ outputReady : ControlledStoredQuery formalControls frontier (.certificate output),
      outputFootprint.Available reply.answer.reply.available ∧
      outputReady.annotation.worlds ⊆ data.query.annotation.worlds := by
  obtain ⟨smaller, sponsored⟩ := FormalFamilyDestination.reindexFunding (head := head) (origin := origin) (destination := destination)
    (location := location) controls callerWorld formalWorld frontier other inherited paid
  obtain ⟨reply, ⟨data⟩⟩ := bank.observation _ smaller base caps callerDisplay formalDisplay
    commonLeft commonRight controls formalControls rfl rfl callerWorld formalWorld frontier rfl sponsored
    callerFrame callerData formalFrame formalData (.code certificate) resources ready.code
  obtain ⟨outputFootprint, output, outputReady, available, worlds⟩ :=
    reply.answer.reply.query.code_controlled henv formalControls data.query certificate.formed
  exact ⟨reply, data, outputFootprint, output, outputReady, available, worlds⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
