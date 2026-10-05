import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeArgumentTransport
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalPiTypeRouteSide

/-! A constructive heterogeneous one-binder recipe experiment. The declared
Pi recipe remains in its actual header frame, while the argument comparison
selects and merges its own destination frames. No union of these unrelated
footprints is advertised. The final result is an actual retained destination
display, so no new original derivation of the substituted declared body is
assumed. This proves interpretation of the proposed instance payload, not
that the shared grammar already contains that payload or its future visitor.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem replayHeterogeneousRecipeBody
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (header : OriginalPiTypeRouteSide U common)
    {left : OriginalNestedDisplay U common expression (header.A.subst header.raw)}
    {right : OriginalNestedDisplay U common expression assigned}
    {n : Nat} {input support : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (leftWorld : WorldEnvironmentProvenance strata U leftEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U rightEnvironment)
    (frontier parent : List (World strata.rules.length))
    (leftFrame : OriginalCaptureRealization left.graph env registry target leftLocals commonLeft commonRight leftAvailable)
    (leftData : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := left)
      leftControls leftWorld frontier leftFrame)
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals commonLeft commonRight rightAvailable)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := caps) (display := right)
      rightControls rightWorld frontier rightFrame)
    (certificate : RichCert left.sourceEnv env U registry target left.node.typeFormation.node leftLocals
      (left.raw.comp commonLeft) true support footprint)
    (resources : footprint.Available leftAvailable)
    (certificateReady : ControlledStoredQuery leftControls frontier (.certificate certificate))
    (typed : (input : Profile n).HasType support)
    (argument : AmbientBoundedGeneratedQueryReply base caps right commonLeft commonRight input
      (environmentCost rightEnvironment))
    (argumentData : WorldGeneratedQueryReplyData (P := P) rightControls rightWorld frontier argument)
    (sponsored : Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftWorld,
       originalCallWorld rightControls .expressionReindex right.node rightWorld])
    (smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftWorld,
        originalCallWorld rightControls .expressionReindex right.node rightWorld]) parent)
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent)
    {prototypeDomain prototypeBody : VExpr} {ambient result : Profile n}
    {rows : List (Key n × Profile n)} (key : Key n)
    (inputEq : key.input = input) (member : (key, result) ∈ rows)
    (anchor : key.anchor = expression.subst commonLeft)
    (parentRecipe : RichCodeRecipe env U registry target header.source headerLocals
      (header.raw.comp commonLeft) (.forallE header.A header.B) relevant
      (.pi prototypeDomain prototypeBody ambient rows) parentFootprint)
    (parentFrame : OriginalCaptureRealization header.graph env registry target headerLocals
      commonLeft commonRight parentAvailable)
    (parentResources : parentFootprint.Available parentAvailable)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat)
    (parentAnnotation : WorldCodeRecipeProvenance strata parentRecipe)
    (parentCalls : parentAnnotation.Calls
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    (parentBound : WithinAbove cutoff fuel
      (fun control => parentRecipe.stratifiedDepth (strata.headOrdinal registry) control))
    (destination : OriginalNestedDisplay U common
      (header.B.subst (header.raw.cons expression)) resultAssigned) :
    ∃ selected : WorldRecipeArgumentSelection (P := P) base caps right commonLeft commonRight
        rightControls rightWorld frontier input support,
    ∃ nextParent : RichCodeRecipe env U registry target header.source headerLocals
        (header.raw.comp commonRight) (.forallE header.A header.B) relevant
        (.pi prototypeDomain prototypeBody ambient
          (reanchorRows key (reanchorKey key (expression.subst commonRight)) rows)) parentFootprint,
    ∃ nextAnnotation : WorldCodeRecipeProvenance strata nextParent,
      nextAnnotation.worlds = parentAnnotation.worlds ∧
      (∀ policy, nextParent.headDepth policy = parentRecipe.headDepth policy) ∧
      TypeRelated env U registry target
        (destination.sourceExpression.subst (destination.raw.comp commonLeft))
        (destination.sourceExpression.subst (destination.raw.comp commonRight)) result ∧
      (∃ rightArgument : RichGradedResult right.sourceEnv env U registry target right.node selected.locals
          (right.raw.comp commonRight) selected.available input,
        Nonempty (ControlledStoredQuery rightControls frontier (.observation rightArgument.observation))) ∧
      (∃ nextFootprint, ∃ nextCertificate : RichCert left.sourceEnv env U registry target
          left.node.typeFormation.node leftLocals (left.raw.comp commonRight) true support nextFootprint,
        nextFootprint.Available leftAvailable ∧
        Nonempty (ControlledStoredQuery leftControls frontier (.certificate nextCertificate))) := by
  obtain ⟨selected, paired, raw, rightArgument, rightCertificate⟩ := transportRecipeArgument henv hscoped formed
    leftControls rightControls sameCutoff sameFuel leftWorld rightWorld frontier parent
    leftFrame leftData rightFrame rightData certificate resources certificateReady typed
    argument argumentData sponsored smaller bank unary
  obtain ⟨nextParent, nextAnnotation, worlds, depth, whole⟩ := parentAnnotation.rebuildWorld
    henv hscoped formed cutoff cutoffBound fuel constants callerSchedule parentCalls parentBound parentFrame.substitutions
    (parentFrame.frame.recipeResources henv hscoped formed parentResources)
  have paired' : Related env U registry target (expression.subst commonLeft) (expression.subst commonRight)
      (header.A.subst (header.raw.comp commonLeft)) key.input support := by
    simpa only [inputEq, subst_subst] using paired
  have raw' : env.IsDefEq U target (expression.subst commonLeft) (expression.subst commonRight)
      (header.A.subst (header.raw.comp commonLeft)) := by
    simpa only [subst_subst] using raw
  have output := TypeRelated.literalPiRowPairFromBinder henv hscoped formed
    (by simpa only [subst] using whole) member anchor raw' paired'
  have compose (commonMap : Subst) :
      (header.raw.comp commonMap).cons (expression.subst commonMap) =
        (header.raw.cons expression).comp commonMap := by
    funext index
    cases index <;> rfl
  have admission := TypeRelated.literalPiRightAdmissionFromBinder henv hscoped formed
    (by simpa only [subst] using whole) member anchor raw' paired'
  let unused : Atom n := match n with | 0 => true | _ + 1 => .sort true
  let change : AtomView env U registry target (n := n + 1)
      (.fn key unused) (.fn (reanchorKey key (expression.subst commonRight)) unused) := .reanchor admission
  let rebuilt : RichCodeRecipe env U registry target header.source headerLocals
      (header.raw.comp commonRight) (.forallE header.A header.B) relevant
      (.pi prototypeDomain prototypeBody ambient
        (reanchorRows key (reanchorKey key (expression.subst commonRight)) rows)) parentFootprint :=
    .action (.map change) nextParent
  refine ⟨selected, rebuilt, .action (.map change) nextAnnotation, ?_,
    (fun policy => ?_), ?_, rightArgument, rightCertificate⟩
  · exact worlds
  · simpa only [rebuilt, RichCodeRecipe.headDepth] using depth policy
  · simpa only [inst_lift_cons, compose, ← subst_subst, destination.realizedExpression] using output

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
