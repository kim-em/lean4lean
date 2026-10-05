import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedVariableSource
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientVariableSource
import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The complete variable computational step uses the ordinary generated R
motive, even when its context-domain occurrence lives in a proper suffix.
Both recursive calls use retained original nodes and computed frame costs. -/
theorem OriginalRichFrame.variableComputationalAmbient
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation sourceEnv U rootSource)
    {level : VLevel}
    (lookup : Lookup source index sourceType) (levelWF : level.WF U)
    (formation : EndpointState sourceEnv U source sourceType (.sort level))
    (location : Located root (.bvar lookup levelWF formation))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initialContext) locals left right available)
    (substitutions : Ctx.SubstEq env U target left right source)
    (ambient : frame.Ambient)
    (bank : OriginalLowerCallBank env U registry limit)
    (scheduled : richSchedule .fundamental
      (Closure.close ((EndpointState.bvar lookup levelWF formation).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost ≤ limit)
    (query : RichObs sourceEnv env U registry target (.bvar lookup levelWF formation)
      locals left profile footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available) :
    Nonempty (RichComputationalValue sourceEnv env U registry target
      (.bvar lookup levelWF formation) locals left right available profile) := by
  apply frame.variableComputationalFull initialContext lookup levelWF formation location henv hscoped formed ordered
    (fun demand entry tailClosed fullAvailable positions _ _ _ => ?_) query closed resources
  obtain ⟨suffix, suffixGenerated, ⟨certificate⟩, sourceResources, sourceClosed, sourceSubstitutions, sourceBound⟩ :=
    entry.generatedSourceAmbient ambient substitutions closed positions
  let base := frame.captureBase substitutions
  let sourceFrame : OriginalCaptureRealization suffix.graph env registry target suffix.locals left right
      (fun i => available (i + (entry.originalLocation.prefix.length + 1))) :=
    ⟨suffix.frame, sourceSubstitutions⟩
  have pairBound :
      (Closure.close (entry.originalDomain.dependencyOrigin ordered)
        (suffix.frame.dependencyEnvironment ordered)).cost +
      (Closure.close (formation.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((EndpointState.bvar lookup levelWF formation).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost := by
    have bound := sourceBound ordered
    simp only [EndpointState.dependencyOrigin, Closure.cost, Origin.weight,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.add_mul, Nat.one_mul] at *
    omega
  obtain ⟨reply⟩ := bank.observation base base.initialCaps
    (suffix.variableDomainDisplay entry substitutions)
    (OriginalNestedDisplay.identity base formation
      ⟨_, _, _, root, initialContext, .assignedFormation location, rfl⟩)
    left right ordered ordered sourceFrame suffixGenerated sourceClosed
    base.identityRealization (.identity ambient) closed
    (Nat.lt_of_lt_of_le (richSchedule_strict pairBound _ _) scheduled) (.code certificate) sourceResources
  obtain ⟨fp, ⟨destination⟩, destinationResources⟩ := reply.answer.freezeBase.code henv certificate.formed
  have sourceSmaller :
      (Closure.close (entry.originalDomain.dependencyOrigin ordered)
        (suffix.frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((EndpointState.bvar lookup levelWF formation).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost := by omega
  obtain ⟨value⟩ := bank.computational ordered ambient.below entry.tailContext
    (Located.here (root := entry.originalDomain)) target suffix.locals
    (suffix.raw.comp left) (suffix.raw.comp right) _ suffix.frame suffixGenerated.ambient.2
    (Nat.lt_of_lt_of_le (richSchedule_strict sourceSmaller _ _) scheduled)
    sourceClosed formed sourceSubstitutions (.code certificate) sourceResources
  obtain ⟨semantics⟩ := value.code henv hscoped formed certificate.formed
  have length : entry.originalLocation.prefix.length = index := by
    rw [entry.originalFront_eq, ← entry.index_eq]
  have leftEq : entry.tailLeft = suffix.raw.comp left := by
    rw [← entry.left_eq, suffix.raw_eq]
    funext i
    simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.comp, Subst.id, length, Nat.add_assoc]
  exact ⟨⟨fp, destination, destinationResources, by
    have code := semantics.related.left_diagonal
    rw [← leftEq, entry.realizedType] at code
    simpa only [entry.realizedType] using code⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
