import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantValuePruning
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantApplicationInputs
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstSharedReturn
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeApplicationCompile
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstLevelBridge
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGradedApplication

/-! Actual rich constant application inputs retain the annotation selected
by pruning. The destination application carries that exact closed query and
the exact selected argument, with only the canonical opening site added. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem canonicalConstSiteOfFunctionAnnotated
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (node : EndpointState owner.selected.origin.source U source (.const name levels) assigned)
    (query : RichObs owner.selected.origin.source env U registry target node locals σ
      (Profile.fn key output) footprint)
    (annotation : WorldObsProvenance strata query) :
    ∃ packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output),
    ∃ next : WorldObsProvenance strata packet.query,
      packet.ownerName = ownerName ∧ HEq packet.owner owner ∧
      next.worlds ⊆ annotation.worlds ∧
      ∀ policy, packet.query.headDepth policy ≤ query.headDepth policy := by
  let head := constantPrefix node
  obtain ⟨closed⟩ := EndpointRef.closedPrimitiveConstant head.reference rfl head.primitive
  obtain ⟨moved, next, worlds, depth⟩ := annotation.pruneConstantFunction (.ref closed.site) [] σ
  let origin : CanonicalConstOrigin env U registry strata name levels := {
    ownerName := ownerName, owner := owner, info := closed.info, lookup := closed.lookup
    assignedLevels := closed.assignedLevels, assignedWF := closed.assignedWF
    levelsWF := closed.levelsWF, equivalent := closed.equivalent
    typeClosed := owner.selected.origin.ordered.closedC closed.lookup, site := closed.site }
  let packet := CanonicalConstSitePacket.ofOrigin (target := target) origin σ moved
    (fun _ _ member => nomatch member)
  exact ⟨packet, next, rfl, HEq.rfl, worlds, depth⟩

theorem nativeRichConstantApplicationInputsAnnotated {key : Key n} {output : Atom n}
    (owner : CanonicalCodeOwner env registry strata ownerName)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (function : EndpointState owner.selected.origin.source U source (.const name levels) (.forallE A B))
    (argument : EndpointState owner.selected.origin.source U source (.bvar 0) A)
    (fn : RichObs owner.selected.origin.source env U registry target function locals σ
      (Profile.fn key output) fnFootprint)
    (arg : RichObs owner.selected.origin.source env U registry target argument locals σ rawInput argFootprint)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (pack : BinderPack n packed (fnFootprint ++ argFootprint) outside)
    (covered : packed.atoms ⊆ outerInput.atoms)
    (closed : available.AtomClosed) (resources : outside.Available available)
    (annotation : WorldObsProvenance strata fn) :
    ∃ packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output),
    ∃ next : WorldObsProvenance strata packet.query,
    ∃ demand : RecipeVariableDemand env U registry target outerInput key.input,
      packet.ownerName = ownerName ∧ HEq packet.owner owner ∧
      next.worlds ⊆ annotation.worlds ∧
      ∀ policy, packet.query.headDepth policy ≤ fn.headDepth policy := by
  obtain ⟨packet, next, nameEq, ownerEq, worlds, depth⟩ :=
    canonicalConstSiteOfFunctionAnnotated owner function fn annotation
  obtain ⟨demand⟩ := arg.recipeVariableArgumentDemand henv hscoped formed adapter pack covered closed resources
  exact ⟨packet, next, demand, nameEq, ownerEq, worlds, depth⟩

namespace CanonicalConstSitePacket

/-- Compile both actual inputs into ordinary shared application code. No
annotation is attached to a separately chosen existential query. -/
theorem compileApplicationAnnotated
    (packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output))
    (annotation : WorldObsProvenance strata packet.query)
    (demand : RecipeVariableDemand env U registry target outerInput key.input)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source (.const name levels) (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (arg : RichGradedResult sourceEnv env U registry target argument locals σ available demand.input)
    (argAnnotation : WorldObsProvenance strata arg.observation)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (sorted : (Profile.singleton output).HasType (.sort relevant)) :
    ∃ certificate : RichCert sourceEnv env U registry target
        (.app hu hv domain body function argument result) locals σ relevant (.singleton output) arg.footprint,
    ∃ next : WorldCertProvenance strata certificate,
      arg.footprint.Available available ∧
      next.worlds = (packet.originalSite.worlds ++ annotation.worlds) ++ argAnnotation.worlds ∧
      ∀ policy, certificate.headDepth policy ≤
        max (policy packet.ownerName (packet.query.headDepth policy)) (arg.observation.headDepth policy) := by
  simpa only [List.nil_append, packet.observation_headDepth, packet.observationProvenance_worlds] using
    demand.compileApplicationAnnotated henv hscoped formed (domain := domain) (body := body) (result := result)
      hu hv (packet.observation function locals σ) (fun _ _ member => nomatch member)
      arg admitted sorted (packet.observationProvenance function locals σ annotation) argAnnotation

/-- Execute the genuine level equality, then consume its actual graded
function in the destination application. Its raw profile and adapter survive
until application factorization; no exact-function restoration is assumed. -/
theorem compileApplicationLevelsControlled
    (packet : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output))
    (equal : EqUpToLevels U (.const name levels) (.const name nextLevels))
    (annotation : WorldObsProvenance strata packet.query)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (EquationWorldClosureOrder.World strata.rules.length))
    (callerPaid : EquationWorldClosureOrder.Sponsored frontier
      [originalCallWorld controls .fundamental caller baseline])
    (sourceReady : P packet.owner.selected.origin.source)
    (sponsored : EquationWorldClosureOrder.Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel packet.chargeDepth)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source (.const name nextLevels) (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (arg : RichGradedResult sourceEnv env U registry target argument locals σ available rawInput)
    (argReady : ControlledStoredQuery controls frontier (.observation arg.observation))
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (sorted : (Profile.singleton output).HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target
        (.app hu hv domain body function argument result) locals σ relevant (.singleton output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available available := by
  obtain ⟨fn, ⟨fnReady⟩⟩ := packet.reindexFunctionLevelsWorld equal annotation formed caller controls
    baseline frontier callerPaid sourceReady sponsored bounded bank function locals σ available
  obtain ⟨footprint, certificate, ready, resources, _⟩ :=
    RichGradedResult.appCodeControlled henv hscoped formed closed domain body result hu hv fn arg arguments
      admitted sorted controls fnReady argReady
  exact ⟨footprint, certificate, ready, resources⟩

end CanonicalConstSitePacket
end Lean4Lean.AnchoredSource.Adapted
