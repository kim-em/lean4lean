import Lean4Lean.Theory.Typing.AnchoredOriginalSourceConstructorBinder
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedConstructorTerminalReindex

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1200000

private theorem lift_comp_anchor (raw common : Subst) (anchor : VExpr) :
    raw.lift.comp (common.cons anchor) = (raw.comp common).cons anchor := by
  funext index
  cases index <;> simp [Subst.comp, Subst.lift, Subst.cons]

/-- One genuine selected-frame constructor binder: the terminal code comes
from actual earlier-stage R, its old field captures survive the merge, and
its chosen body frame is peeled to construct the original destination Pi.
No completed body plan or semantic terminal answer is supplied. -/
theorem StagedOriginalLowerCallBank.constructorBinderTerminalReindex
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {header : EndpointRef sourceEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) signature.result (.sort v)}
    {graph : OriginalCaptureMap (common := common) context raw}
    {displayed : A.subst raw = annotation}
    {key : Key (n + 1)} {domainSupport : Profile (n + 1)}
    {family : FamilyData (Profile n)} {keys : List (DataRequest (Profile n))}
    (henv : env.Ordered)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (lower : callStage < stage)
    (ordered : sourceEnv.Ordered)
    (hu : u.WF U) (hv : v.WF U)
    (domainAt : signature.domains[arguments.length]? = some A)
    (location : Located header (.ref domain))
    (lineage : location.contextDerivation .nil = context)
    (bodyLocation : Located header body)
    (bodyLineage : bodyLocation.contextDerivation .nil = .cons context domain)
    (saturated : (arguments ++ [key.anchor]).length = signature.domains.length)
    (resultShape : signature.result = mkApps (.const family.name familyLevels) familyArguments)
    (relevant : family.relevant = true)
    (childFrame : OriginalCaptureRealization (.bind graph domain annotation displayed)
      env registry target (Locals.push (List.range arguments.length))
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) childAvailable)
    (generated : SourceCaptureGenerated (SourceAtStage callStage) base (caps.push (Need.Fits key.input))
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor)
      (.bind graph domain annotation displayed) childFrame.frame.raw)
    (closed : childAvailable.AtomClosed)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain)
      (List.range arguments.length) (raw.comp commonLeft) true domainSupport domainFootprint)
    (domainResources : domainFootprint.Available (fun index => childAvailable (index + 1)))
    (guard : LambdaGuard env U registry target (raw.comp commonLeft) A key domainSupport)
    (captures : FamilyCaptures env U registry target (A :: source)
      (List.range (arguments ++ [key.anchor]).length) ((raw.comp commonLeft).cons key.anchor)
      (constantCaptureVariables (arguments ++ [key.anchor]).length) keys captureFootprint)
    (captureResources : captureFootprint.Available childAvailable)
    (leftDisplay : OriginalNestedDisplay U (annotation :: common)
      (signature.result.subst raw.lift) leftAssigned)
    (leftOrdered : leftDisplay.sourceEnv.Ordered)
    (leftFrame : OriginalCaptureRealization leftDisplay.graph env registry target
      leftLocals (commonLeft.cons key.anchor) (commonRight.cons key.anchor) leftAvailable)
    (leftGenerated : SourceCaptureGenerated (SourceAtStage callStage) base (caps.push (Need.Fits key.input))
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) leftDisplay.graph leftFrame.frame.raw)
    (leftClosed : leftAvailable.AtomClosed)
    (leftCode : RichCert leftDisplay.sourceEnv env U registry target leftDisplay.node leftLocals
      (leftDisplay.raw.comp (commonLeft.cons key.anchor)) true
      (Profile.singleton (n := n + 1) (.family family)) leftFootprint)
    (leftResources : leftFootprint.Available leftAvailable) :
    ∃ available, ∃ parent : OriginalCaptureRealization graph env registry target
        (List.range arguments.length) commonLeft commonRight available,
      SourceCaptureGenerated (SourceAtStage callStage) base caps commonLeft commonRight graph parent.frame.raw ∧
      Nonempty (RichConstructorPlanResult env U registry target header name levels signature
        context (.pi hu hv (.ref domain) body) (raw.comp commonLeft) arguments available
        (n := n + 2) (.fn key (.ctor ⟨name, levels, keys, family, relevant⟩))) ∧
      (domain.dependencyOrigin ordered).weight *
        (1 + environmentCost (parent.frame.dependencyEnvironment ordered)) ≤
          environmentCost (childFrame.frame.dependencyEnvironment ordered) := by
  let rightDisplay : OriginalNestedDisplay U (annotation :: common)
      (signature.result.subst raw.lift) (.sort v) := {
    sourceEnv := sourceEnv, source := A :: source, sourceExpression := signature.result
    sourceType := .sort v, context := .cons context domain, node := body
    provenance := ⟨_, _, _, header, .nil, bodyLocation, bodyLineage.symm⟩
    raw := raw.lift, graph := .bind graph domain annotation displayed
    expression_eq := rfl, type_eq := rfl }
  obtain ⟨answer⟩ := bank.constructorTerminalReindex henv lower leftOrdered ordered
    leftFrame leftGenerated leftClosed (rightDisplay := rightDisplay)
    childFrame generated closed leftCode leftResources
  have resultCode : RichCert sourceEnv env U registry target body
      (List.range (arguments ++ [key.anchor]).length) ((raw.comp commonLeft).cons key.anchor)
      true (Profile.singleton (n := n + 1) (.family family)) answer.footprint := by
    simpa only [List.length_append, List.length_singleton, List.range_succ_eq_map,
      Locals.push, rightDisplay, lift_comp_anchor] using answer.certificate
  let terminal := RichConstructorPlanResult.terminal (name := name) (levels := levels) saturated resultShape relevant
    bodyLocation bodyLineage captures resultCode
    (answer.captureResources captureResources) answer.resources
  have domainAvailable : domainFootprint.Available (fun index => answer.nextAvailable (index + 1)) :=
    fun index need member => answer.included (index + 1) need (domainResources index need member)
  obtain ⟨parent, parentGenerated, result, domainBound⟩ := terminal.closeSelectedBinder hu hv
    domainAt location lineage answer.nextFrame answer.generation domainCode domainAvailable guard
  exact ⟨_, parent, parentGenerated, result, Nat.le_trans (domainBound ordered) answer.bounded⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
