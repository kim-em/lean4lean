import Lean4Lean.Theory.Typing.AnchoredOriginalSourceBinderPeel
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorPlanResult

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1200000

/-- Close the actual selected body frame, including all merged branches.
Both plan footprints are packed from its actual finite head table; the
parent is computed by peeling that same frame. -/
theorem RichConstructorPlanResult.closeSelectedBinder
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {header : EndpointRef sourceEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {graph : OriginalCaptureMap (common := common) context raw}
    {displayed : A.subst raw = annotation}
    {key : Key n} {output : Atom n} {domainSupport : Profile n}
    (hu : u.WF U) (hv : v.WF U)
    (domainAt : signature.domains[arguments.length]? = some A)
    (location : Located header (.ref domain))
    (lineage : location.contextDerivation .nil = context)
    (childFrame : OriginalCaptureRealization (.bind graph domain annotation displayed)
      env registry target (Locals.push (List.range arguments.length))
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor) childAvailable)
    (generated : SourceCaptureGenerated P base (caps.push (Need.Fits key.input))
      (commonLeft.cons key.anchor) (commonRight.cons key.anchor)
      (.bind graph domain annotation displayed) childFrame.frame.raw)
    (domainCode : RichCert sourceEnv env U registry target (.ref domain)
      (List.range arguments.length) (raw.comp commonLeft) true domainSupport domainFootprint)
    (domainResources : domainFootprint.Available (fun index => childAvailable (index + 1)))
    (guard : LambdaGuard env U registry target (raw.comp commonLeft) A key domainSupport)
    (child : RichConstructorPlanResult env U registry target header name levels signature
      (.cons context domain) body ((raw.comp commonLeft).cons key.anchor)
      (arguments ++ [key.anchor]) childAvailable output) :
    ∃ parent : OriginalCaptureRealization graph env registry target
        (List.range arguments.length) commonLeft commonRight (fun index => childAvailable (index + 1)),
      SourceCaptureGenerated P base caps commonLeft commonRight graph parent.frame.raw ∧
      Nonempty (RichConstructorPlanResult env U registry target header name levels signature
        context (.pi hu hv (.ref domain) body) (raw.comp commonLeft) arguments
        (fun index => childAvailable (index + 1)) (n := n + 1) (.fn key output)) ∧
      ∀ ordered : sourceEnv.Ordered,
        (domain.dependencyOrigin ordered).weight *
          (1 + environmentCost (parent.frame.dependencyEnvironment ordered)) ≤
            environmentCost (childFrame.frame.dependencyEnvironment ordered) := by
  obtain ⟨parentLocals, parent, parentGenerated, positions, _, environment⟩ :=
    childFrame.peelSourceBinder generated
  have sameLocals : parentLocals = List.range arguments.length := by
    have same := congrArg (fun xs : List Nat => xs.tail.map Nat.pred) positions
    simpa [Locals.push, List.tail_cons, List.map_map, Function.comp_def,
      Nat.pred_succ, List.map_id_fun] using same
  subst parentLocals
  have headBound : ∀ need ∈ childAvailable 0, Need.Fits key.input need := by
    intro need member
    exact generated.capped.availableBound 0 need member
  have table : childAvailable = Valuation.push (childAvailable 0) (fun index => childAvailable (index + 1)) := by
    funext index
    cases index <;> rfl
  have child' : RichConstructorPlanResult env U registry target header name levels signature
      (.cons context domain) body ((raw.comp commonLeft).cons key.anchor)
      (arguments ++ [key.anchor])
      (Valuation.push (childAvailable 0) (fun index => childAvailable (index + 1))) output := by
    simpa only [← table] using child
  obtain ⟨answer⟩ := RichConstructorPlanResult.binder hu hv domainAt location lineage
    domainCode domainResources guard (childAvailable 0)
    (fun need member => (headBound need member).1)
    (fun need member => (headBound need member).2) child'
  exact ⟨parent, parentGenerated, ⟨answer⟩, environment⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
