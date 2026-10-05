import Lean4Lean.Theory.Typing.AnchoredOriginalWorldNativeApplicationAdmission
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGradedApplication

/-! The two actual native-row child answers construct ordinary application
code. This consumer never calls F on the whole body or extracts a purported
physical application from a newly returned recipe. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem NativeApplicationAdmissionResult.compileCodeControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {function : EndpointState sourceEnv U (D :: source) f (.forallE A B)}
    {argument : EndpointState sourceEnv U (D :: source) (.bvar 0) A}
    (answer : NativeApplicationAdmissionResult (registry := registry) (target := target)
      (function := function) (argument := argument) controls frontier locals σ oldAnchor newAnchor
      available needs key output rawInput)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : (Valuation.push needs available).AtomClosed)
    (domain : EndpointState sourceEnv U (D :: source) A (.sort u))
    (body : EndpointState sourceEnv U (A :: D :: source) B (.sort v))
    (resultNode : EndpointState sourceEnv U (D :: source) (B.inst (.bvar 0)) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (sorted : (Profile.singleton output).HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target
      (.app hu hv domain body function argument resultNode) (Locals.push locals) (σ.cons newAnchor)
      relevant (.singleton output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available (Valuation.push needs available) ∧
      ready.annotation.worlds ⊆ answer.functionQuery.annotation.worlds ++ answer.argumentQuery.annotation.worlds ∧
      TypeRelated env U registry target ((.app f (.bvar 0) : VExpr).subst (σ.cons oldAnchor))
        ((.app f (.bvar 0) : VExpr).subst (σ.cons newAnchor)) (.singleton output) := by
  obtain ⟨footprint, certificate, ready, resources, worlds⟩ :=
    RichGradedResult.appCodeControlled henv hscoped formed closed domain body resultNode hu hv
      answer.functionValue.rightQuery answer.argumentValue.rightQuery arguments
      (by simpa only [subst, Subst.cons] using answer.admitted) sorted controls
      answer.functionQuery answer.argumentQuery
  exact ⟨footprint, certificate, ready, resources, worlds,
    answer.applicationCode henv hscoped formed sorted⟩

/-- Return to the original sorted row endpoint through its actual conversion
prefix. The structural application need not itself have a literal sort as its
assigned type. -/
theorem NativeApplicationAdmissionResult.compileRowCodeControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {function : EndpointState sourceEnv U (D :: source) f (.forallE A B)}
    {argument : EndpointState sourceEnv U (D :: source) (.bvar 0) A}
    (answer : NativeApplicationAdmissionResult (registry := registry) (target := target)
      (function := function) (argument := argument) controls frontier locals σ oldAnchor newAnchor
      available needs key output rawInput)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : (Valuation.push needs available).AtomClosed)
    (domain : EndpointState sourceEnv U (D :: source) A (.sort u))
    (body : EndpointState sourceEnv U (A :: D :: source) B (.sort v))
    (resultNode : EndpointState sourceEnv U (D :: source) (B.inst (.bvar 0)) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (piBody : EndpointState sourceEnv U (D :: source) (.app f (.bvar 0)) (.sort resultLevel))
    (bodyRoute : PrefixRoute sourceEnv U (D :: source) (.app f (.bvar 0)) piBody
      (.app hu hv domain body function argument resultNode))
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (sorted : (Profile.singleton output).HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target piBody
      (Locals.push locals) (σ.cons newAnchor) relevant (.singleton output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available (Valuation.push needs available) ∧
      ready.annotation.worlds ⊆ answer.functionQuery.annotation.worlds ++ answer.argumentQuery.annotation.worlds ∧
      TypeRelated env U registry target ((.app f (.bvar 0) : VExpr).subst (σ.cons oldAnchor))
        ((.app f (.bvar 0) : VExpr).subst (σ.cons newAnchor)) (.singleton output) := by
  obtain ⟨footprint, certificate, ready, resources, worlds, related⟩ :=
    answer.compileCodeControlled henv hscoped formed closed domain body resultNode hu hv arguments sorted
  let annotation : WorldCertProvenance strata (.route bodyRoute certificate) :=
    .route bodyRoute ready.annotation
  have same : annotation.worlds = WorldCertProvenance.worlds ready.annotation := rfl
  let next : ControlledStoredQuery controls frontier (.certificate (.route bodyRoute certificate)) := {
    annotation := annotation
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using ready.within control active
    sponsored := ready.sponsored }
  refine ⟨footprint, .route bodyRoute certificate, next, resources, ?_, related⟩
  change annotation.worlds ⊆ _
  rw [same]
  exact worlds

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
