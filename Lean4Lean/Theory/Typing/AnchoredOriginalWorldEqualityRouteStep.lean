import Lean4Lean.Theory.Typing.AnchoredOriginalParameterEqualityData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterReply
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations

/-! Assemble a retained equality-route reply from its actual primitive equality
answer. The selected frame and all dormant history evidence remain unchanged;
code extraction preserves the supplied answer's concrete annotation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem AmbientBoundedParameterReply.equalityResultWorld
    {sourceEnv env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target common : List VExpr}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {commonLeft commonRight : Subst} {start : VExpr}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env} {P : VEnv → Prop}
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base commonCaps start
      (parameterEqualityDisplay graph original forward) commonLeft commonRight
      (profile : Profile n) (environmentCost baselineEnvironment))
    (answerData : WorldParameterReplyData (P := P) controls baseline frontier answer)
    (sorted : profile.HasType (.sort relevant))
    (changed : OriginalDirectionalEqualityResult original forward env registry target
      answer.reply.answer.reply.locals (raw.comp commonLeft) (raw.comp commonLeft)
      answer.reply.answer.reply.available profile)
    (changedReady : ControlledStoredQuery controls frontier (.observation changed.rightQuery.observation)) :
    ∃ result : AmbientBoundedParameterReply base commonCaps start
        (parameterEqualityDisplay graph original (!forward)) commonLeft commonRight profile
        (environmentCost baselineEnvironment),
      ∃ output : WorldParameterReplyData (P := P) controls baseline frontier result,
        result.reply.answer.reply.available = answer.reply.answer.reply.available ∧
        result.reply.answer.reply.locals = answer.reply.answer.reply.locals ∧
        output.generation.worlds = answerData.generation.worlds := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, certificate, ready, resources, _⟩ :=
    changed.rightQuery.code_controlled henv controls changedReady sorted
  let query : RichGradedResult sourceEnv env U registry target
      (.ref (parameterEqualitySide original (!forward))) prior.locals (raw.comp commonLeft)
      prior.available profile := {
    rank := n, bound := Nat.le_refl _, raw := profile
    footprint := footprint, observation := .code certificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := resources
    live := Profile.HasType.sortable_live sorted }
  let next : BoundedGeneratedQueryReply base commonCaps
      (parameterEqualityDisplay graph original (!forward)) commonLeft commonRight profile
      (environmentCost baselineEnvironment) := {
    answer := {
      reply := { prior with query := query }
      capped := answer.reply.answer.capped }
    bounded := answer.reply.bounded }
  have related : TypeRelated env U registry target
      (((if forward then A else B).subst raw).subst commonLeft)
      (((if !forward then A else B).subst raw).subst commonLeft) profile := by
    simpa only [subst_subst] using changed.related.code_of_sortable henv hscoped formed sorted
  have rawEquality := (original.forget.defeq.mono answer.ambient.below).substDF henv
    prior.realization.substitutions.left.wf formed prior.realization.substitutions.left
  have path : TypeConversion env U target
      (((if forward then A else B).subst raw).subst commonLeft)
      (((if !forward then A else B).subst raw).subst commonLeft) := by
    cases forward
    · simpa only [Bool.not_false, Bool.false_eq_true, reduceIte, subst_subst,
        parameterEqualityDisplay, OriginalCaptureMap.parameterCellDisplay] using
        (TypeConversion.single rawEquality.symm)
    · simpa only [Bool.not_true, Bool.false_eq_true, reduceIte, subst_subst,
        parameterEqualityDisplay, OriginalCaptureMap.parameterCellDisplay] using
        (TypeConversion.single rawEquality)
  let result : AmbientBoundedParameterReply base commonCaps start
      (parameterEqualityDisplay graph original (!forward)) commonLeft commonRight profile
      (environmentCost baselineEnvironment) := {
    toBoundedParameterReply := ⟨next, answer.related.trans henv related, answer.path.trans path⟩
    generation := answer.generation }
  let output : WorldParameterReplyData (P := P) controls baseline frontier result := {
    generation := answerData.generation
    hereditary := answerData.hereditary
    replayable := answerData.replayable
    controlled := answerData.controlled
    compatible := answerData.compatible
    query := ready.code
    covered := answerData.covered }
  exact ⟨result, output, rfl, rfl, rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
