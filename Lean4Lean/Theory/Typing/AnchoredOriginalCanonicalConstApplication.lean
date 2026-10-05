import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstStep
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalBoundedGeneratedReply
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth
import Lean4Lean.Theory.Typing.AnchoredSortableApplicationCode

/-! The closed-function / external-argument application boundary. This
isolated query retains the caller's actual application children. Only its
closed function packet is masked by a canonical owner; the caller argument
keeps its own original source, footprint, and controls. No function-source
comparison joins the canonical environment to the caller environment. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open OriginalEndpointFactor EquationStratifiedFuel
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

structure CanonicalConstApplicationAt (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (strata : EquationStratification env)
    (function : EndpointRef sourceEnv U source (.const name levels) (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (key : Key n) (output : Atom n) (relevant : Bool) where
  functionQuery : CanonicalConstSitePacket env U registry target strata name levels (Profile.fn key output)
  argumentQuery : RichGradedResult sourceEnv env U registry target argument locals σ available key.input
  admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)
  sorted : (Profile.singleton output).HasType (.sort relevant)

namespace CanonicalConstApplicationAt
variable {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {strata : EquationStratification env} {source : List VExpr} {name : Name} {levels : List VLevel}
  {A B a : VExpr} {u v : VLevel}
  {function : EndpointRef sourceEnv U source (.const name levels) (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {locals : List Nat} {σ τ : Subst} {available : Valuation} {key : Key n} {output : Atom n} {relevant : Bool}

noncomputable def depth
    (query : CanonicalConstApplicationAt sourceEnv env U registry target strata
      function argument locals σ available key output relevant) : Nat → Nat :=
  fun control => max (query.functionQuery.chargeDepth control)
    (query.argumentQuery.observation.stratifiedDepth (strata.headOrdinal registry) control)

/-- This is the native destination application whose query is represented
by the finite composite; all formation children are original caller nodes. -/
def applicationNode
    (domain : EndpointState sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U) :
    EndpointState sourceEnv U source (.app (.const name levels) a) (B.inst a) :=
  .app hu hv domain codomain (.ref function) argument result

noncomputable def applicationSchedule
    (ordered : sourceEnv.Ordered)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U) (captured : List Closure) : Nat :=
  richSchedule .fundamental (Closure.close
    ((applicationNode (function := function) (argument := argument) domain codomain result hu hv).dependencyOrigin ordered)
    captured).cost

theorem argument_schedule
    (ordered : sourceEnv.Ordered)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U) (captured : List Closure) :
    richSchedule .fundamental (Closure.close (argument.dependencyOrigin ordered) captured).cost <
      applicationSchedule (function := function) (argument := argument) ordered domain codomain result hu hv captured := by
  unfold applicationSchedule applicationNode
  apply richSchedule_strict
  exact Nat.lt_of_lt_of_le (binder_other_cost (by simp) captured)
    (application_cost_le_captured (domain.dependencyOrigin ordered) (codomain.dependencyOrigin ordered)
      ((EndpointState.ref function).dependencyOrigin ordered) (argument.dependencyOrigin ordered)
      (result.dependencyOrigin ordered) captured)

/-- Both calls are actual lower original F calls: canonical function opening
and the caller's proper argument child. The returned syntax keeps the closed
function packet and the actual reconstructed argument query separately. -/
theorem step
    (query : CanonicalConstApplicationAt sourceEnv env U registry target strata
      function argument locals σ available key output relevant)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (primitive : function.Primitive)
    (context : ContextDerivation sourceEnv U source)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (sourceCutoff : strata.SourceCutoff sourceEnv cutoff)
    (bounded : WithinAbove cutoff fuel query.depth)
    (functionF : query.functionQuery.ComputationalBelow
      (EquationControlMeasure.key strata.rules.length cutoff fuel ordered.constantCount
        (applicationSchedule (function := function) (argument := argument) ordered domain codomain result hu hv
          (frame.dependencyEnvironment ordered))))
    (argumentF :
      WithinAbove cutoff fuel
        (fun control => query.argumentQuery.observation.stratifiedDepth (strata.headOrdinal registry) control) →
      strata.SourceCutoff sourceEnv cutoff →
      EquationControlMeasure.Less
        (EquationControlMeasure.key strata.rules.length cutoff fuel ordered.constantCount
          (richSchedule .fundamental
            (Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost))
        (EquationControlMeasure.key strata.rules.length cutoff fuel ordered.constantCount
          (applicationSchedule (function := function) (argument := argument) ordered domain codomain result hu hv
            (frame.dependencyEnvironment ordered))) →
      ∃ answer : RichComputationalValue sourceEnv env U registry target argument locals σ τ available
          query.argumentQuery.raw,
        WithinAbove cutoff fuel
          (fun control => answer.rightQuery.observation.stratifiedDepth (strata.headOrdinal registry) control)) :
    ∃ right : CanonicalConstApplicationAt sourceEnv env U registry target strata
        function argument locals τ available key output relevant,
      right.functionQuery = query.functionQuery ∧
      TypeRelated env U registry target ((VExpr.app (.const name levels) a).subst σ)
        ((VExpr.app (.const name levels) a).subst τ) (.singleton output) ∧
      WithinAbove cutoff fuel right.depth := by
  have functionBound : WithinAbove cutoff fuel query.functionQuery.chargeDepth :=
    fun control above => Nat.le_trans (Nat.le_max_left _ _) (bounded control above)
  have argumentBound : WithinAbove cutoff fuel
      (fun control => query.argumentQuery.observation.stratifiedDepth (strata.headOrdinal registry) control) :=
    fun control above => Nat.le_trans (Nat.le_max_right _ _) (bounded control above)
  obtain ⟨functionAnswer, functionReturn, _, _⟩ := query.functionQuery.primitiveStep henv below function primitive
    locals σ τ cutoff cutoffBound fuel ordered.constantCount
      (applicationSchedule (function := function) (argument := argument) ordered domain codomain result hu hv
        (frame.dependencyEnvironment ordered)) functionBound functionF
  obtain ⟨argumentAnswer, outputBound⟩ := argumentF argumentBound sourceCutoff
    (EquationControlMeasure.scheduleDecrease
      (argument_schedule (function := function) ordered domain codomain result hu hv (frame.dependencyEnvironment ordered))
      strata.rules.length cutoff fuel ordered.constantCount)
  have functionValue : Related env U registry target (.const name levels) (.const name levels)
      (.forallE (A.subst σ) (B.subst σ.lift)) (Profile.fn key output) functionAnswer.support := by
    simpa only [subst] using functionReturn.related
  obtain ⟨support, inputTyped, supportFormed, path, bridge⟩ :=
    functionValue.fn_domain_alignment henv hscoped formed
  have sourceCode := (bridge.symm henv inputTyped.wf_type).left_diagonal
  have keyCode := bridge.left_diagonal
  have high := query.argumentQuery.adapter.termMap henv hscoped formed
    (Profile.HasType.raise query.argumentQuery.bound inputTyped)
    (sourceCode.raise henv query.argumentQuery.bound) argumentAnswer.related
  have adapted : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) key.input support := by
    simpa only [lower_raised] using Related.lower henv query.argumentQuery.bound formed high
  have paired := Related.convert henv inputTyped (bridge.symm henv inputTyped.wf_type) adapted
  have pairedRaw := path.symm.cast
    ((argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions)
  obtain ⟨anchorRaw, _, _, _, _, _, anchor, _⟩ := query.admitted
  have anchor' := Related.retag henv inputTyped keyCode anchor
  have pairAdmission : Admitted env U registry target key (a.subst σ) (a.subst τ) :=
    ⟨anchorRaw, pairedRaw, support, inputTyped, supportFormed, keyCode, anchor', paired⟩
  have rightAnchor := Related.trans henv hscoped anchor' paired
  have rightSelf := (Related.symm henv rightAnchor).left_diagonal
  have rightAdmission : Admitted env U registry target key (a.subst τ) (a.subst τ) :=
    ⟨anchorRaw.trans pairedRaw, pairedRaw.hasType.2, support, inputTyped, supportFormed,
      keyCode, rightAnchor, rightSelf⟩
  let right : CanonicalConstApplicationAt sourceEnv env U registry target strata
      function argument locals τ available key output relevant := {
    functionQuery := query.functionQuery
    argumentQuery := argumentAnswer.rightQuery.adaptRequest henv hscoped formed
      query.argumentQuery.bound query.argumentQuery.adapter
    admitted := rightAdmission
    sorted := query.sorted }
  refine ⟨right, rfl, ?_, ?_⟩
  · simpa only [subst] using Related.applicationCode henv hscoped formed query.sorted functionValue pairAdmission
  · intro control above
    exact Nat.max_le.mpr ⟨functionBound control above, outputBound control above⟩

end CanonicalConstApplicationAt
end Lean4Lean.AnchoredSource.Adapted
