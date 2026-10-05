import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplicationRows
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationStep

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The retained source capture also carries the actual rich binder frame.
Its source F environment records the declared domain; its reindex closure
additionally charges the original argument used by the finite replacements. -/
structure GenericApplicationCapture
    {context : ContextDerivation headerEnv U headerSource}
    (base : OriginalRichFrame headerEnv env U registry target context locals σ σ available)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (argument : EndpointState headerEnv U headerSource a A) (support : Profile n) where
  needs : List Need
  capture : RichApplicationCapture headerEnv env U registry target body argument locals σ available needs support
  frame : OriginalRichFrame headerEnv env U registry target (.cons context domain)
    (Locals.push locals) (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (available.push needs)
  substitutions : Ctx.SubstEq env U target (σ.cons (a.subst σ)) (σ.cons (a.subst σ)) (A :: headerSource)
  environment_eq : ∀ (hf : headerEnv.Ordered),
    frame.dependencyEnvironment hf =
      .bundle (.close (argument.dependencyOrigin hf) (base.dependencyEnvironment hf))
        (.close (domain.dependencyOrigin hf) (base.dependencyEnvironment hf)) ::
        base.dependencyEnvironment hf

/-- Actual original application row consumption. Both induction hypotheses
receive strict bounds at their real source frames. The captured-body/result
comparison receives the exact finite query and actual rich binder frame. -/
theorem OriginalRichFrame.applicationRowGeneric
    {root : EndpointRef headerEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation headerEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (headerFormed : headerEnv.Ordered) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    (body : EndpointState headerEnv U (A :: headerSource) B (.sort v))
    (function : EndpointState headerEnv U headerSource f (.forallE A B))
    (argument : EndpointState headerEnv U headerSource a A)
    (result : EndpointState headerEnv U headerSource (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (appLocation : Located root (.app hu hv (.ref domain) body function argument result))
    (frame : OriginalRichFrame headerEnv env U registry target
      (appLocation.contextDerivation initialContext) locals σ σ available)
    (substitutions : Ctx.SubstEq env U target σ σ headerSource)
    (row : RichPiRowCertificate env U registry target locals σ available true (.ref domain) body (key : Key n) outputSupport)
    (outputTyped : (Profile.singleton output).HasType outputSupport)
    (functionAnswer : RichBinderValue headerEnv env U registry target function locals σ σ available (Profile.fn key output))
    (argumentAnswer : RichBinderValue headerEnv env U registry target argument locals σ σ available rawInput)
    (argumentObservation : RichObs headerEnv env U registry target argument locals σ rawInput argumentFootprint)
    (argumentAvailable : argumentFootprint.Available available)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (domainF : OriginalCodeInductionAt env registry headerFormed initialContext (.appDomain appLocation)
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
        (frame.dependencyEnvironment headerFormed)).cost)
    (bodyF : ∀ needs, (available.push needs).AtomClosed →
      ∀ bodyFrame : OriginalRichFrame headerEnv env U registry target (.cons (appLocation.contextDerivation initialContext) domain)
        (Locals.push locals) (σ.cons key.anchor) (σ.cons (a.subst σ)) (available.push needs),
      richSchedule .fundamental
        (Closure.close (body.dependencyOrigin headerFormed)
          (bodyFrame.dependencyEnvironment headerFormed)).cost <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
          (frame.dependencyEnvironment headerFormed)).cost →
      Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons (a.subst σ)) (A :: headerSource) →
      RichCodeTransfer env U registry target body body (Locals.push locals) (Locals.push locals)
        (σ.cons key.anchor) (σ.cons (a.subst σ)) (available.push needs) (available.push needs))
    (resultR : ∀ {q : Profile n} (capture : GenericApplicationCapture frame domain body argument q),
      richSchedule .expressionReindex
        ((Closure.close (result.dependencyOrigin headerFormed)
          (frame.dependencyEnvironment headerFormed)).cost +
         (Closure.close (body.dependencyOrigin headerFormed)
           (capture.frame.dependencyEnvironment headerFormed)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
          (frame.dependencyEnvironment headerFormed)).cost →
      Nonempty (RichCodeTransferResult env U registry target body result locals
        (σ.cons (a.subst σ)) σ available true q)) :
    Nonempty (RichSupportedValue headerEnv env U registry target
      (.app hu hv (.ref domain) body function argument result) locals σ σ available (.singleton output)) := by
  let needs := row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n := fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member atom present => row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present)
  have domainBound : (Closure.close (domain.dependencyOrigin headerFormed)
      (frame.dependencyEnvironment headerFormed)).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
        (frame.dependencyEnvironment headerFormed)).cost :=
    Nat.lt_of_lt_of_le (binder_domain_cost _ [_] [_ , _, _] _)
      (application_cost_le_captured (domain.dependencyOrigin headerFormed) (body.dependencyOrigin headerFormed)
        (function.dependencyOrigin headerFormed) (argument.dependencyOrigin headerFormed)
        (result.dependencyOrigin headerFormed) (frame.dependencyEnvironment headerFormed))
  obtain ⟨domainAnswer⟩ := domainF target locals σ σ available frame domainBound closed formed substitutions
    row.domain row.domainAvailable
  have alignedAdmission := row.alignment.admission henv admitted
  obtain ⟨rawPair, rawArgument, _, _, _, _, pair, self⟩ := alignedAdmission
  let bodyFrame := OriginalRichFrame.capture frame domain initialContext argument (.appArgument appLocation) rfl
    argumentObservation argumentAvailable row.domain row.domainAvailable
    row.inputTyped (Related.retag henv row.inputTyped domainAnswer.related pair) needs bounded covered
  have bodySubstitutions : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons (a.subst σ)) (A :: headerSource) :=
    .cons substitutions (domain.sound.defeq.mono headerBelow) rawPair
  have bodyClosed : (available.push needs).AtomClosed := Valuation.push_atomized_closed closed row.bodyFootprint.localNeeds
  have bodyBound : richSchedule .fundamental
      (Closure.close (body.dependencyOrigin headerFormed)
        (bodyFrame.dependencyEnvironment headerFormed)).cost <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin headerFormed)
          (frame.dependencyEnvironment headerFormed)).cost := by
    apply richSchedule_strict
    exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _)
      (capturedApplication_comparison (domain.dependencyOrigin headerFormed) (body.dependencyOrigin headerFormed)
        (function.dependencyOrigin headerFormed) (argument.dependencyOrigin headerFormed)
        (result.dependencyOrigin headerFormed) (frame.dependencyEnvironment headerFormed))
  obtain ⟨bodyAnswer⟩ := bodyF needs bodyClosed bodyFrame bodyBound bodySubstitutions row.body
    (row.pack.available_atomized_localNeeds row.outsideAvailable)
  let argumentQuery : RichGradedResult headerEnv env U registry target argument locals σ available key.input :=
    ⟨n, Nat.le_refl n, rawInput, argumentFootprint, argumentObservation,
      by simpa only [raiseProfile_self] using arguments, argumentAvailable,
      argumentAnswer.related.live henv hscoped formed⟩
  obtain ⟨query⟩ := row.captureResult argumentQuery bodyAnswer
  let actualFrame := OriginalRichFrame.capture frame domain initialContext argument (.appArgument appLocation) rfl
    argumentObservation argumentAvailable row.domain row.domainAvailable
    row.inputTyped (Related.retag henv row.inputTyped domainAnswer.related self) needs bounded covered
  let capture : GenericApplicationCapture frame domain body argument outputSupport := {
    needs := needs, capture := query, frame := actualFrame
    substitutions := .cons substitutions (domain.sound.defeq.mono headerBelow) rawArgument
    environment_eq := fun _ => rfl }
  obtain ⟨answer⟩ := resultR capture
    (richSchedule_strict (capturedApplication_comparison _ _ _ _ _ _) _ _)
  have resultRode : TypeRelated env U registry target ((B.inst a).subst σ) ((B.inst a).subst σ) outputSupport :=
    TypeRelated.left_diagonal (TypeRelated.symm henv row.body.formed.wf_value answer.related)
  refine ⟨{
    support := outputSupport
    footprint := answer.footprint
    certificate := answer.certificate
    resources := answer.resources
    typed := outputTyped
    typeCode := resultRode
    related := ?_ }⟩
  simpa only [subst, subst_inst, inst_lift_cons] using Related.apply (B := B.subst σ.lift) henv hscoped formed outputTyped
    (by simpa only [subst_inst, inst_lift_cons] using resultRode)
    (by simpa only [subst] using functionAnswer.related) admitted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
