import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationBody
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencySchedules

/-! Computational beta queries retain the actual instantiated and body
occurrences. The empty own-argument capture is constructed before recursive
replay selects any finite demands. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

section
variable
  (context : ContextDerivation sourceEnv U source)
  (domainWF : u.WF U) (bodyWF : v.WF U)
  (domain : Derivation sourceEnv U source A A (.sort u))
  (codomain : Derivation sourceEnv U (A :: source) B B (.sort v))
  (body : Derivation sourceEnv U (A :: source) e e B)
  (argument : Derivation sourceEnv U source a a A)
  (result : Derivation sourceEnv U source (B.inst a) (B.inst a) (.sort v))
  (instantiated : Derivation sourceEnv U source (e.inst a) (e.inst a) (B.inst a))
  (graph : OriginalCaptureMap (common := common) context raw)

noncomputable def betaInstantiatedDisplay :
    OriginalNestedDisplay U common ((e.inst a).subst raw) ((B.inst a).subst raw) :=
  OriginalNestedDisplay.ofOccurrence context (.here (root := .left instantiated)) graph

noncomputable def betaCapturedBodyDisplay :
    OriginalNestedDisplay U common ((e.inst a).subst raw) ((B.inst a).subst raw) where
  sourceEnv := sourceEnv
  source := A :: source
  sourceExpression := e
  sourceType := B
  context := .cons context (.left domain)
  node := .ref (.left body)
  provenance := .ofLocation .here (.cons context (.left domain))
  raw := raw.cons (a.subst raw)
  graph := .capture graph (.left domain) graph (.ref (.left argument)) (.ofLocation .here context)
  expression_eq := by rw [subst_inst, inst_lift_cons]
  type_eq := by rw [subst_inst, inst_lift_cons]

/-- No demand, argument F answer or source alignment is needed to create
this baseline. Both original argument and domain closures are charged. -/
theorem emptyBetaBodyFrame
    {base : OriginalCaptureBase env U registry target}
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph realized.frame.raw) :
    ∃ next : OriginalCaptureRealization
        (betaCapturedBodyDisplay context domain body argument graph).graph
        env registry target (Locals.push locals) commonLeft commonRight (available.push []),
      CappedCaptureGenerated base commonCaps commonLeft commonRight
        (betaCapturedBodyDisplay context domain body argument graph).graph next.frame.raw ∧
      ∀ ordered : sourceEnv.Ordered,
        next.frame.dependencyEnvironment ordered =
          Closure.bundle (.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered))
            (.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) ::
          realized.frame.dependencyEnvironment ordered := by
  let query : RichObs sourceEnv env U registry target (.ref (.left argument)) locals (raw.comp commonLeft)
      (.empty : Profile 0) [] := .legacy (.legacy .empty)
  let certificate : RichCert sourceEnv env U registry target (.ref (.left domain)) locals (raw.comp commonLeft)
      true (.empty : Profile 0) [] :=
    .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
  have resources : Footprint.Available [] available := fun _ _ h => nomatch h
  have typed : (.empty : Profile 0).HasType .empty := Profile.HasType.empty Profile.WF.empty
  have arguments : Related env U registry target (a.subst (raw.comp commonLeft))
      (a.subst (raw.comp commonRight)) (A.subst (raw.comp commonLeft)) (.empty : Profile 0) .empty :=
    Related.of_singletons (fun _ h => nomatch h)
  let frame := realized.frame.capture (.left domain) context (.ref (.left argument)) .here rfl
    query resources certificate resources typed arguments [] (fun _ h => nomatch h) (fun _ h => nomatch h)
  have nextCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (betaCapturedBodyDisplay context domain body argument graph).graph frame.raw :=
    .capture capped (.left domain) context (.ref (.left argument)) .here rfl query resources
      (Nat.le_refl _) (by rw [raiseProfile_self]; exact .refl _) certificate resources
      typed arguments [] (fun _ h => nomatch h) (fun _ h => nomatch h)
  have rawPair := (argument.forget.defeq.mono below).substDF henv realized.substitutions.wf formed realized.substitutions
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons (a.subst (raw.comp commonLeft)))
      ((raw.comp commonRight).cons (a.subst (raw.comp commonRight))) (A :: source) :=
    .cons realized.substitutions (domain.forget.defeq.mono below) rawPair
  obtain ⟨next, generated, environment⟩ := nextCapped.realize frame substitutions
  exact ⟨next, generated, environment⟩

/-- The recursive query is computational, so projections inside arbitrary
term demands remain in the actual body query rather than being erased. -/
theorem generatedBetaBody
    {base : OriginalCaptureBase env U registry target}
    (henv : env.Ordered) (below : sourceEnv ≤ env) (ordered : sourceEnv.Ordered)
    (formed : OnCtx target (env.IsType U))
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph realized.frame.raw)
    (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall base commonCaps
      (betaInstantiatedDisplay context instantiated graph)
      (betaCapturedBodyDisplay context domain body argument graph)
      commonLeft commonRight ordered ordered
      (richSchedule .fundamental
        (Closure.close ((Derivation.beta domainWF bodyWF domain codomain body argument result instantiated).dependencyOrigin ordered)
          (realized.frame.dependencyEnvironment ordered)).cost))
    (query : RichObs sourceEnv env U registry target (.ref (.left instantiated)) locals (raw.comp commonLeft)
      (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (betaCapturedBodyDisplay context domain body argument graph)
      commonLeft commonRight profile
      (environmentCost
        (Closure.bundle (.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered))
          (.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) ::
          realized.frame.dependencyEnvironment ordered))) := by
  obtain ⟨next, generated, environment⟩ := emptyBetaBodyFrame context domain body argument graph
    henv below formed realized capped
  have nextClosed : (available.push []).AtomClosed := by
    simpa only [List.flatMap_nil, List.nil_append] using Valuation.push_atomized_closed closed []
  have scheduled : richSchedule .expressionReindex
      ((Closure.close (instantiated.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)).cost +
       (Closure.close (body.dependencyOrigin ordered) (next.frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental
        (Closure.close ((Derivation.beta domainWF bodyWF domain codomain body argument result instantiated).dependencyOrigin ordered)
          (realized.frame.dependencyEnvironment ordered)).cost := by
    rw [environment ordered]
    have old := Derivation.beta_dependency_comparison_schedule ordered domainWF bodyWF domain codomain body
      argument result instantiated (realized.frame.dependencyEnvironment ordered)
    simp only [schedule, Phase.code, richSchedule, RichPhase.code] at *
    omega
  obtain ⟨answer⟩ := bodyR realized capped closed next generated nextClosed scheduled query resources
  rw [environment ordered] at answer
  exact ⟨answer⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
