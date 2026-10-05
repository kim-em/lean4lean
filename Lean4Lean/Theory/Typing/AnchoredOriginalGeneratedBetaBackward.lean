import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBetaApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalEqualityGradedReplay
import Lean4Lean.Theory.Typing.AnchoredBeta

/-! Backward beta pairs the original instantiated child F with computed
rich lambda/application reconstruction. The finite argument calls remain
actual selected occurrences, all strictly below the original beta rule. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option quotPrecheck false

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
  (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)

local notation "original" => Derivation.beta domainWF bodyWF domain codomain body argument result instantiated
local notation "bodyDisplay" => betaCapturedBodyDisplay context domain body argument (.identity context)
local notation "capacity" => environmentCost (Closure.bundle (.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) (.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) :: frame.dependencyEnvironment ordered)
local notation "limit" => (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost

/-- An actual instantiated F answer is expanded without changing its
requested support or any original assigned-type evidence. -/
theorem RichComputationalValue.betaBackward
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall (frame.captureBase substitutions) ((frame.captureBase substitutions)).initialCaps
      (betaInstantiatedDisplay context instantiated (.identity context)) bodyDisplay
      σ τ ordered ordered (richSchedule .fundamental limit))
    (domainF : OriginalCodeInductionAt env registry ordered context (.here (root := .left domain)) limit)
    (leftF : OriginalComputationalInductionAt env registry ordered context
      (.expose (.here (root := .left original))) limit)
    (query : RichObs sourceEnv env U registry target (.ref (.left instantiated)) locals σ
      (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (answer : RichComputationalValue sourceEnv env U registry target (.ref (.left instantiated))
      locals σ τ available profile) :
    ∃ ledgers : List (Σ needs, CapturedArgumentQueries (frame.captureBase substitutions) ((frame.captureBase substitutions)).initialCaps source σ τ a capacity needs),
      (∀ entry ∈ ledgers,
        entry.2.Calls (OriginalNestedDisplay.identity (frame.captureBase substitutions) (.ref (.left argument)) (.ofLocation .here context))
          ordered (richSchedule .fundamental limit)) →
      Nonempty (OriginalEqualityQueryResult (original).symm env registry target locals σ τ available profile) := by
  obtain ⟨ledgers, reconstruct⟩ := generatedBetaExpansion context domainWF bodyWF domain codomain body argument result instantiated
    frame substitutions ordered henv hscoped below formed closed bodyR domainF query resources
  refine ⟨ledgers, ?_⟩
  intro calls
  obtain ⟨expanded⟩ := reconstruct calls
  have leftSmaller : (Closure.close ((EndpointRef.left original).expose.dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost < limit := by
    rw [Derivation.dependencyOrigin.eq_def ordered (Derivation.beta domainWF bodyWF domain codomain body argument result instantiated)]
    exact original_child_same_environment (Origin.rule_child (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact Or.inr rfl)) _
  obtain ⟨leftAnswer⟩ := leftF target locals σ τ available frame leftSmaller closed formed substitutions
    expanded.observation expanded.resources
  let requested := leftAnswer.rightQuery.adaptRequest henv hscoped formed expanded.bound expanded.adapter
  have rawBody := body.forget.defeq.mono below
  have rawArgument := argument.forget.defeq.mono below
  have beta := IsDefEq.beta rawBody rawArgument
  have typePair := (result.forget.defeq.mono below).substDF henv substitutions.wf formed substitutions
  have rightBeta := IsDefEq.defeqDF typePair.symm
    (beta.subst henv (substitutions.right henv formed) formed)
  have leftTyped := beta.hasType.2.subst henv substitutions.left formed
  have step : HeadBeta ((VExpr.app (.lam A e) a).subst τ) ((e.inst a).subst τ) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, subst_inst] using
      (HeadBeta.contract (A := A.subst τ) (body := e.subst τ.lift) (argument := a.subst τ) (trailing := []))
  have related := Related.headBeta henv .refl step leftTyped rightBeta answer.related
  let reference := EndpointRef.right (original).symm
  have exposed : reference.expose = (EndpointRef.left original).expose := rfl
  let restored : RichGradedResult sourceEnv env U registry target (.ref reference) locals τ available profile :=
    { requested with observation := .route (.expose reference (.done _)) requested.observation }
  exact ⟨⟨answer.support, related, restored⟩⟩

/-- The source answer above is produced by the actual strictly smaller
instantiated original child, not supplied as a completed equality result. -/
theorem generatedBetaBackward
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall (frame.captureBase substitutions) ((frame.captureBase substitutions)).initialCaps
      (betaInstantiatedDisplay context instantiated (.identity context)) bodyDisplay
      σ τ ordered ordered (richSchedule .fundamental limit))
    (domainF : OriginalCodeInductionAt env registry ordered context (.here (root := .left domain)) limit)
    (leftF : OriginalComputationalInductionAt env registry ordered context
      (.expose (.here (root := .left original))) limit)
    (instantiatedF : OriginalComputationalInductionAt env registry ordered context (.here (root := .left instantiated))
      (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost)
    (query : RichObs sourceEnv env U registry target (.ref (.left instantiated)) locals σ
      (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ ledgers : List (Σ needs, CapturedArgumentQueries (frame.captureBase substitutions) ((frame.captureBase substitutions)).initialCaps source σ τ a capacity needs),
      (∀ entry ∈ ledgers,
        entry.2.Calls (OriginalNestedDisplay.identity (frame.captureBase substitutions) (.ref (.left argument)) (.ofLocation .here context))
          ordered (richSchedule .fundamental limit)) →
      Nonempty (OriginalEqualityQueryResult (original).symm env registry target locals σ τ available profile) := by
  have smaller : (Closure.close (instantiated.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost := by
    have pair := Derivation.beta_dependency_comparison_schedule ordered domainWF bodyWF domain codomain body argument result instantiated
      (frame.dependencyEnvironment ordered)
    simp only [schedule, Phase.code] at pair
    omega
  obtain ⟨answer⟩ := instantiatedF target locals σ τ available frame smaller closed formed substitutions query resources
  exact answer.betaBackward context domainWF bodyWF domain codomain body argument result instantiated
    frame substitutions ordered henv hscoped below formed closed bodyR domainF leftF query resources

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
