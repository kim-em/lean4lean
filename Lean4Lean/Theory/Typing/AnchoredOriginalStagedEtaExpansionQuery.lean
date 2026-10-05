import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedEtaLift
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureRealization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedLambda
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedResourceClosure

/-! Reverse eta source reconstruction uses an actual generated comparison
between the original function and its retained lifted child. Fresh demands
are selected by that reply and packed under the incoming finite guard. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private etaBody from Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints
open private LambdaGuard.anchorRelated from Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
open private closeNeeds_fits from Lean4Lean.Theory.Typing.AnchoredOriginalCappedResourceClosure
open private anchor_live from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option quotPrecheck false

private def castGraded
    {node : EndpointState sourceEnv U source expression assigned}
    (he : expression = nextExpression) (ht : assigned = nextAssigned)
    (query : RichGradedResult sourceEnv env U registry target node locals σ available profile) :
    RichGradedResult sourceEnv env U registry target (node.cast he ht) locals σ available profile := by
  cases he; cases ht; exact query

section
variable
  {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {A B f : VExpr} {u v : VLevel}
  (context : ContextDerivation sourceEnv U source)
  (domainWF : u.WF U) (bodyWF : v.WF U)
  (domain : Derivation sourceEnv U source A A (.sort u))
  (codomain : Derivation sourceEnv U (A :: source) B B (.sort v))
  (liftedCodomain : Derivation sourceEnv U (A.lift :: A :: source)
    (B.liftN 1 1) (B.liftN 1 1) (.sort v))
  (term : Derivation sourceEnv U source f f (.forallE A B))
  (liftedTerm : Derivation sourceEnv U (A :: source) f.lift f.lift
    (.forallE A.lift (B.liftN 1 1)))
  (liftedDomain : Derivation sourceEnv U (A :: source) A.lift A.lift (.sort u))
  (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)
local notation "original" => Derivation.eta domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
local notation "body" => etaBody domainWF bodyWF codomain liftedCodomain liftedTerm liftedDomain
local notation "limit" => (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost
local notation "base" => frame.captureBase substitutions
local notation "unliftedDisplay" => (OriginalNestedDisplay.identity base (.ref (.left term)) (.ofLocation .here context)).weaken (Ctx.Lift'.skip (A := A) .refl)

/-- The returned source lambda contains the original eta application
children, including projected metadata inside its function query. No source
renaming or synthesized original derivation is used. -/
theorem stagedEtaExpansionQuery
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (ambientSources : frame.Ambient) (sources : frame.AllSources (SourceAtStage stage))
    {key : Key n} {output : Atom n} {ambient : Profile n}
    (domainCode : RichCert sourceEnv env U registry target (.ref (.left domain)) locals σ true ambient domainFootprint)
    (domainResources : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A key ambient)
    (functionR : SourceGeneratedObservationCall (SourceAtStage stage) base ((base).initialCaps.push (Need.Fits key.input))
      unliftedDisplay (etaLiftedFunctionDisplay context domain liftedTerm)
      (σ.cons key.anchor) (τ.cons key.anchor) ordered ordered stage stage (richSchedule .fundamental limit))
    (query : RichObs sourceEnv env U registry target (.ref (.left term)) locals σ
      (Profile.fn key output) footprint)
    (resources : footprint.Available available) :
    Nonempty (RichGradedResult sourceEnv env U registry target (EndpointRef.left original).expose
      locals σ available (Profile.fn key output)) := by
  obtain ⟨sourceFrame, sourceCapped, sourceEnvironment⟩ := (base).identityRealization.weakenSource
    (.identity ambientSources sources) (show Ctx.Lift' (.skip .refl) source (A :: source) from .skip .refl)
    (nextLeft := σ.cons key.anchor) (nextRight := τ.cons key.anchor)
    (nextCaps := (base).initialCaps.push (Need.Fits key.input)) rfl rfl rfl
  obtain ⟨targetFrame, targetCapped, targetEnvironment⟩ := (base).identityRealization.bindSource
    (.identity ambientSources sources) (.left domain) A subst_id below domainCode domainResources guard.inputTyped
    (LambdaGuard.anchorRelated henv guard) (guard.path.cast guard.anchor.1) []
    (fun _ h => nomatch h) (fun _ h => nomatch h)
  have scheduled : richSchedule .expressionReindex
      ((Closure.close ((unliftedDisplay).node.dependencyOrigin ordered)
          (sourceFrame.frame.dependencyEnvironment ordered)).cost +
       (Closure.close ((etaLiftedFunctionDisplay context domain liftedTerm).node.dependencyOrigin ordered)
          (targetFrame.frame.dependencyEnvironment ordered)).cost) < richSchedule .fundamental limit := by
    rw [sourceEnvironment, targetEnvironment]
    apply richSchedule_strict
    have strict := eta_lifted_function_pair domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
      ordered (frame.dependencyEnvironment ordered)
    change (Closure.close (term.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
      (Closure.close (liftedTerm.dependencyOrigin ordered)
        (.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered) :: frame.dependencyEnvironment ordered)).cost < limit
    omega
  have targetClosed : (available.push []).AtomClosed := Valuation.push_atomized_closed closed []
  have sourceSubst : Subst.comp (Subst.id.lift_r (.skip .refl)) (σ.cons key.anchor) = σ := by
    funext i
    simp only [Subst.comp, Subst.lift_r, Subst.id, lift', Lift.liftVar, subst, Subst.cons]
  obtain ⟨reply⟩ := functionR sourceFrame sourceCapped closed targetFrame targetCapped targetClosed (Prod.Lex.right stage scheduled)
    (by simpa only [OriginalNestedDisplay.identity, OriginalNestedDisplay.weaken, OriginalRichFrame.captureBase, sourceSubst] using query)
    resources
  have caps := reply.answer.capped.availableBound
  have headCaps : ∀ need ∈ reply.answer.reply.available 0, Need.Fits key.input need := by
    exact caps 0
  have tailCaps : ∀ i need, need ∈ reply.answer.reply.available (i+1) → need ∈ available i := by
    exact fun i => caps (i+1)
  let requestedNeed : Need := ⟨n, key.input⟩
  let originals := reply.answer.reply.available 0 ++ [requestedNeed]
  have originalCaps : ∀ need ∈ originals, Need.Fits key.input need := by
    intro need member
    rcases List.mem_append.mp member with old | new
    · exact headCaps need old
    · cases List.mem_singleton.mp new
      exact ⟨Nat.le_refl _, by simp only [requestedNeed, Need.atGrade, dif_pos (Nat.le_refl n), raiseProfile_self]; exact fun _ h => h⟩
  let needs := originals ++ originals.flatMap Need.singletons
  have needCaps : ∀ need ∈ needs, Need.Fits key.input need :=
    closeNeeds_fits key.input originals (fun need member => (originalCaps need member).1)
      (fun need member => (originalCaps need member).2)
  have bodyClosed : (available.push needs).AtomClosed := Valuation.push_atomized_closed closed originals
  have included : ∀ i need, need ∈ reply.answer.reply.available i → need ∈ (available.push needs) i := by
    intro i need member
    cases i with
    | zero => exact List.mem_append_left _ (List.mem_append_left _ member)
    | succ i => exact tailCaps i need member
  have localsEq : reply.answer.reply.locals = Locals.push locals := reply.answer.reply.locals_eq
  have targetSubst : Subst.comp Subst.id.lift (σ.cons key.anchor) = σ.cons key.anchor := by rw [id_lift]; rfl
  let functionQuery : RichGradedResult sourceEnv env U registry target (.ref (.left liftedTerm))
      (Locals.push locals) (σ.cons key.anchor) (available.push needs) (Profile.fn key output) := by
    simpa only [etaLiftedFunctionDisplay, OriginalRichFrame.captureBase, localsEq, targetSubst] using
      reply.answer.reply.query.availableMono included
  let argumentNode := EndpointState.bvar (.zero : Lookup (A :: source) 0 A.lift) domainWF (.ref (.left liftedDomain))
  let argumentQuery : RichGradedResult sourceEnv env U registry target argumentNode
      (Locals.push locals) (σ.cons key.anchor) (available.push needs) key.input := {
    rank := n
    bound := Nat.le_refl _
    raw := key.input
    footprint := [(0, requestedNeed)]
    observation := .legacy (.legacy (.var _ _ 0 key.input))
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := by
      intro i need member
      cases List.mem_singleton.mp member
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    live := anchor_live henv hscoped formed guard.anchor }
  obtain ⟨application⟩ := RichGradedResult.app henv hscoped formed bodyClosed
    (.ref (.left liftedDomain)) (.ref (.left liftedCodomain))
    (.cast (inst_liftN_bvar B 0).symm rfl (.ref (.left codomain))) domainWF bodyWF
    functionQuery argumentQuery (.refl _) guard.anchor
  let bodyQuery := castGraded rfl (inst_liftN_bvar B 0) application
  exact RichGradedResult.lam henv hscoped formed closed (.ref (.left codomain)) domainWF bodyWF
    domainCode domainResources guard needs (fun need member => (needCaps need member).1)
    (fun need member _ present => (needCaps need member).2 _ present) bodyQuery bodyClosed

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
