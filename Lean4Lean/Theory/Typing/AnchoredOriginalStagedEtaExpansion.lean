import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedEtaExpansion
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedEtaPi
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedEtaExpansionQuery
import Lean4Lean.Theory.Typing.AnchoredOriginalSupportedEquality
import Lean4Lean.Theory.Typing.AnchoredOriginalRichReferenceExposure
import Lean4Lean.Theory.Typing.AnchoredEtaAnnotation

/-! Reverse eta reconstructs each actually requested function atom from its
retained Pi row, then interprets the rebuilt lambda with its smaller original
F. Neither an outgoing source query nor eta semantics is supplied. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private etaBody from Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option quotPrecheck false

private theorem eta_subst (A f : VExpr) (σ : Subst) :
    (VExpr.lam A (.app f.lift (.bvar 0))).subst σ =
      .lam (A.subst σ) (.app (f.subst σ).lift (.bvar 0)) := by
  show VExpr.lam (A.subst σ) (.app (f.lift.subst σ.lift) ((VExpr.bvar 0).subst σ.lift)) = _
  rw [lift_subst_lift]
  rfl

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

local notation "piNode" => EndpointState.pi domainWF bodyWF (.ref (.left domain)) (.ref (.left codomain))
local notation "piLocation" => Located.assignedFormation (Located.expose (.here (root := .left original)))

/-- The function atom, its domain certificate, and its guard are all selected
from the actual incoming query and its computed original Pi certificate. -/
theorem stagedEtaExpansionAtom
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (ambient : frame.Ambient) (sources : frame.AllSources (SourceAtStage stage))
    (leftF : OriginalStagedComputationalInductionAt env registry stage ordered context
      (.expose (.here (root := .left original))) limit)
    (domainF : OriginalStagedCodeInductionAt env registry stage ordered context (.piDomain piLocation) limit)
    (bodyF : OriginalStagedCodeInductionAt env registry stage ordered context (.piBody piLocation) limit)
    (functionR : ∀ {k : Nat} (key : Key k),
      SourceGeneratedObservationCall (SourceAtStage stage) base ((base).initialCaps.push (Need.Fits key.input))
        unliftedDisplay (etaLiftedFunctionDisplay context domain liftedTerm)
        (σ.cons key.anchor) (τ.cons key.anchor) ordered ordered stage stage (richSchedule .fundamental limit))
    {atom : Atom n} {support : Profile n}
    (query : RichObs sourceEnv env U registry target (.ref (.left term)) locals σ (.singleton atom) footprint)
    (resources : footprint.Available available)
    (certificate : RichCert sourceEnv env U registry target piNode locals σ true support typeFootprint)
    (typeResources : typeFootprint.Available available)
    (typed : (Profile.singleton atom).HasType support)
    (code : TypeRelated env U registry target ((VExpr.forallE A B).subst σ) ((VExpr.forallE A B).subst σ) support)
    (related : Related env U registry target (f.subst σ) (f.subst τ) ((VExpr.forallE A B).subst σ)
      (.singleton atom) support) :
    Nonempty (OriginalSupportedEqualityResult (original).symm env registry target locals σ τ available (.singleton atom)) := by
  have origins := stagedEtaPiOrigins context domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
    frame substitutions ordered henv hscoped below formed closed ambient sources domainF bodyF certificate typeResources
  have shape := origins.value_shape typed (List.mem_singleton_self _)
  cases n with
  | zero => exact shape.elim
  | succ n =>
    obtain ⟨key, output, normalEq⟩ := shape
    let normal : AtomView env U registry target atom (n := n+1) (.fn key output) :=
      normalEq ▸ AdapterNormal.view henv atom
    let normalQuery := RichObs.view query normal
    let normalCode := RichCert.map normal certificate
    have normalTyped := normal.mapType_typed typed
    have normalOrigins := stagedEtaPiOrigins context domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
      frame substitutions ordered henv hscoped below formed closed ambient sources domainF bodyF normalCode typeResources
    obtain ⟨protoDomain, protoBody, domainSupport, rows, result, member, _, _, _, rowMember, resultTyped⟩ :=
      normalTyped.fn_inv (List.mem_singleton_self _)
    obtain ⟨row⟩ := normalCode.piRowOfOrigins normalOrigins member rowMember
    have piBound := eta_pi_formation_pair domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain ordered
      (frame.dependencyEnvironment ordered)
    have domainBound : (Closure.close (domain.dependencyOrigin ordered)
        (frame.leftDiagonal.dependencyEnvironment ordered)).cost < limit := by
      rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal]
      have child := binder_domain_cost (domain.dependencyOrigin ordered) [codomain.dependencyOrigin ordered] []
        (frame.dependencyEnvironment ordered)
      change (Closure.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost <
        (Closure.close ((piNode).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost at child
      omega
    obtain ⟨domainAnswer⟩ := domainF target locals σ σ available frame.leftDiagonal (OriginalRichFrame.Ambient.leftDiagonal frame ambient)
      (OriginalRichFrame.AllSources.leftDiagonal frame sources) domainBound closed formed substitutions.left
      row.domain row.domainAvailable
    let newKey : Key n := ⟨A.subst σ, key.anchor, key.input⟩
    have guard : LambdaGuard env U registry target σ A newKey row.domainSupport := {
      inputTyped := row.inputTyped
      formed := row.domain.formed
      path := .refl
      domains := domainAnswer.related
      anchor := row.alignment.admission henv row.anchor }
    let changing : AtomView env U registry target (n := n+1) (.fn key output) (.fn newKey output) :=
      row.alignment.view key.anchor output
    let whole : AtomView env U registry target atom (n := n+1) (.fn newKey output) := .trans normal changing
    obtain ⟨expanded⟩ := stagedEtaExpansionQuery context domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
      frame substitutions ordered henv hscoped below formed closed ambient sources row.domain row.domainAvailable guard (functionR newKey)
      (.view normalQuery changing) resources
    obtain ⟨requested⟩ := expanded.action henv hscoped formed (.view (whole.inverse henv))
    have leftSmaller : (Closure.close ((EndpointRef.left original).expose.dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost < limit := by
      rw [Derivation.dependencyOrigin.eq_def ordered (Derivation.eta domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain)]
      apply original_child_same_environment
      apply Origin.rule_child
      simp only [EndpointRef.expose, Derivation.expose, etaBody, EndpointState.dependencyOrigin_cast,
        EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, dependencyEtaLeftOrigin, dependencyEtaBodyOrigin,
        List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr trivial
    obtain ⟨lambdaAnswer⟩ := leftF target locals σ τ available frame ambient sources leftSmaller closed formed substitutions
      requested.observation requested.resources
    let right := lambdaAnswer.rightQuery.adaptRequest henv hscoped formed requested.bound requested.adapter
    let restored : RichGradedResult sourceEnv env U registry target (.ref (.right (original).symm)) locals τ available (.singleton atom) :=
      { right with observation := .route (.expose (.right (original).symm) (.done _)) right.observation }
    have rawTerm := (term.forget.defeq.mono below).substDF henv substitutions.wf formed substitutions
    have typePair := ((original).typeFormation.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
    have rawEta := IsDefEq.defeqDF typePair.symm
      (((original).forget.defeq.mono below).subst henv (substitutions.right henv formed) formed)
    change env.IsDefEq U target ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ) (f.subst τ)
      ((VExpr.forallE A B).subst σ) at rawEta
    rw [eta_subst] at rawEta
    have mapped := whole.termMap henv hscoped formed related
    have backward := Related.etaExpandAt henv rawEta rawTerm.hasType.1 (Related.symm henv mapped)
    have restoredRelated := (whole.inverse henv).termMap henv hscoped formed (Related.symm henv backward)
    have final := Related.retag henv typed code restoredRelated
    refine ⟨{ support := support, related := ?_, rightQuery := restored, typed := typed, typeCode := code }⟩
    change Related env U registry target (f.subst σ)
      ((VExpr.lam A (.app f.lift (.bvar 0))).subst τ) ((VExpr.forallE A B).subst σ) (.singleton atom) support
    rw [eta_subst]
    exact final

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
