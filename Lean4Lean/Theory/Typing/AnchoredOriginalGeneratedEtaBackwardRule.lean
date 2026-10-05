import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedEtaExpansion
import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank

/-! Full reverse function eta at the original public endpoints. Arbitrary
rich queries are classified by the original assigned Pi support, rebuilt
atom-by-atom, and interpreted by the actual smaller exposed lambda F. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private etaBody from Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option quotPrecheck false

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
local notation "sourceDisplay" => OriginalNestedDisplay.identity base (EndpointState.ref (.left term)).typeFormation.node (.ofLocation (.assignedFormation (.here (root := .left term))) context)
local notation "piDisplay" => OriginalNestedDisplay.identity base piNode (.ofLocation piLocation context)

/-- Every premise below is a fixed original child F or an exact reserved
original comparison; all outgoing lambda guards and queries are produced. -/
theorem generatedEtaExpansion
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (leftF : OriginalComputationalInductionAt env registry ordered context
      (.expose (.here (root := .left original))) limit)
    (termF : OriginalComputationalInductionAt env registry ordered context (.here (root := .left term)) limit)
    (domainF : OriginalCodeInductionAt env registry ordered context (.piDomain piLocation) limit)
    (bodyF : OriginalCodeInductionAt env registry ordered context (.piBody piLocation) limit)
    (formationR : GeneratedObservationCall base ((base).initialCaps) sourceDisplay piDisplay
      σ τ ordered ordered (richSchedule .fundamental limit))
    (functionR : ∀ {k : Nat} (key : Key k),
      GeneratedObservationCall base ((base).initialCaps.push (Need.Fits key.input))
        unliftedDisplay (etaLiftedFunctionDisplay context domain liftedTerm)
        (σ.cons key.anchor) (τ.cons key.anchor) ordered ordered (richSchedule .fundamental limit))
    (query : RichObs sourceEnv env U registry target (.ref (.right original)) locals σ
      (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (OriginalDirectionalEqualityResult original false env registry target locals σ τ available profile) := by
  let sourceQuery := RichObs.changeReference (first := .right original) (second := .left term) rfl query
  have strict := eta_lifted_function_pair domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
    ordered (frame.dependencyEnvironment ordered)
  have termSmaller : (Closure.close (term.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit := by omega
  obtain ⟨answer⟩ := termF target locals σ τ available frame termSmaller closed formed substitutions sourceQuery resources
  obtain ⟨required, ⟨certificate⟩, typeResources⟩ := generatedEtaPiCertificate context domainWF bodyWF domain codomain
    liftedCodomain term liftedTerm liftedDomain frame substitutions ordered henv closed formationR answer.certificate answer.resources
  obtain ⟨expanded⟩ := OriginalSupportedEqualityResult.ofSingletons henv hscoped formed profile (fun atom member =>
    generatedEtaExpansionAtom context domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
      frame substitutions ordered henv hscoped below formed closed leftF domainF bodyF functionR
      (.select sourceQuery member) resources certificate typeResources (answer.typed.singleton_of_mem member)
      answer.typeCode (answer.related.singleton_of_mem member))
  let right : RichGradedResult sourceEnv env U registry target (.ref (.left original)) locals τ available profile :=
    { expanded.rightQuery with observation := RichObs.changeReference (first := .right (original).symm) (second := .left original) rfl expanded.rightQuery.observation }
  exact ⟨⟨expanded.support, expanded.related, right⟩⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
