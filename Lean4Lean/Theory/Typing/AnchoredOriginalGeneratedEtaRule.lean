import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedEtaContraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichLambdaEqualityReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank

/-! Original eta contraction for every finite rich query. The only semantic
premises are fixed smaller original lambda/function F calls and the actual
lifted-to-original expression comparison beneath the incoming guard. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private etaBody from Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
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
local notation "destination" => (OriginalNestedDisplay.identity base (.ref (.left term)) (.ofLocation .here context)).weaken (Ctx.Lift'.skip (A := A) .refl)

/-- All incoming wrappers are consumed structurally. The returned observer
is rooted at the right endpoint of the SAME original eta derivation. -/
theorem generatedEtaContraction
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (leftF : OriginalComputationalInductionAt env registry ordered context
      (.expose (.here (root := .left original))) limit)
    (liftedF : OriginalComputationalInductionAt env registry ordered (.cons context (.left domain))
      (.here (root := .left liftedTerm)) limit)
    (termF : OriginalComputationalInductionAt env registry ordered context (.here (root := .left term)) limit)
    (functionR : ∀ {k : Nat} (key : Key k),
      GeneratedObservationCall base ((base).initialCaps.push (Need.Fits key.input))
        (etaLiftedFunctionDisplay context domain liftedTerm) destination
        (σ.cons key.anchor) (τ.cons key.anchor) ordered ordered (richSchedule .fundamental limit))
    (query : RichObs sourceEnv env U registry target (.ref (.left original)) locals σ
      (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    Nonempty (OriginalDirectionalEqualityResult original true env registry target locals σ τ available profile) := by
  have primitive : ∀ {k : Nat} {ambient : Profile k} {key : Key k} {output : Atom k}
      {domainFootprint bodyFootprint outside : Footprint} {packed : Profile k},
      RichCert sourceEnv env U registry target (.ref (.left domain)) locals σ true ambient domainFootprint →
      LambdaGuard env U registry target σ A key ambient →
      RichObs sourceEnv env U registry target body (Locals.push locals) (σ.cons key.anchor)
        (.singleton output) bodyFootprint →
      BinderPack k packed bodyFootprint outside →
      (∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) →
      domainFootprint.Available available → outside.Available available →
      Nonempty (OriginalSupportedEqualityResult original env registry target locals σ τ available (Profile.fn key output)) := by
    intro k ambient key output domainFootprint bodyFootprint outside packed domainCode guard observation pack covered domainAvailable outsideAvailable
    exact generatedEtaNativeContraction context domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
      frame substitutions ordered henv hscoped below formed closed leftF liftedF termF (functionR key)
      domainCode guard observation pack covered domainAvailable outsideAvailable
  obtain ⟨answer⟩ := query.replayEqualityLambda henv hscoped formed primitive domainWF bodyWF
    (.expose (.left original) (.done _)) resources
  exact ⟨⟨answer.support, answer.related, answer.rightQuery⟩⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
