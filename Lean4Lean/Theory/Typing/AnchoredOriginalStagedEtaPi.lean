import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedEtaPi
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameAmbientDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalSourcePredicatesDiagonal
import Lean4Lean.Theory.Typing.AnchoredOriginalStagedPiReanchor

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
local notation "etaBodyNode" => etaBody domainWF bodyWF codomain liftedCodomain liftedTerm liftedDomain
local notation "limit" => (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost
local notation "base" => frame.captureBase substitutions
local notation "piNode" => EndpointState.pi domainWF bodyWF (.ref (.left domain)) (.ref (.left codomain))
local notation "piLocation" => Located.assignedFormation (Located.expose (.here (root := .left original)))
local notation "sourceDisplay" => OriginalNestedDisplay.identity base (EndpointState.ref (.left term)).typeFormation.node (.ofLocation (.assignedFormation (.here (root := .left term))) context)
local notation "piDisplay" => OriginalNestedDisplay.identity base piNode (.ofLocation piLocation context)

/-- Reconstruct the complete requested support at eta's actual Pi node.
Identity caps turn the selected reply into a query on the original table. -/
theorem stagedEtaPiCertificate
    (henv : env.Ordered) (closed : available.AtomClosed)
    (ambient : frame.Ambient) (sources : frame.AllSources (SourceAtStage stage))
    (formationR : SourceGeneratedObservationCall (SourceAtStage stage) base ((base).initialCaps) sourceDisplay piDisplay
      σ τ ordered ordered stage stage (richSchedule .fundamental limit))
    (certificate : RichCert sourceEnv env U registry target (EndpointState.ref (.left term)).typeFormation.node
      locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (RichCert sourceEnv env U registry target piNode locals σ true support required) ∧
      required.Available available := by
  have scheduled := richSchedule_strict
    (eta_pi_formation_pair domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain ordered
      (frame.dependencyEnvironment ordered)) RichPhase.expressionReindex RichPhase.fundamental
  obtain ⟨reply⟩ := formationR (base).identityRealization (.identity ambient sources) closed
    (base).identityRealization (.identity ambient sources) closed (Prod.Lex.right stage scheduled) (.code certificate) resources
  exact reply.answer.freezeBase.code henv certificate.formed

include substitutions in
/-- All Pi row reanchoring calls remain the actual eta domain and codomain,
under the actual generic frame and its finite fresh binders. -/
theorem stagedEtaPiOrigins
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (ambient : frame.Ambient) (sources : frame.AllSources (SourceAtStage stage))
    (domainF : OriginalStagedCodeInductionAt env registry stage ordered context (.piDomain piLocation) limit)
    (bodyF : OriginalStagedCodeInductionAt env registry stage ordered context (.piBody piLocation) limit)
    (certificate : RichCert sourceEnv env U registry target piNode locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available) :
    RichPiProfileOrigins env U registry target locals σ available (.ref (.left domain)) (.ref (.left codomain)) support := by
  have bodyContext : (Located.piBody piLocation).contextDerivation context =
      .cons ((Located.piDomain piLocation).contextDerivation context) (.left domain) := by
    change ContextDerivation.cons context (Classical.choose (piLocation).originalDomains.1) = _
    exact congrArg (ContextDerivation.cons context)
      (EndpointState.ref.inj (Classical.choose_spec (piLocation).originalDomains.1).symm)
  have strict := eta_pi_formation_pair domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain ordered
    (frame.dependencyEnvironment ordered)
  have bound : (Closure.close (.binder (domain.dependencyOrigin ordered) [codomain.dependencyOrigin ordered] [])
      (frame.leftDiagonal.dependencyEnvironment ordered)).cost ≤ limit := by
    rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal]
    change (Closure.close ((piNode).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost ≤ limit
    omega
  exact certificate.piOriginsWith henv hscoped formed closed
    (fun row admitted => row.reanchorStaged context henv below ordered (.left domain) (.piDomain piLocation)
      (.ref (.left codomain)) (.piBody piLocation) bodyContext domainF bodyF frame.leftDiagonal (OriginalRichFrame.Ambient.leftDiagonal frame ambient) (OriginalRichFrame.AllSources.leftDiagonal frame sources) bound
      closed formed substitutions.left admitted) domainWF bodyWF (.done _) resources

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
