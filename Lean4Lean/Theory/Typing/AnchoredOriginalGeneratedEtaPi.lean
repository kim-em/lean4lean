import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedEtaLift
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReanchor
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrameDiagonal
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePiShape

/-! Eta expansion reads its domain and body rows from the actual function
assigned formation, reindexed to the Pi formed by eta's original children. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private etaBody from Lean4Lean.Theory.Typing.AnchoredOriginalEndpoints
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option quotPrecheck false

/-- Intrinsic typing against actual Pi origins forces the usual normalized
function shape, even through arbitrary pads and code actions. -/
theorem RichPiProfileOrigins.value_shape
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {value : Profile n} {atom : Atom n}
    (origins : RichPiProfileOrigins env U registry target locals σ available domain body (profile : Profile n))
    (typed : value.HasType profile) (member : atom ∈ value.atoms) : NormalFunction atom := by
  induction n with
  | zero =>
    obtain ⟨cover, hm, _⟩ := typed atom member
    exact (origins cover hm).elim
  | succ n ih =>
    obtain ⟨cover, hm, ht⟩ := typed.2.2 atom member
    have origin := origins cover hm
    cases cover with
    | sort | fn | family | ctor | record => exact origin.elim
    | pi protoDomain protoBody domain rows =>
      cases atom with
      | sort | pi | pad | family | ctor | record => contradiction
      | fn key output => exact ⟨AdapterNormal.key key, AdapterNormal.atom output, rfl⟩
    | pad cover =>
      cases atom with
      | sort | fn | pi | family | ctor | record => contradiction
      | pad atom =>
        have smaller : RichPiProfileOrigins env U registry target locals σ available domain body (Profile.singleton cover) := by
          intro a hm
          cases List.mem_singleton.mp hm
          exact origin
        have shape := ih smaller ht (List.mem_singleton_self _)
        cases n with
        | zero => exact shape.elim
        | succ n =>
          obtain ⟨key, output, he⟩ := shape
          refine ⟨AdapterNormal.shiftKey key, AdapterNormal.shiftAtom output, ?_⟩
          rw [AdapterNormal.atom_pad, he]
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
local notation "etaBodyNode" => etaBody domainWF bodyWF codomain liftedCodomain liftedTerm liftedDomain
local notation "limit" => (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost
local notation "base" => frame.captureBase substitutions
local notation "piNode" => EndpointState.pi domainWF bodyWF (.ref (.left domain)) (.ref (.left codomain))
local notation "piLocation" => Located.assignedFormation (Located.expose (.here (root := .left original)))
local notation "sourceDisplay" => OriginalNestedDisplay.identity base (EndpointState.ref (.left term)).typeFormation.node (.ofLocation (.assignedFormation (.here (root := .left term))) context)
local notation "piDisplay" => OriginalNestedDisplay.identity base piNode (.ofLocation piLocation context)

/-- Source code transfer pays the two actual formation occurrences. The
Pi on the right is the original exposed eta lambda's assigned formation. -/
theorem eta_pi_formation_pair
    (captured : List Closure) :
    (Closure.close ((EndpointState.ref (.left term)).typeFormation.node.dependencyOrigin ordered) captured).cost +
      (Closure.close ((piNode).dependencyOrigin ordered) captured).cost <
      (Closure.close ((original).dependencyOrigin ordered) captured).cost := by
  have first := (EndpointState.ref (.left term)).typeFormation_dependency_cost_le ordered captured
  have second := (EndpointRef.left original).expose.typeFormation_dependency_cost_le ordered captured
  have scheduled := Derivation.eta_dependency_endpoint_schedule ordered domainWF bodyWF domain codomain
    liftedCodomain term liftedTerm liftedDomain captured
  simp only [schedule, Phase.code] at scheduled
  have leftOrigin : (EndpointRef.left original).expose.dependencyOrigin ordered =
      dependencyEtaLeftOrigin (domain.dependencyOrigin ordered) (codomain.dependencyOrigin ordered)
        (liftedCodomain.dependencyOrigin ordered) (liftedTerm.dependencyOrigin ordered)
        (liftedDomain.dependencyOrigin ordered) := by
    simp only [EndpointRef.expose, Derivation.expose, etaBody, EndpointState.dependencyOrigin_cast,
      EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, dependencyEtaLeftOrigin, dependencyEtaBodyOrigin]
  rw [leftOrigin] at second
  change (Closure.close ((piNode).dependencyOrigin ordered) captured).cost ≤ _ at second
  change (Closure.close ((EndpointState.ref (.left term)).typeFormation.node.dependencyOrigin ordered) captured).cost ≤
    (Closure.close (term.dependencyOrigin ordered) captured).cost at first
  omega

/-- Reconstruct the complete requested support at eta's actual Pi node.
Identity caps turn the selected reply into a query on the original table. -/
theorem generatedEtaPiCertificate
    (henv : env.Ordered) (closed : available.AtomClosed)
    (formationR : GeneratedObservationCall base ((base).initialCaps) sourceDisplay piDisplay
      σ τ ordered ordered (richSchedule .fundamental limit))
    (certificate : RichCert sourceEnv env U registry target (EndpointState.ref (.left term)).typeFormation.node
      locals σ true (support : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (RichCert sourceEnv env U registry target piNode locals σ true support required) ∧
      required.Available available := by
  have scheduled := richSchedule_strict
    (eta_pi_formation_pair domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain ordered
      (frame.dependencyEnvironment ordered)) RichPhase.expressionReindex RichPhase.fundamental
  obtain ⟨reply⟩ := formationR (base).identityRealization (base).identityCapped closed
    (base).identityRealization (base).identityCapped closed scheduled (.code certificate) resources
  exact reply.answer.freezeBase.code henv certificate.formed

include substitutions in
/-- All Pi row reanchoring calls remain the actual eta domain and codomain,
under the actual generic frame and its finite fresh binders. -/
theorem generatedEtaPiOrigins
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (domainF : OriginalCodeInductionAt env registry ordered context (.piDomain piLocation) limit)
    (bodyF : OriginalCodeInductionAt env registry ordered context (.piBody piLocation) limit)
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
    (fun row admitted => row.reanchorGeneric context henv below ordered (.left domain) (.piDomain piLocation)
      (.ref (.left codomain)) (.piBody piLocation) bodyContext domainF bodyF frame.leftDiagonal bound
      closed formed substitutions.left admitted) domainWF bodyWF (.done _) resources

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
