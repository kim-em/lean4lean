import Lean4Lean.Theory.Typing.AnchoredOriginalRichEtaFactor
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedCaptureRealization
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedNativePiReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencySchedules

/-! Eta contraction replays its actual lifted-function query back to the
retained unlifted function. The fresh common binder is capped by the incoming
lambda guard; weakening the destination and freezing the returned base keep
all selected resources in the original caller frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private LambdaGuard.anchorRelated from Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReindex
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option Elab.async false
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

local notation "original" => Derivation.eta domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain

noncomputable def etaLiftedFunctionDisplay :
    OriginalNestedDisplay U (A :: source) (f.lift' (.skip .refl)) (.forallE A.lift (B.liftN 1 1)) where
  sourceEnv := sourceEnv
  source := A :: source
  sourceExpression := f.lift
  sourceType := .forallE A.lift (B.liftN 1 1)
  context := .cons context (.left domain)
  node := .ref (.left liftedTerm)
  provenance := .ofLocation .here (.cons context (.left domain))
  raw := Subst.id.lift
  graph := .bind (.identity context) (.left domain) A subst_id
  expression_eq := by rw [id_lift, subst_id]; exact lift_eq_lift'.symm
  type_eq := by rw [id_lift, subst_id]

/-- Both ends are actual original eta children. The left closure includes
its real domain binder and is charged by the exposed eta lambda. -/
theorem eta_lifted_function_pair
    (ordered : sourceEnv.Ordered) (captured : List Closure) :
    (Closure.close (liftedTerm.dependencyOrigin ordered)
      (.close (domain.dependencyOrigin ordered) captured :: captured)).cost +
      (Closure.close (term.dependencyOrigin ordered) captured).cost <
      (Closure.close ((original).dependencyOrigin ordered) captured).cost := by
  let bodyOrigin := dependencyEtaBodyOrigin (codomain.dependencyOrigin ordered)
    (liftedCodomain.dependencyOrigin ordered) (liftedTerm.dependencyOrigin ordered)
    (liftedDomain.dependencyOrigin ordered)
  have functionLess : (Closure.close (liftedTerm.dependencyOrigin ordered)
      (.close (domain.dependencyOrigin ordered) captured :: captured)).cost <
      (Closure.close bodyOrigin (.close (domain.dependencyOrigin ordered) captured :: captured)).cost := by
    apply Nat.lt_of_lt_of_le (binder_other_cost (domain := liftedDomain.dependencyOrigin ordered)
      (bodies := [liftedCodomain.dependencyOrigin ordered])
      (children := [liftedTerm.dependencyOrigin ordered, .rule [liftedDomain.dependencyOrigin ordered], codomain.dependencyOrigin ordered])
      (by simp) _)
    exact application_cost_le_captured _ _ _ _ _ _
  have bodyLess := binder_body_cost (domain := domain.dependencyOrigin ordered)
    (bodies := [codomain.dependencyOrigin ordered, bodyOrigin]) (children := [])
    (body := bodyOrigin) (by simp) captured
  have pair := original_two_children (term.dependencyOrigin ordered)
    (dependencyEtaLeftOrigin (domain.dependencyOrigin ordered) (codomain.dependencyOrigin ordered)
      (liftedCodomain.dependencyOrigin ordered) (liftedTerm.dependencyOrigin ordered)
      (liftedDomain.dependencyOrigin ordered)) [] captured
  rw [Derivation.dependencyOrigin.eq_def ordered (Derivation.eta domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain)]
  dsimp only
  change _ < (Closure.close (.rule [term.dependencyOrigin ordered,
    .binder (domain.dependencyOrigin ordered) [codomain.dependencyOrigin ordered, bodyOrigin] []]) captured).cost
  change _ < (Closure.close (.binder (domain.dependencyOrigin ordered)
    [codomain.dependencyOrigin ordered, bodyOrigin] []) captured).cost at bodyLess
  change (Closure.close (term.dependencyOrigin ordered) captured).cost +
    (Closure.close (.binder (domain.dependencyOrigin ordered)
      [codomain.dependencyOrigin ordered, bodyOrigin] []) captured).cost <
      (Closure.close (.rule [term.dependencyOrigin ordered,
        .binder (domain.dependencyOrigin ordered) [codomain.dependencyOrigin ordered, bodyOrigin] []]) captured).cost at pair
  omega

variable
  (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)
local notation "base" => frame.captureBase substitutions
local notation "destination" => (OriginalNestedDisplay.identity base (.ref (.left term)) (.ofLocation .here context)).weaken (Ctx.Lift'.skip (A := A) .refl)
local notation "limit" => (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost

/-- A whole rich query, not merely a reflected target value, returns to the
actual unlifted child using one strictly smaller original R call. -/
theorem generatedEtaUnlift
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed)
    {key : Key n}
    (domainCode : RichCert sourceEnv env U registry target (.ref (.left domain)) locals σ
      true (ambient : Profile n) domainFootprint)
    (domainResources : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A key ambient)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
    (bodyClosed : (available.push needs).AtomClosed)
    (functionR : GeneratedObservationCall base ((base).initialCaps.push (Need.Fits key.input))
      (etaLiftedFunctionDisplay context domain liftedTerm) destination
      (σ.cons key.anchor) (τ.cons key.anchor) ordered ordered (richSchedule .fundamental limit))
    (query : RichObs sourceEnv env U registry target (.ref (.left liftedTerm)) (Locals.push locals)
      (σ.cons key.anchor) (profile : Profile k) footprint)
    (resources : footprint.Available (available.push needs)) :
    Nonempty (RichGradedResult sourceEnv env U registry target (.ref (.left term))
      locals σ available profile) := by
  obtain ⟨sourceFrame, sourceCapped, sourceEnvironment⟩ := (base).identityRealization.bindCapped
    (base).identityCapped (.left domain) A subst_id below domainCode domainResources guard.inputTyped
    (LambdaGuard.anchorRelated henv guard) (guard.path.cast guard.anchor.1) needs bounded covered
  obtain ⟨rightFrame, rightCapped, rightEnvironment⟩ := (base).identityRealization.weakenCapped
    (base).identityCapped (show Ctx.Lift' (.skip .refl) source (A :: source) from .skip .refl)
    (nextLeft := σ.cons key.anchor) (nextRight := τ.cons key.anchor)
    (nextCaps := (base).initialCaps.push (Need.Fits key.input)) rfl rfl rfl
  have scheduled : richSchedule .expressionReindex
      ((Closure.close ((etaLiftedFunctionDisplay context domain liftedTerm).node.dependencyOrigin ordered)
          (sourceFrame.frame.dependencyEnvironment ordered)).cost +
       (Closure.close ((destination).node.dependencyOrigin ordered)
          (rightFrame.frame.dependencyEnvironment ordered)).cost) < richSchedule .fundamental limit := by
    rw [sourceEnvironment, rightEnvironment]
    exact richSchedule_strict
      (eta_lifted_function_pair domainWF bodyWF domain codomain liftedCodomain term liftedTerm liftedDomain
        ordered (frame.dependencyEnvironment ordered)) _ _
  have sameRealization : Subst.comp Subst.id.lift (σ.cons key.anchor) = σ.cons key.anchor := by
    rw [id_lift]; rfl
  obtain ⟨reply⟩ := functionR sourceFrame sourceCapped bodyClosed rightFrame rightCapped closed scheduled
    (by simpa only [etaLiftedFunctionDisplay, sameRealization, OriginalRichFrame.captureBase] using query) resources
  obtain ⟨returned⟩ := reply.answer.unweaken
    (show Ctx.Lift' (.skip .refl) source (A :: source) from .skip .refl) rfl rfl rfl
  exact ⟨returned.freezeBase⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
