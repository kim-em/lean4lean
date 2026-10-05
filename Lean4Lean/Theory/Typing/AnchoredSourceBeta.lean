import Lean4Lean.Theory.Typing.AnchoredSourceArgument
import Lean4Lean.Theory.Typing.AnchoredSourceSubstitution
import Lean4Lean.Theory.Typing.AnchoredBeta

/-! The direct source beta row, assembled from the original domain, argument,
body, and codomain children. The finite singleton closure of the input
valuation is explicit; no protected-resource equivalence is asserted. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure BetaRowResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst) (available : Valuation)
    (A B body argument : VExpr) (key : Key n) (output : Atom n)
    (domainSupport : Profile n) (domainFootprint : Footprint) where
  argumentSupport : ArgumentAtDomain env U registry target locals realization realization
    available argument A key.input domainSupport domainFootprint
  transfer : TransferResult env U registry target locals realization realization
    (Valuation.atomize available) (.app (.lam A body) argument) (body.inst argument)
    (B.inst argument) (.singleton output)

/-- At a finite singleton-closed valuation, the beta result uses exactly
that same available valuation. This is only membership closure: it asserts
no equality or reversible view between the old and new local footprints. -/
def BetaRowResult.atClosed
    (result : BetaRowResult env U registry target locals realization available
      A B body argument key output domainSupport domainFootprint)
    (closed : available.AtomClosed) :
    TransferResult env U registry target locals realization realization available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output) :=
  { result.transfer with
    resultAvailable := result.transfer.resultAvailable.of_atomize closed
    typeAvailable := result.transfer.typeAvailable.of_atomize closed }

/-- Contract a directly observed lambda application. Every semantic source
call below is one of the original beta-rule children. The codomain child is
needed because the body's returned certificate initially lives at the anchor.
The instantiated observation and certificate use the actual argument instead.
-/
theorem Obs.beta_row
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {support : Profile n}
    {domainFootprint bodyFootprint outside argumentFootprint : Footprint}
    (originalDomain : Joint env U registry source A A (.sort domainLevel))
    (originalArgument : Joint env U registry source argument argument A)
    (originalBody : Joint env U registry (A :: source) body body B)
    (originalCodomain : Joint env U registry (A :: source) B B (.sort bodyLevel))
    (formedA : env.HasType U source A (.sort domainLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target realization realization source)
    (fits : Fits env U registry source target locals realization realization available)
    (domain : CodeCert env U registry target locals realization A support domainFootprint)
    (guard : LambdaGuard env U registry target realization A key support)
    (bodyObservation : Obs env U registry target (Locals.push locals)
      (realization.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n key.input bodyFootprint outside)
    (argumentObservation : Obs env U registry target locals realization argument
      key.input argumentFootprint)
    (admitted : Admitted env U registry target key
      (argument.subst realization) (argument.subst realization))
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (BetaRowResult env U registry target locals realization available
      A B body argument key output support domainFootprint) := by
  obtain ⟨argumentResult⟩ := argumentAtDomain henv hscoped originalArgument originalDomain
    hTarget substitutions fits argumentObservation argumentAvailable domain domainAvailable
    guard.inputTyped
  obtain ⟨rawAnchor, _, _, _, _, _, anchorArgument, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains anchorArgument
  have paired : Ctx.SubstEq env U target (realization.cons key.anchor)
      (realization.cons (argument.subst realization)) (A :: source) :=
    .cons substitutions formedA (guard.path.cast rawAnchor)
  have localFits := fits.push henv hTarget domain domainAvailable guard.inputTyped arguments
    (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm => (pack.atomized_localNeeds need hm).2)
  obtain ⟨bodyResult⟩ :=
    (originalBody target (Locals.push locals) (realization.cons key.anchor)
      (realization.cons (argument.subst realization))
      (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available) hTarget paired localFits).1
      bodyObservation (pack.available_atomized_localNeeds outsideAvailable)
  obtain ⟨bodyPacked, bodyOutside, bodyPack, bodyCovered, bodyOutsideAvailable⟩ :=
    Footprint.pack_available bodyResult.resultAvailable
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm => (pack.atomized_localNeeds need hm).2)
  obtain ⟨valueFootprint, ⟨valueObservation⟩, valueSelected⟩ :=
    bodyResult.observation.instantiate argumentObservation bodyPack bodyCovered
  have codomainProducer : Transfer env U registry target (Locals.push locals)
      (realization.cons key.anchor) (realization.cons (argument.subst realization))
      (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available) B B (.sort bodyLevel) :=
    (originalCodomain target (Locals.push locals) (realization.cons key.anchor)
      (realization.cons (argument.subst realization))
      (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available) hTarget paired localFits).1
  obtain ⟨codomainResult⟩ := bodyResult.certificate.transfer henv hscoped hTarget
    codomainProducer bodyResult.typeAvailable
  obtain ⟨typePacked, typeOutside, typePack, typeCovered, typeOutsideAvailable⟩ :=
    Footprint.pack_available codomainResult.available
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm => (pack.atomized_localNeeds need hm).2)
  obtain ⟨typeFootprint, ⟨typeCertificate⟩, typeSelected⟩ :=
    codomainResult.certificate.instantiate argumentObservation typePack typeCovered
  have bodyRelated := Related.convert henv bodyResult.typed codomainResult.related bodyResult.related
  have self := (bodyRelated.symm henv).left_diagonal
  have rawBeta := (IsDefEq.beta rawBody rawArgument).subst henv substitutions hTarget
  have rawStep : HeadBeta ((VExpr.app (.lam A body) argument).subst realization)
      ((body.inst argument).subst realization) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, subst_inst] using
      (HeadBeta.contract (A := A.subst realization) (body := body.subst realization.lift)
        (argument := argument.subst realization) (trailing := []))
  have valueSelf : Related env U registry target ((body.inst argument).subst realization)
      ((body.inst argument).subst realization) ((B.inst argument).subst realization)
      (.singleton output) bodyResult.support := by
    simpa only [subst_inst, inst_lift_cons] using self
  refine ⟨⟨argumentResult, {
    resultFootprint := valueFootprint
    observation := valueObservation
    resultAvailable := ?_
    support := bodyResult.support
    typeFootprint := typeFootprint
    certificate := typeCertificate
    typeAvailable := ?_
    typed := bodyResult.typed
    related := Related.headBeta henv rawStep .refl rawBeta rawBeta.hasType.2 valueSelf }⟩⟩
  · apply valueSelected.available
    intro index need member
    exact (List.mem_append.mp member).elim (argumentAvailable index need)
      (bodyOutsideAvailable index need)
  · apply typeSelected.available
    intro index need member
    exact (List.mem_append.mp member).elim (argumentAvailable index need)
      (typeOutsideAvailable index need)

end Lean4Lean.AnchoredSource
