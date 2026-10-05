import Lean4Lean.Theory.Typing.AnchoredBoundedInstantiation
import Lean4Lean.Theory.Typing.AnchoredBoundedBinder
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceScope
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode
import Lean4Lean.Theory.Typing.AnchoredBeta

/-! The direct graded beta row uses the original instantiated-term child to
interpret the genuinely substituted raw observation. Pure substitution itself
supplies finite syntax and liveness, not an invented semantic typing proof. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

noncomputable def Result.pure
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (result : Result current fuel env U registry Γ locals σ τ available left right type demand) :
    Substitution.GradedResult current fuel env U registry Γ locals τ available right demand where
  rank := result.rank
  bound := result.bound
  raw := result.rawDemand
  footprint := result.resultFootprint
  observation := result.observation
  adapter := result.adapter
  resources := result.resultAvailable
  live := Related.live henv hscoped hΓ result.rawRelated
  observationBound := result.observationBound

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

/-- A concrete source lambda/application row contracts at the same fixed
available valuation. The body and codomain transports use their original
children; replay of the changed RHS observation uses the original instantiated
term child present in `IsDefEqStrong.beta`. -/
theorem Obs.beta_row
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {support packed rawInput : Profile n}
    {domainFootprint bodyFootprint outside argumentFootprint : Footprint}
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalArgument : Joint current fuel env U registry source argument argument A)
    (originalBody : Joint current fuel env U registry (A :: source) body body B)
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalInstantiated : Joint current fuel env U registry source
      (body.inst argument) (body.inst argument) (B.inst argument))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    (domain : CodeCert env U registry target locals σ A support domainFootprint)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (guard : LambdaGuard env U registry target σ A key support)
    (bodyObservation : Obs env U registry target (Locals.push locals)
      (σ.cons key.anchor) body (.singleton output) bodyFootprint)
    (bodyBound : bodyObservation.nativeDepth current ≤ fuel)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (argumentObservation : Obs env U registry target locals σ argument rawInput argumentFootprint)
    (argumentBound : argumentObservation.nativeDepth current ≤ fuel)
    (argumentAdapter : NormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output)) := by
  obtain ⟨arg⟩ := (originalArgument target locals σ σ available closed hTarget substitutions fits).1
    argumentObservation argumentBound argumentAvailable
  let rawArgumentResult := arg.pure henv hscoped hTarget
  have argumentResult : Substitution.GradedResult current fuel env U registry target locals σ available argument key.input :=
    { rawArgumentResult with adapter := (ProfileAdapter.comp rawArgumentResult.adapter
        (NormalProfileAdapter.raise henv hscoped hTarget arg.bound argumentAdapter)) }
  obtain ⟨rawAnchor, _, _, _, _, _, anchorArgument, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains anchorArgument
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor)
      (σ.cons (argument.subst σ)) (A :: source) :=
    .cons substitutions formedA (guard.path.cast rawAnchor)
  let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
  have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
  have domainChild : Transfer current fuel env U registry target locals σ σ available A A (.sort domainLevel) := (originalDomain target locals σ σ available closed hTarget substitutions fits).1
  have localFits := fits.pushGraded henv hscoped hTarget closed domainChild domain domainBound domainAvailable
    guard.inputTyped arguments head (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodyChild : Transfer current fuel env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (argument.subst σ)) (Valuation.push head available) body body B := (originalBody target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons (argument.subst σ)) (Valuation.push head available) headClosed hTarget paired localFits).1
  obtain ⟨bodyResult⟩ := bodyChild bodyObservation bodyBound (pack.available_atomized_localNeeds outsideAvailable)
  have codomainChild : Transfer current fuel env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (argument.subst σ)) (Valuation.push head available) B B (.sort bodyLevel) := (originalCodomain target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons (argument.subst σ)) (Valuation.push head available) headClosed hTarget paired localFits).1
  obtain ⟨codomain⟩ := codomainChild.codeCertificate henv hscoped hTarget headClosed
    bodyResult.certificate bodyResult.certificateBound bodyResult.typeAvailable
  obtain ⟨bodyPacked, bodyOutside, bodyPack, bodyCovered, bodyOutsideAvailable⟩ :=
    Footprint.pack_available bodyResult.resultAvailable
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodyScope := rawBody.closedN henv (CtxWF.closed henv paired.wf)
  have bodyOutsideLive := fits.forward.forget.leavesLive henv hscoped hTarget bodyOutsideAvailable
    (bodyPack.scoped (bodyResult.observation.scoped bodyScope))
  obtain ⟨substituted⟩ := Substitution.Obs.instantiate henv hscoped hTarget closed
    bodyResult.observation bodyResult.observationBound argumentResult bodyPack bodyCovered bodyOutsideAvailable bodyOutsideLive
  obtain ⟨typePacked, typeOutside, typePack, typeCovered, typeOutsideAvailable⟩ :=
    Footprint.pack_available codomain.available
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have typeScope := formedB.closedN henv (CtxWF.closed henv paired.wf)
  have typeOutsideLive := fits.forward.forget.leavesLive henv hscoped hTarget typeOutsideAvailable
    (typePack.scoped (codomain.certificate.scoped typeScope))
  obtain ⟨typeCertificate⟩ := Substitution.CodeCert.instantiate henv hscoped hTarget closed
    codomain.certificate codomain.certificateBound argumentResult typePack typeCovered typeOutsideAvailable typeOutsideLive
  obtain ⟨replayed⟩ := (originalInstantiated target locals σ σ available closed hTarget
    substitutions fits).1 substituted.observation substituted.observationBound substituted.resources
  have bodyToFinal := Nat.le_trans substituted.bound replayed.bound
  have oldTyped := AnchoredSemantics.Profile.HasType.raise bodyToFinal bodyResult.typed
  simp only [raiseProfile_trans] at oldTyped
  have valueCode : TypeRelated env U registry target ((B.inst argument).subst σ)
      ((B.inst argument).subst σ) bodyResult.support := by
    simpa only [subst_inst, inst_lift_cons] using
      (TypeRelated.symm henv bodyResult.typed.wf_type codomain.related).left_diagonal
  have raisedCode := TypeRelated.raise henv bodyToFinal valueCode
  have joinedCode := code_union raisedCode replayed.typeCode
  have joinedWF := oldTyped.wf_type.union replayed.typed.wf_type
  have joinedTyped := oldTyped.enlarge (Profile.le_union_left _ _) joinedWF
  have joinedRawTyped := replayed.rawTyped.enlarge (Profile.le_union_right _ _) joinedWF
  have converted := Related.convert henv bodyResult.typed codomain.related bodyResult.related
  have self := (converted.symm henv).left_diagonal
  have valueSelf : Related env U registry target ((body.inst argument).subst σ)
      ((body.inst argument).subst σ) ((B.inst argument).subst σ)
      (raiseProfile bodyResult.rank bodyResult.bound (.singleton output)) bodyResult.support := by
    simpa only [subst_inst, inst_lift_cons] using self
  have rawBeta := (IsDefEq.beta rawBody rawArgument).subst henv substitutions hTarget
  have rawStep : HeadBeta ((VExpr.app (.lam A body) argument).subst σ)
      ((body.inst argument).subst σ) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, subst_inst] using
      (HeadBeta.contract (A := A.subst σ) (body := body.subst σ.lift)
        (argument := argument.subst σ) (trailing := []))
  have cross := Related.headBeta henv rawStep .refl rawBeta rawBeta.hasType.2 valueSelf
  have finalCross := Related.raise henv bodyToFinal cross
  simp only [raiseProfile_trans] at finalCross
  have firstAdapter := NormalProfileAdapter.raise henv hscoped hTarget replayed.bound substituted.adapter
  have secondAdapter := NormalProfileAdapter.raise henv hscoped hTarget bodyToFinal bodyResult.adapter
  simp only [raiseProfile_trans] at firstAdapter secondAdapter
  exact ⟨{
    rank := replayed.rank
    bound := Nat.le_trans bodyResult.bound bodyToFinal
    rawDemand := replayed.rawDemand
    resultFootprint := replayed.resultFootprint
    observation := replayed.observation
    adapter := ProfileAdapter.comp replayed.adapter (ProfileAdapter.comp firstAdapter secondAdapter)
    resultAvailable := replayed.resultAvailable
    support := (raiseProfile replayed.rank bodyToFinal bodyResult.support).union replayed.support
    typeFootprint := typeCertificate.footprint ++ replayed.typeFootprint
    certificate := .union (typeCertificate.certificate.raise bodyToFinal) replayed.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (typeCertificate.resources i need) (replayed.typeAvailable i need)
    typed := joinedTyped
    rawTyped := joinedRawTyped
    typeCode := joinedCode
    related := Related.retag henv joinedTyped joinedCode finalCross
    rawRelated := Related.retag henv joinedRawTyped joinedCode replayed.rawRelated
    observationBound := replayed.observationBound
    certificateBound := by simpa only [CodeCert.nativeDepth, CodeCert.nativeDepth_raise] using
      (Nat.max_le.mpr ⟨typeCertificate.certificateBound, replayed.certificateBound⟩) }⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
