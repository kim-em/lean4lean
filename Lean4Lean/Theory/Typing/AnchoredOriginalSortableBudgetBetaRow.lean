import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBetaRow
import Lean4Lean.Theory.Typing.AnchoredSortableBudgetComposition
import Lean4Lean.Theory.Typing.AnchoredSortableDepthInstantiation

/-! Beta row contraction preserves simultaneous caller declaration controls.
Every semantic call is to a stored original child. Both finite dependent
substitutions retain their actual argument payload and all depth bounds. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open private code_union from Lean4Lean.Theory.Typing.AnchoredOriginalSortableBetaRow
set_option backward.isDefEq.respectTransparency false
/-- A concrete source lambda/application row contracts at the same fixed
available valuation. The body and codomain transports use their original
children; replay of the changed RHS observation uses the original instantiated
term child present in `IsDefEqStrong.beta`. -/
theorem SortableObs.betaRowBudgeted
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {support packed rawInput : Profile n}
    {domainFootprint bodyFootprint outside argumentFootprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref domainRef))
    (originalArgument : HereditaryBudgeted.StateFundamentalAt budgets env registry context argumentRef)
    (originalBody : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) bodyRef)
    (originalCodomain : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : HereditaryBudgeted.StateFundamentalAt budgets env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (frameBound : HereditaryBudgeted.Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals σ A true support domainFootprint)
    (guard : LambdaGuard env U registry target σ A key support)
    (bodyObservation : SortableObs env U registry target (Locals.push locals)
      (σ.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (argumentObservation : SortableObs env U registry target locals σ argument rawInput argumentFootprint)
    (argumentAdapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (domainBound : HereditaryBudgeted.Within budgets domain.nativeDepth)
    (bodyBound : HereditaryBudgeted.Within budgets bodyObservation.nativeDepth)
    (argumentBound : HereditaryBudgeted.Within budgets argumentObservation.nativeDepth)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output)) := by
  obtain ⟨arg⟩ := (originalArgument target locals σ σ available closed hTarget substitutions fits frameBound)
    argumentObservation argumentBound argumentAvailable
  let rawArgumentResult := arg.toSortableGradedResult
  let argumentResult : SortableGradedResult env U registry target locals σ available argument key.input :=
    { rawArgumentResult with adapter := (GeneralProfileAdapter.comp rawArgumentResult.adapter
        (GeneralNormalProfileAdapter.raise henv hscoped hTarget arg.bound argumentAdapter)) }
  obtain ⟨rawAnchor, _, _, _, _, _, anchorArgument, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains anchorArgument
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor)
      (σ.cons (argument.subst σ)) (A :: source) :=
    .cons substitutions formedA (guard.path.cast rawAnchor)
  let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
  have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
  have domainChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available A A (.sort domainLevel) := (originalDomain target locals σ σ available closed hTarget substitutions fits frameBound)
  obtain ⟨domainAnswer⟩ := domainChild.sortable henv hscoped hTarget closed domain domainBound domainAvailable
  let localFits := fits.pushCertificates domainRef domain domainAnswer.certificate domainAvailable
    domainAnswer.available guard.inputTyped guard.inputTyped arguments
    (Related.convert henv guard.inputTyped domainAnswer.related (arguments.symm henv)) head
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have localBound : HereditaryBudgeted.Within budgets localFits.nativeDepth := by
    intro current fuel member
    simp only [localFits, SortableTailPairedFits.nativeDepth, SortableTailPairedFits.pushCertificates,
      SortableTailFits.nativeDepth]
    have original := Nat.max_le.mp (frameBound current fuel member)
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨domainBound current fuel member, original.1⟩,
      Nat.max_le.mpr ⟨domainAnswer.valueBound current fuel member, original.2⟩⟩
  have bodyChild : HereditaryBudgeted.Transfer budgets env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (argument.subst σ)) (Valuation.push head available) body body B := (originalBody target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons (argument.subst σ)) (Valuation.push head available) headClosed hTarget paired localFits localBound)
  obtain ⟨bodyResult⟩ := bodyChild bodyObservation bodyBound (pack.available_atomized_localNeeds outsideAvailable)
  have codomainChild : HereditaryBudgeted.Transfer budgets env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (argument.subst σ)) (Valuation.push head available) B B (.sort bodyLevel) := (originalCodomain target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons (argument.subst σ)) (Valuation.push head available) headClosed hTarget paired localFits localBound)
  obtain ⟨codomain⟩ := codomainChild.sortable henv hscoped hTarget headClosed
    bodyResult.typeCertificate bodyResult.certificateBound bodyResult.typeAvailable
  obtain ⟨bodyPacked, bodyOutside, bodyPack, bodyCovered, bodyOutsideAvailable⟩ :=
    Footprint.pack_available bodyResult.resources
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodyScope := rawBody.closedN henv (CtxWF.closed henv paired.wf)
  have bodyOutsideLive := fits.forward.leavesLive henv hscoped hTarget bodyOutsideAvailable
    (bodyPack.scoped (bodyResult.observation.scoped bodyScope))
  obtain ⟨substituted, substitutedDepth⟩ := bodyResult.observation.instantiate_allDepth henv hscoped hTarget closed
    argumentResult bodyPack bodyCovered bodyOutsideAvailable bodyOutsideLive
  obtain ⟨typePacked, typeOutside, typePack, typeCovered, typeOutsideAvailable⟩ :=
    Footprint.pack_available codomain.available
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have typeScope := formedB.closedN henv (CtxWF.closed henv paired.wf)
  have typeOutsideLive := fits.forward.leavesLive henv hscoped hTarget typeOutsideAvailable
    (typePack.scoped (codomain.certificate.scoped typeScope))
  obtain ⟨typeCertificate, typeDepth⟩ := codomain.certificate.instantiate_allDepth henv hscoped hTarget closed
    argumentResult typePack typeCovered typeOutsideAvailable typeOutsideLive
  have substitutedBound : HereditaryBudgeted.Within budgets substituted.observation.nativeDepth := by
    intro current fuel member
    exact Nat.le_trans (substitutedDepth current) (Nat.max_le.mpr
      ⟨bodyResult.observationBound current fuel member, arg.observationBound current fuel member⟩)
  obtain ⟨replayed⟩ := (originalInstantiated target locals σ σ available closed hTarget
    substitutions fits frameBound) substituted.observation substitutedBound substituted.resources
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
  have firstAdapter := GeneralNormalProfileAdapter.raise henv hscoped hTarget replayed.bound substituted.adapter
  have secondAdapter := GeneralNormalProfileAdapter.raise henv hscoped hTarget bodyToFinal bodyResult.adapter
  simp only [raiseProfile_trans] at firstAdapter secondAdapter
  exact ⟨{
    rank := replayed.rank
    bound := Nat.le_trans bodyResult.bound bodyToFinal
    raw := replayed.raw
    footprint := replayed.footprint
    observation := replayed.observation
    adapter := GeneralProfileAdapter.comp replayed.adapter (GeneralProfileAdapter.comp firstAdapter secondAdapter)
    resources := replayed.resources
    support := (raiseProfile replayed.rank bodyToFinal bodyResult.support).union replayed.support
    typeFootprint := typeCertificate.footprint ++ replayed.typeFootprint
    typeCertificate := .union (typeCertificate.certificate.raise bodyToFinal) replayed.typeCertificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (typeCertificate.resources i need) (replayed.typeAvailable i need)
    typed := joinedTyped
    rawTyped := joinedRawTyped
    typeCode := joinedCode
    related := Related.retag henv joinedTyped joinedCode finalCross
    rawRelated := Related.retag henv joinedRawTyped joinedCode replayed.rawRelated
    live := replayed.live
    observationBound := replayed.observationBound
    certificateBound := by
      intro current fuel member
      simp only [SortableCert.nativeDepth, SortableCert.nativeDepth_raise]
      exact Nat.max_le.mpr ⟨Nat.le_trans (typeDepth current) (Nat.max_le.mpr
        ⟨codomain.valueBound current fuel member, arg.observationBound current fuel member⟩),
        replayed.certificateBound current fuel member⟩ }⟩

end Lean4Lean.AnchoredSource.Adapted
