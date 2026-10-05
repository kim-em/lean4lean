import Lean4Lean.Theory.Typing.AnchoredOriginalSortableLambdaData
import Lean4Lean.Theory.Typing.AnchoredSortableInstantiation
import Lean4Lean.Theory.Typing.AnchoredSortablePiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalTailBeta

/-! Actual hereditary beta contraction. Finite body and type queries are
substituted using the original argument result, then replayed through the
instantiated-term child already present in the original beta derivation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

abbrev OriginalTail.EndpointHereditaryFundamental (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {expression type : VExpr}
    (context : ContextDerivation sourceEnv U source)
    (original : EndpointRef sourceEnv U source expression type) : Prop :=
  StateHereditaryFundamental env registry context (.ref original)

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
theorem SortableObs.betaRowOriginal
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
    (originalDomain : EndpointHereditaryFundamental env registry context domainRef)
    (originalArgument : StateHereditaryFundamental env registry context argumentRef)
    (originalBody : StateHereditaryFundamental env registry (.cons context domainRef) bodyRef)
    (originalCodomain : StateHereditaryFundamental env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : StateHereditaryFundamental env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailPairedFits env registry target context locals σ σ available)
    (domain : SortableCert env U registry target locals σ A true support domainFootprint)
    (guard : LambdaGuard env U registry target σ A key support)
    (bodyObservation : SortableObs env U registry target (Locals.push locals)
      (σ.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (argumentObservation : SortableObs env U registry target locals σ argument rawInput argumentFootprint)
    (argumentAdapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output)) := by
  obtain ⟨arg⟩ := (originalArgument target locals σ σ available closed hTarget substitutions fits)
    argumentObservation argumentAvailable
  let rawArgumentResult := arg.toSortableGradedResult
  have argumentResult : SortableGradedResult env U registry target locals σ available argument key.input :=
    { rawArgumentResult with adapter := (GeneralProfileAdapter.comp rawArgumentResult.adapter
        (GeneralNormalProfileAdapter.raise henv hscoped hTarget arg.bound argumentAdapter)) }
  obtain ⟨rawAnchor, _, _, _, _, _, anchorArgument, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains anchorArgument
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor)
      (σ.cons (argument.subst σ)) (A :: source) :=
    .cons substitutions formedA (guard.path.cast rawAnchor)
  let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
  have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
  have domainChild : SortableComputationalTransfer env U registry target locals σ σ available A A (.sort domainLevel) := (originalDomain target locals σ σ available closed hTarget substitutions fits)
  obtain ⟨domainAnswer⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget domainChild domain domainAvailable
  let localFits := fits.pushCertificates domainRef domain domainAnswer.certificate domainAvailable
    domainAnswer.available guard.inputTyped guard.inputTyped arguments
    (Related.convert henv guard.inputTyped domainAnswer.related (arguments.symm henv)) head
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodyChild : SortableComputationalTransfer env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (argument.subst σ)) (Valuation.push head available) body body B := (originalBody target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons (argument.subst σ)) (Valuation.push head available) headClosed hTarget paired localFits)
  obtain ⟨bodyResult⟩ := bodyChild bodyObservation (pack.available_atomized_localNeeds outsideAvailable)
  have codomainChild : SortableComputationalTransfer env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (argument.subst σ)) (Valuation.push head available) B B (.sort bodyLevel) := (originalCodomain target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons (argument.subst σ)) (Valuation.push head available) headClosed hTarget paired localFits)
  obtain ⟨codomain⟩ := SortableComputationalTransfer.sortable henv hscoped headClosed hTarget
    codomainChild bodyResult.typeCertificate bodyResult.typeAvailable
  obtain ⟨bodyPacked, bodyOutside, bodyPack, bodyCovered, bodyOutsideAvailable⟩ :=
    Footprint.pack_available bodyResult.resources
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodyScope := rawBody.closedN henv (CtxWF.closed henv paired.wf)
  have bodyOutsideLive := fits.forward.leavesLive henv hscoped hTarget bodyOutsideAvailable
    (bodyPack.scoped (bodyResult.observation.scoped bodyScope))
  obtain ⟨substituted⟩ := bodyResult.observation.instantiate henv hscoped hTarget closed
    argumentResult bodyPack bodyCovered bodyOutsideAvailable bodyOutsideLive
  obtain ⟨typePacked, typeOutside, typePack, typeCovered, typeOutsideAvailable⟩ :=
    Footprint.pack_available codomain.available
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have typeScope := formedB.closedN henv (CtxWF.closed henv paired.wf)
  have typeOutsideLive := fits.forward.leavesLive henv hscoped hTarget typeOutsideAvailable
    (typePack.scoped (codomain.certificate.scoped typeScope))
  obtain ⟨typeCertificate⟩ := codomain.certificate.instantiate henv hscoped hTarget closed
    argumentResult typePack typeCovered typeOutsideAvailable typeOutsideLive
  obtain ⟨replayed⟩ := (originalInstantiated target locals σ σ available closed hTarget
    substitutions fits) substituted.observation substituted.resources
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
    live := replayed.live }⟩

end Lean4Lean.AnchoredSource.Adapted
