import Lean4Lean.Theory.Typing.AnchoredOriginalTailApplication
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceBetaJoint

/-! Beta transfer at exact original source tails. Forward substitution
replays the actual stored instantiated-term child. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

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
theorem Obs.betaRowOriginal
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
    (originalDomain : EndpointFundamental env registry context domainRef)
    (originalArgument : StateFundamental env registry context argumentRef)
    (originalBody : StateFundamental env registry (.cons context domainRef) bodyRef)
    (originalCodomain : StateFundamental env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : StateFundamental env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailPairedFits env registry target context locals σ σ available)
    (domain : CodeCert env U registry target locals σ A support domainFootprint)
    (guard : LambdaGuard env U registry target σ A key support)
    (bodyObservation : Obs env U registry target (Locals.push locals)
      (σ.cons key.anchor) body (.singleton output) bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (argumentObservation : Obs env U registry target locals σ argument rawInput argumentFootprint)
    (argumentAdapter : NormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output)) := by
  obtain ⟨arg⟩ := (originalArgument target locals σ σ available closed hTarget substitutions fits).1
    argumentObservation argumentAvailable
  let rawArgumentResult := arg.pure henv hscoped hTarget
  have argumentResult : GradedResult env U registry target locals σ available argument key.input :=
    { rawArgumentResult with adapter := (ProfileAdapter.comp rawArgumentResult.adapter
        (NormalProfileAdapter.raise henv hscoped hTarget arg.bound argumentAdapter)) }
  obtain ⟨rawAnchor, _, _, _, _, _, anchorArgument, _⟩ := admitted
  have arguments := Related.convert henv guard.inputTyped guard.domains anchorArgument
  have paired : Ctx.SubstEq env U target (σ.cons key.anchor)
      (σ.cons (argument.subst σ)) (A :: source) :=
    .cons substitutions formedA (guard.path.cast rawAnchor)
  let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
  have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
  have domainChild : GradedTransfer env U registry target locals σ σ available A A (.sort domainLevel) := (originalDomain target locals σ σ available closed hTarget substitutions fits).1
  obtain ⟨domainAnswer⟩ := domain.transfer_graded henv hscoped hTarget closed domainChild domainAvailable
  let localFits := fits.pushCertificates domainRef domain domainAnswer.certificate domainAvailable
    domainAnswer.available guard.inputTyped guard.inputTyped arguments
    (Related.convert henv guard.inputTyped domainAnswer.related (arguments.symm henv)) head
    (fun need hm => (pack.atomized_localNeeds need hm).1)
    (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodyChild : GradedTransfer env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (argument.subst σ)) (Valuation.push head available) body body B := (originalBody target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons (argument.subst σ)) (Valuation.push head available) headClosed hTarget paired localFits).1
  obtain ⟨bodyResult⟩ := bodyChild bodyObservation (pack.available_atomized_localNeeds outsideAvailable)
  have codomainChild : GradedTransfer env U registry target (Locals.push locals)
      (σ.cons key.anchor) (σ.cons (argument.subst σ)) (Valuation.push head available) B B (.sort bodyLevel) := (originalCodomain target (Locals.push locals) (σ.cons key.anchor)
    (σ.cons (argument.subst σ)) (Valuation.push head available) headClosed hTarget paired localFits).1
  obtain ⟨codomain⟩ := bodyResult.certificate.transfer_graded henv hscoped hTarget headClosed
    codomainChild bodyResult.typeAvailable
  obtain ⟨bodyPacked, bodyOutside, bodyPack, bodyCovered, bodyOutsideAvailable⟩ :=
    Footprint.pack_available bodyResult.resultAvailable
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have bodyScope := rawBody.closedN henv (CtxWF.closed henv paired.wf)
  have bodyOutsideLive := (fits.forward.toFits henv hTarget).leavesLive henv hscoped hTarget bodyOutsideAvailable
    (bodyPack.scoped (bodyResult.observation.scoped bodyScope))
  obtain ⟨substituted⟩ := bodyResult.observation.instantiate henv hscoped hTarget closed
    argumentResult bodyPack bodyCovered bodyOutsideAvailable bodyOutsideLive
  obtain ⟨typePacked, typeOutside, typePack, typeCovered, typeOutsideAvailable⟩ :=
    Footprint.pack_available codomain.available
      (fun need hm => (pack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => covered atom ((pack.atomized_localNeeds need hm).2 atom ha))
  have typeScope := formedB.closedN henv (CtxWF.closed henv paired.wf)
  have typeOutsideLive := (fits.forward.toFits henv hTarget).leavesLive henv hscoped hTarget typeOutsideAvailable
    (typePack.scoped (codomain.certificate.scoped typeScope))
  obtain ⟨typeCertificate⟩ := codomain.certificate.instantiate henv hscoped hTarget closed
    argumentResult typePack typeCovered typeOutsideAvailable typeOutsideLive
  obtain ⟨replayed⟩ := (originalInstantiated target locals σ σ available closed hTarget
    substitutions fits).1 substituted.observation substituted.resources
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
    rawRelated := Related.retag henv joinedRawTyped joinedCode replayed.rawRelated }⟩
private def lowerRaised {p : Profile n} (h : n ≤ N)
    (result : GradedTransferResult env U registry Γ locals σ τ available l r A
      (raiseProfile N h p)) :
    GradedTransferResult env U registry Γ locals σ τ available l r A p :=
  { result with
    bound := Nat.le_trans h result.bound
    adapter := by simpa only [raiseProfile_trans] using result.adapter
    typed := by simpa only [raiseProfile_trans] using result.typed
    related := by simpa only [raiseProfile_trans] using result.related }

private theorem unnormalizeAdmission
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {key : Key n} (admitted : Admitted env U registry Γ (AdapterNormal.key key) x y) :
    Admitted env U registry Γ key x y := by
  have view := (AdapterNormal.profileView (U := U) (registry := registry)
    (Γ := Γ) henv key.input).inverse henv
  exact view.admissionMapWith (key := AdapterNormal.key key) hΓ
    (fun {_ _} v {_ _ _} h => v.codeMap henv hscoped h)
    (fun hΓ {_ _} v {_ _ _ _} ht h => v.termMap henv hscoped hΓ ht h) admitted

theorem Obs.betaAppOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    {functionFootprint argumentFootprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : EndpointFundamental env registry context domainRef)
    (originalArgument : StateFundamental env registry context argumentRef)
    (originalBody : StateFundamental env registry (.cons context domainRef) bodyRef)
    (originalCodomain : StateFundamental env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : StateFundamental env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailPairedFits env registry target context locals σ σ available)
    (function : Obs env U registry target locals σ (.lam A body)
      (Profile.fn key output) functionFootprint)
    (argumentObservation : Obs env U registry target locals σ argument rawInput argumentFootprint)
    (argumentAdapter : NormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) (.singleton output)) := by
  obtain ⟨origin, ⟨path⟩, footprint⟩ := function.lambda_factor (.fn key output) rfl
  let M := path.height
  have ho : origin.rank ≤ M := Nat.le_trans (Nat.le_succ _) path.bounds.1
  have hn : n ≤ M := Nat.le_trans (Nat.le_succ _) path.bounds.2
  let oldKey := raiseKey M ho origin.key
  let newKey := raiseKey M hn key
  let oldOut := raiseAtom M ho origin.output
  let newOut := raiseAtom M hn output
  have views : AtomView env U registry target (n := M + 1)
      (.fn oldKey oldOut) (.fn newKey newOut) :=
    .trans ((functionGradeView ho origin.key origin.output).inverse henv)
      (.trans (path.normalize (M + 1) (Nat.le_succ _)) (functionGradeView hn key output))
  have change := views.toAdapter henv hscoped hTarget
  change AtomAdapter (n := M + 1) env U registry target
    (.fn (AdapterNormal.key oldKey) (AdapterNormal.atom oldOut))
    (.fn (AdapterNormal.key newKey) (AdapterNormal.atom newOut)) at change
  obtain ⟨sk, so, eq, ⟨keys⟩, _⟩ := change.fn_inv
  obtain ⟨rfl, rfl⟩ := AtomData.fn.inj eq
  have oldGuard := origin.node.guard.raise henv ho
  have normalAdmission := keys.pull henv hscoped hTarget
    (AdapterNormal.normalizeAdmission henv hscoped hTarget oldGuard.anchor)
    (AdapterNormal.normalizeAdmission henv hscoped hTarget (Admitted.raise henv hn admitted))
  have oldAdmission := unnormalizeAdmission henv hscoped hTarget normalAdmission
  have raisedArgs := NormalProfileAdapter.raise henv hscoped hTarget hn argumentAdapter
  have arguments : NormalProfileAdapter env U registry target
      (raiseProfile M hn rawInput) oldKey.input :=
    ProfileAdapter.comp raisedArgs keys.arguments
  have bodyObs := origin.node.bodyObservation.raise ho
  rw [raiseProfile_singleton] at bodyObs
  have domainAvailable : origin.node.domainFootprint.Available available :=
    fun i need hm => functionAvailable i need (footprint ▸ List.mem_append_left _ hm)
  have outsideAvailable : origin.node.outside.Available available :=
    fun i need hm => functionAvailable i need (footprint ▸ List.mem_append_right _ hm)
  obtain ⟨result⟩ := Obs.betaRowOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument
    originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
    closed hTarget substitutions fits (origin.node.domain.raise ho) oldGuard bodyObs
    (origin.node.pack.raise ho) (raiseProfile_subset ho origin.node.covered)
    (argumentObservation.raise hn) arguments oldAdmission domainAvailable outsideAvailable argumentAvailable
  obtain ⟨outputView⟩ := views.normal_fn_output henv hscoped hTarget rfl rfl
  have finish : AtomView env U registry target oldOut newOut :=
    .trans (AdapterNormal.view henv oldOut)
      (.trans outputView ((AdapterNormal.view henv newOut).inverse henv))
  have result := result.view henv hscoped hTarget finish
  have result : GradedTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument)
      (raiseProfile M hn (.singleton output)) := by
    simpa only [raiseProfile_singleton] using result
  exact ⟨lowerRaised hn result⟩

theorem Obs.betaDiagonalOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    {demand : Profile n} {footprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : EndpointFundamental env registry context domainRef)
    (originalArgument : StateFundamental env registry context argumentRef)
    (originalBody : StateFundamental env registry (.cons context domainRef) bodyRef)
    (originalCodomain : StateFundamental env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : StateFundamental env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailPairedFits env registry target context locals σ σ available)
    (observation : Obs env U registry target locals σ (.app (.lam A body) argument)
      demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ σ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .app function argumentObservation arguments admitted =>
    exact Obs.betaAppOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits function argumentObservation arguments admitted
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := left.betaDiagonalOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := right.betaDiagonalOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := source.betaDiagonalOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := source.betaDiagonalOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := source.betaDiagonalOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := source.betaDiagonalOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument originalBody
      originalCodomain originalInstantiated formedA formedB rawBody rawArgument closed hTarget
      substitutions fits resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem GradedTransfer.betaForwardOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainRef : EndpointRef sourceEnv U source A (.sort domainLevel))
    (argumentRef : EndpointState sourceEnv U source argument A)
    (bodyRef : EndpointState sourceEnv U (A :: source) body B)
    (codomainRef : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (instantiatedRef : EndpointState sourceEnv U source (body.inst argument) (B.inst argument))
    (originalDomain : EndpointFundamental env registry context domainRef)
    (originalArgument : StateFundamental env registry context argumentRef)
    (originalBody : StateFundamental env registry (.cons context domainRef) bodyRef)
    (originalCodomain : StateFundamental env registry (.cons context domainRef) codomainRef)
    (originalInstantiated : StateFundamental env registry context instantiatedRef)
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : TailPairedFits env registry target context locals σ τ available)
    : GradedTransfer env U registry target locals σ τ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) := by
  apply GradedTransfer.trans henv hscoped hTarget
  · intro n demand footprint observation resources
    exact observation.betaDiagonalOriginal henv hscoped context domainRef argumentRef bodyRef codomainRef instantiatedRef originalDomain originalArgument
      originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
      closed hTarget substitutions.left fits.left resources
  · exact (originalInstantiated target locals σ τ available closed hTarget substitutions fits).1

private theorem one_realized (argument : VExpr) (σ : Subst) :
    (Subst.one argument).comp σ = σ.cons (argument.subst σ) := by
  funext i
  cases i <;> rfl

theorem Obs.betaExpandAtomOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {output : Atom n} {footprint : Footprint}
    (argumentChild : GradedTransfer env U registry target locals σ σ available argument argument A)
    (rawArgument : env.HasType U source argument A)
    (_closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (observation : Obs env U registry target locals σ (body.inst argument) (.singleton output) footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (Obs env U registry target locals σ (.app (.lam A body) argument)
      (.singleton output) required) ∧ required.Available available := by
  obtain ⟨bodyFootprint, ⟨bodyObservation⟩, ⟨factor⟩⟩ :=
    observation.factorInst body argument 0 rfl σ (by funext i; rfl) locals (Locals.push locals)
  simp only [Subst.liftN, one_realized] at bodyObservation
  obtain ⟨arguments⟩ := factor.arguments available resources n
  obtain ⟨argResult⟩ :=
    argumentChild
      arguments.observation arguments.argumentAvailable
  let domain := argResult.requestedCertificate
  have typed := argResult.requestedTyped
  have related := argResult.requestedRelated henv hTarget
  have code := TypeRelated.lower henv argResult.bound argResult.typeCode
  have raw := rawArgument.subst henv substitutions hTarget
  let key : Key arguments.rank := ⟨A.subst σ, argument.subst σ, arguments.input⟩
  have admitted : Admitted env U registry target key key.anchor key.anchor :=
    ⟨raw, raw, _, typed, domain.formed, code, related, related⟩
  have guard : LambdaGuard env U registry target σ A key _ :=
    ⟨typed, domain.formed, .refl, code, admitted⟩
  have bodyHigh := bodyObservation.raise arguments.bound
  rw [raiseProfile_singleton] at bodyHigh
  have fn := Obs.lam domain guard bodyHigh arguments.pack (fun _ h => h)
  have app := Obs.app fn arguments.observation (ProfileAdapter.refl _) admitted
  have app' : Obs env U registry target locals σ (.app (.lam A body) argument)
      (raiseProfile arguments.rank arguments.bound (.singleton output))
      ((argResult.typeFootprint ++ arguments.outside) ++ arguments.argumentFootprint) := by
    rw [raiseProfile_singleton]
    exact app
  refine ⟨_, ⟨app'.lower arguments.bound⟩, ?_⟩
  intro i need hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (List.mem_append.mp hm).elim
      (argResult.typeAvailable i need) (arguments.outsideAvailable i need)
  · exact arguments.argumentAvailable i need hm

theorem Obs.betaExpandOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {demand : Profile n} {footprint : Footprint}
    (argumentChild : GradedTransfer env U registry target locals σ σ available argument argument A)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (observation : Obs env U registry target locals σ (body.inst argument) demand footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (Obs env U registry target locals σ (.app (.lam A body) argument)
      demand required) ∧ required.Available available := by
  induction demand generalizing footprint with
  | nil => exact ⟨[], ⟨.empty⟩, fun _ _ h => nomatch h⟩
  | cons atom rest ih =>
    obtain ⟨selected⟩ := observation.atom List.mem_cons_self
    obtain ⟨firstFootprint, ⟨first⟩, firstAvailable⟩ := selected.observation.betaExpandAtomOriginal henv
      argumentChild rawArgument closed hTarget substitutions
      (selected.atomizes.available_closed resources closed)
    obtain ⟨tailFootprint, ⟨tail⟩, selection⟩ := observation.subprofile
      (selected := rest) (fun _ h => List.mem_cons_of_mem _ h)
    obtain ⟨lastFootprint, ⟨last⟩, lastAvailable⟩ := ih tail
      (selection.available_closed resources closed)
    exact ⟨firstFootprint ++ lastFootprint, ⟨.union first last⟩,
      fun i need hm => (List.mem_append.mp hm).elim (firstAvailable i need) (lastAvailable i need)⟩

theorem GradedTransferResult.betaExpandOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B body argument : VExpr} {demand : Profile n}
    (argumentChild : GradedTransfer env U registry target locals τ τ available argument argument A)
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (formedInstantiated : env.HasType U source (B.inst argument) (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (result : GradedTransferResult env U registry target locals σ τ available
      (body.inst argument) (body.inst argument) (B.inst argument) demand) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (body.inst argument) (.app (.lam A body) argument) (B.inst argument) demand) := by
  obtain ⟨footprint, ⟨observation⟩, resources⟩ := result.observation.betaExpandOriginal henv
    argumentChild rawArgument closed hTarget (substitutions.right henv hTarget) result.resultAvailable
  have beta := IsDefEq.beta rawBody rawArgument
  have typePair := formedInstantiated.substDF henv substitutions.wf hTarget substitutions
  have rightBeta := IsDefEq.defeqDF typePair.symm
    (beta.subst henv (substitutions.right henv hTarget) hTarget)
  have leftTyped := beta.hasType.2.subst henv substitutions.left hTarget
  have step : HeadBeta ((VExpr.app (.lam A body) argument).subst τ)
      ((body.inst argument).subst τ) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, subst_inst] using
      (HeadBeta.contract (A := A.subst τ) (body := body.subst τ.lift)
        (argument := argument.subst τ) (trailing := []))
  exact ⟨{
    rank := result.rank
    bound := result.bound
    rawDemand := result.rawDemand
    resultFootprint := footprint
    observation := observation
    adapter := result.adapter
    resultAvailable := resources
    support := result.support
    typeFootprint := result.typeFootprint
    certificate := result.certificate
    typeAvailable := result.typeAvailable
    typed := result.typed
    rawTyped := result.rawTyped
    typeCode := result.typeCode
    related := Related.headBeta henv .refl step leftTyped rightBeta result.related
    rawRelated := Related.headBeta henv step step rightBeta rightBeta result.rawRelated }⟩


/-- Both beta directions replay only actual stored original children. The
inverse-substitution worker changes finite syntax, not source proof origins. -/
theorem OriginalTail.DerivationFundamental.beta
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (bodyRef : Derivation sourceEnv U (A :: source) body body B)
    (argumentRef : Derivation sourceEnv U source argument argument A)
    (result : Derivation sourceEnv U source (B.inst argument) (B.inst argument) (.sort bodyLevel))
    (instantiated : Derivation sourceEnv U source (body.inst argument) (body.inst argument) (B.inst argument))
    (domainIH : DerivationFundamental env registry context domain)
    (codomainIH : DerivationFundamental env registry (.cons context (.left domain)) codomain)
    (bodyIH : DerivationFundamental env registry (.cons context (.left domain)) bodyRef)
    (argumentIH : DerivationFundamental env registry context argumentRef)
    (instantiatedIH : DerivationFundamental env registry context instantiated) :
    DerivationFundamental env registry context
      (.beta domainWF bodyWF domain codomain bodyRef argumentRef result instantiated) := by
  intro target locals σ τ available closed hTarget substitutions fits
  have forward : GradedTransfer env U registry target locals σ τ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) :=
    GradedTransfer.betaForwardOriginal henv hscoped context (.left domain) (.ref (.left argumentRef))
      (.ref (.left bodyRef)) (.ref (.left codomain)) (.ref (.left instantiated))
      (domainIH.left henv hscoped) (argumentIH.left henv hscoped) (bodyIH.left henv hscoped)
      (codomainIH.left henv hscoped) (instantiatedIH.left henv hscoped)
      (domain.forget.defeq.mono hle) (codomain.forget.defeq.mono hle)
      (bodyRef.forget.defeq.mono hle) (argumentRef.forget.defeq.mono hle)
      closed hTarget substitutions fits
  have argumentChild : GradedTransfer env U registry target locals τ τ available argument argument A :=
    (argumentIH target locals τ τ available closed hTarget (substitutions.right henv hTarget) fits.right).1
  have instantiatedChild : GradedTransfer env U registry target locals σ τ available
      (body.inst argument) (body.inst argument) (B.inst argument) :=
    (instantiatedIH target locals σ τ available closed hTarget substitutions fits).1
  have backward : GradedTransfer env U registry target locals σ τ available
      (body.inst argument) (.app (.lam A body) argument) (B.inst argument) := by
    intro n demand footprint observation resources
    obtain ⟨value⟩ := instantiatedChild observation resources
    exact value.betaExpandOriginal henv argumentChild (bodyRef.forget.defeq.mono hle)
      (argumentRef.forget.defeq.mono hle) (result.forget.defeq.mono hle)
      closed hTarget substitutions
  exact ⟨forward, backward, forward.sortCorrect henv hTarget, backward.sortCorrect henv hTarget⟩

/-- Every semantic call in beta is charged to its actual original context;
none is charged to a newly synthesized substitution typing. -/
theorem OriginalTail.beta_schedule
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (bodyRef : Derivation sourceEnv U (A :: source) body body B)
    (argumentRef : Derivation sourceEnv U source argument argument A)
    (result : Derivation sourceEnv U source (B.inst argument) (B.inst argument) (.sort bodyLevel))
    (instantiated : Derivation sourceEnv U source (body.inst argument) (body.inst argument) (B.inst argument)) :
    let parent := schedule .fundamental (Closure.close
      (Derivation.beta domainWF bodyWF domain codomain bodyRef argumentRef result instantiated).origin
      context.closures).cost
    schedule .fundamental (Closure.close domain.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close codomain.origin
      (ContextDerivation.cons context (.left domain)).closures).cost < parent ∧
    schedule .fundamental (Closure.close bodyRef.origin
      (ContextDerivation.cons context (.left domain)).closures).cost < parent ∧
    schedule .fundamental (Closure.close argumentRef.origin context.closures).cost < parent ∧
    schedule .fundamental (Closure.close instantiated.origin context.closures).cost < parent := by
  have parentBound : (Closure.close
      (betaLeftOrigin domain.origin codomain.origin bodyRef.origin argumentRef.origin result.origin)
      context.closures).cost < (Closure.close
      (Derivation.beta domainWF bodyWF domain codomain bodyRef argumentRef result instantiated).origin
      context.closures).cost :=
    original_child_same_environment (Origin.rule_child (by simp)) context.closures
  have domainBound := binder_domain_cost domain.origin [codomain.origin]
    [lambdaOrigin domain.origin codomain.origin bodyRef.origin, argumentRef.origin, result.origin] context.closures
  have codomainBound := binder_body_cost (domain := domain.origin) (bodies := [codomain.origin])
    (children := [lambdaOrigin domain.origin codomain.origin bodyRef.origin, argumentRef.origin, result.origin])
    (body := codomain.origin) (by simp) context.closures
  have lambdaBound := binder_other_cost (domain := domain.origin) (bodies := [codomain.origin])
    (children := [lambdaOrigin domain.origin codomain.origin bodyRef.origin, argumentRef.origin, result.origin])
    (child := lambdaOrigin domain.origin codomain.origin bodyRef.origin) (by simp) context.closures
  have bodyBound := binder_body_cost (domain := domain.origin) (bodies := [codomain.origin, bodyRef.origin])
    (children := []) (body := bodyRef.origin) (by simp) context.closures
  have argumentBound := binder_other_cost (domain := domain.origin) (bodies := [codomain.origin])
    (children := [lambdaOrigin domain.origin codomain.origin bodyRef.origin, argumentRef.origin, result.origin])
    (child := argumentRef.origin) (by simp) context.closures
  have betaBound : (Closure.close
      (.typedBeta domain.origin bodyRef.origin argumentRef.origin instantiated.origin
        [.binder domain.origin [codomain.origin] [], result.origin]) context.closures).cost <
      (Closure.close (Derivation.beta domainWF bodyWF domain codomain bodyRef argumentRef result instantiated).origin
        context.closures).cost :=
    original_child_same_environment (Origin.rule_child (by simp)) context.closures
  have instantiatedBound := typed_beta_comparison domain.origin bodyRef.origin argumentRef.origin instantiated.origin
    [.binder domain.origin [codomain.origin] [], result.origin] context.closures
  exact ⟨schedule_strict (Nat.lt_trans domainBound parentBound) _ _,
    schedule_strict (Nat.lt_trans codomainBound parentBound) _ _,
    schedule_strict (Nat.lt_trans bodyBound (Nat.lt_trans lambdaBound parentBound)) _ _,
    schedule_strict (Nat.lt_trans argumentBound parentBound) _ _,
    schedule_strict (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_trans instantiatedBound betaBound)) _ _⟩

end Lean4Lean.AnchoredSource.Adapted
