import Lean4Lean.Theory.Typing.AnchoredSortablePiShape
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableCutSupply
import Lean4Lean.Theory.Typing.AnchoredSortableCodeResults
import Lean4Lean.Theory.Typing.AnchoredSortableTransferConversion

/-! Actual application transfer uses the original domain, codomain, function,
argument, and result children. All source queries retain hereditary syntax. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem DomainChain.backward
    (henv : env.Ordered)
    (chain : DomainChain env U registry Γ (input : Profile n) left right)
    (typed : input.HasType support) (formed : support.HasType (.sort true))
    (code : TypeRelated env U registry Γ right right support)
    (related : Related env U registry Γ x y right input support) :
    ∃ support, input.HasType support ∧ support.HasType (.sort true) ∧
      TypeRelated env U registry Γ left left support ∧
      Related env U registry Γ x y left input support := by
  induction chain with
  | refl => exact ⟨support, typed, formed, code, related⟩
  | step path ht hf bridge tail ih =>
    obtain ⟨_, _, _, _, pair⟩ := ih code related
    exact ⟨_, ht, hf, bridge.left_diagonal,
      Related.convert henv ht (bridge.symm henv ht.wf_type) pair⟩

private theorem admission_left
    (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ key x x := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := admitted
  exact ⟨anchor, pair.hasType.1, support, typed, formed, code, first, Related.left_diagonal second⟩

private theorem admission_right
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ key y y := by
  obtain ⟨anchor, pair, support, typed, formed, code, first, second⟩ := admitted
  exact ⟨anchor.trans pair, pair.hasType.2, support, typed, formed, code,
    Related.trans henv hscoped first second, Related.left_diagonal (Related.symm henv second)⟩

private theorem SortablePiRowCertificate.argumentPair
    (henv : env.Ordered) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    (row : SortablePiRowCertificate env U registry target locals σ available true A B (key : Key n) result)
    (domainCode : TypeRelated env U registry target (A.subst σ) (A.subst σ) row.domainSupport)
    (argument : Related env U registry target x y (A.subst σ) rawInput support)
    (adapter : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (raw : env.IsDefEq U target x y (A.subst σ))
    (admitted : Admitted env U registry target key x x) :
    Admitted env U registry target key x y := by
  have changed := adapter.termMap henv hscoped hTarget row.inputTyped domainCode argument
  obtain ⟨support, typed, formed, code, pair⟩ := DomainChain.backward henv row.alignment row.inputTyped
    row.domain.formed domainCode changed
  obtain ⟨anchor, _, _, _, _, _, first, _⟩ := admitted
  exact ⟨anchor, row.alignment.path.symm.cast raw, support, typed, formed, code,
    Related.retag henv typed code first, pair⟩

private theorem code_union
    (left : TypeRelated env U registry Γ A B p)
    (right : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => left.singleton h) (fun h => right.singleton h)

theorem SortableObs.appTransferOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    {key : Key n} {output : Atom n} {rawInput : Profile n}
    {functionFootprint argumentFootprint : Footprint}
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (domainIH : StateSortableFundamental env registry context (.ref originalDomain))
    (bodyIH : StateSortableFundamental env registry (.cons context originalDomain) originalBody)
    (functionChild : SortableComputationalTransfer env U registry target locals σ τ available f g (.forallE A B))
    (argumentChild : SortableComputationalTransfer env U registry target locals σ τ available a b A)
    (resultChild : SortableComputationalTransfer env U registry target locals σ σ available
      (B.inst a) (B.inst a) (.sort bodyLevel))
    (rawArgument : env.IsDefEq U source a b A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (functionObservation : SortableObs env U registry target locals σ f (Profile.fn key output) functionFootprint)
    (argumentObservation : SortableObs env U registry target locals σ a rawInput argumentFootprint)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (functionAvailable : functionFootprint.Available available)
    (argumentAvailable : argumentFootprint.Available available) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (.app f a) (.app g b) (B.inst a) (.singleton output)) := by
  obtain ⟨fn⟩ := functionChild functionObservation functionAvailable
  obtain ⟨arg⟩ := argumentChild argumentObservation argumentAvailable
  have domainChild : SortableTransfer env U registry target locals σ σ available A A (.sort domainLevel) :=
    domainIH target locals σ σ available closed hTarget substitutions.left fits.left
  obtain ⟨result, ⟨row⟩, outputTyped⟩ := fn.requestedCertificate.piRowOriginal henv hscoped hle hTarget
    closed context originalDomain originalBody substitutions.left fits.left.forward domainIH bodyIH
    fn.typeAvailable fn.requestedTyped
  obtain ⟨domainCode⟩ := domainChild row.domain row.domainAvailable
  have argumentRelated := arg.requestedRelated henv hTarget
  have paired := row.argumentPair henv hscoped hTarget domainCode.related argumentRelated arguments
    (rawArgument.substDF henv substitutions.wf hTarget substitutions) admitted
  have sourceLive := Related.live henv hscoped hTarget argumentRelated
  let sourceArgument : SortableGradedResult env U registry target locals σ available a key.input :=
    { rank := n, bound := Nat.le_refl n, raw := rawInput, footprint := argumentFootprint,
      observation := argumentObservation, adapter := by simpa only [raiseProfile_self] using arguments,
      resources := argumentAvailable, live := sourceLive }
  obtain ⟨requestedCert⟩ := OriginalFactorCut.rowInstantiateSortableOriginal henv hscoped hle hTarget closed
    context originalDomain originalBody substitutions.left fits.left.forward domainIH bodyIH row admitted sourceArgument
  obtain ⟨requestedCode⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget
    resultChild requestedCert.certificate requestedCert.resources
  have requestedRelated : Related env U registry target ((VExpr.app f a).subst σ)
      ((VExpr.app g b).subst τ) ((B.inst a).subst σ) (.singleton output) result := by
    simpa only [subst, subst_inst] using Related.apply henv hscoped hTarget outputTyped
      (by simpa only [subst_inst] using requestedCode.related)
      (by simpa only [subst] using fn.requestedRelated henv hTarget) paired
  let M := max fn.rank (arg.rank + 1) - 1
  have hfn : fn.rank ≤ M + 1 := by dsimp [M]; omega
  have harg : arg.rank ≤ M := by dsimp [M]; omega
  have hn : n ≤ M := by have := fn.bound; dsimp [M]; omega
  let highKey := raiseKey M hn key
  let highOutput := raiseAtom M hn output
  have raisedFn := fn.observation.raise hfn
  have raisedArg := arg.observation.raise harg
  have raisedFnAdapter := GeneralNormalProfileAdapter.raise henv hscoped hTarget hfn fn.adapter
  simp only [raiseProfile_trans] at raisedFnAdapter
  have gradeView := functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) hn key output
  have functionAdapter : GeneralNormalProfileAdapter env U registry target
      (raiseProfile (M + 1) hfn fn.raw) (Profile.fn highKey highOutput) := by
    change GeneralNormalProfileAdapter env U registry target _
      (raiseProfile (M + 1) (Nat.succ_le_succ hn) (.singleton (.fn key output))) at raisedFnAdapter
    rw [raiseProfile_singleton] at raisedFnAdapter
    exact raisedFnAdapter.comp (.cons (List.mem_singleton_self _)
      (gradeView.toGeneralAdapter henv hscoped hTarget) (.nil _))
  have argumentAdapter : GeneralNormalProfileAdapter env U registry target
      (raiseProfile M harg arg.raw) highKey.input := by
    have raised := GeneralNormalProfileAdapter.raise henv hscoped hTarget harg arg.adapter
    simp only [raiseProfile_trans] at raised
    exact raised.comp (GeneralNormalProfileAdapter.raise henv hscoped hTarget hn arguments)
  obtain ⟨factor⟩ := SortableObs.factor_application henv raisedFn functionAdapter raisedArg argumentAdapter
  let selectedView := AdapterNormal.view (U := U) (registry := registry) (Γ := target) henv factor.rawOrigin
  have selectedCertificate := SortableCert.map selectedView (fn.typeCertificate.raise hfn)
  have selectedTyped := selectedView.mapType_typed
    ((Profile.HasType.raise hfn fn.rawTyped).singleton_of_mem factor.origin)
  have selectedRelated := selectedView.termMap henv hscoped hTarget
    ((Related.raise henv hfn fn.rawRelated).singleton_of_mem factor.origin)
  generalize selectedSupportEq : selectedView.mapType (raiseProfile (M + 1) hfn fn.support) =
    selectedSupport at selectedCertificate selectedTyped selectedRelated
  rw [factor.normalOrigin] at selectedTyped selectedRelated
  obtain ⟨rawResult, ⟨rawRow⟩, rawOutputTyped⟩ := selectedCertificate.piRowOriginal henv hscoped hle hTarget
    closed context originalDomain originalBody substitutions.left fits.left.forward domainIH bodyIH
    fn.typeAvailable selectedTyped
  have highAdmission := Admitted.raise henv hn paired
  have actualAdmission := factor.keys.pull henv hscoped hTarget rawRow.anchor
    (AdapterNormal.normalizeAdmission henv hscoped hTarget highAdmission)
  have fixed : AdapterNormal.atom (n := M + 1) (.fn factor.key factor.output) =
      .fn factor.key factor.output := by
    rw [← factor.normalOrigin, AdapterNormal.atom_idem]
  have keyFixed := (AtomData.fn.inj fixed).1
  have inputFixed : AdapterNormal.profile factor.key.input = factor.key.input := congrArg KeyData.input keyFixed
  have sourceAdapter : GeneralNormalProfileAdapter env U registry target
      (raiseProfile M hn rawInput) factor.key.input := by
    change GeneralProfileAdapter env U registry target _ (AdapterNormal.profile factor.key.input)
    rw [inputFixed]
    exact GeneralProfileAdapter.comp (GeneralNormalProfileAdapter.raise henv hscoped hTarget hn arguments) factor.keys.arguments
  let rawSourceArgument : SortableGradedResult env U registry target locals σ available a factor.key.input :=
    { rank := M, bound := Nat.le_refl M, raw := raiseProfile M hn rawInput,
      footprint := argumentFootprint, observation := argumentObservation.raise hn,
      adapter := by simpa only [raiseProfile_self] using sourceAdapter,
      resources := argumentAvailable, live := (raiseProfile_live_iff hn rawInput).mpr sourceLive }
  obtain ⟨rawCert⟩ := OriginalFactorCut.rowInstantiateSortableOriginal henv hscoped hle hTarget closed
    context originalDomain originalBody substitutions.left fits.left.forward domainIH bodyIH rawRow (admission_left actualAdmission) rawSourceArgument
  obtain ⟨rawCode⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget
    resultChild rawCert.certificate rawCert.resources
  have rawPair : Related env U registry target (.app (g.subst τ) (a.subst σ))
      ((VExpr.app g b).subst τ) ((B.inst a).subst σ) (.singleton factor.output) rawResult := by
    simpa only [subst, subst_inst] using Related.apply henv hscoped hTarget rawOutputTyped
      (by simpa only [subst_inst] using rawCode.related)
      (by simpa only [subst, Profile.fn] using selectedRelated) actualAdmission
  have rawSelf := (rawPair.symm henv).left_diagonal
  have produced := SortableObs.app factor.functionObservation factor.argumentObservation factor.argumentAdapter
    (admission_right henv hscoped actualAdmission)
  have resultAdapter : GeneralNormalProfileAdapter env U registry target (.singleton factor.output)
      (raiseProfile M hn (.singleton output)) := by
    rw [raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) factor.outputAdapter (.nil _)
  have raisedTyped := Profile.HasType.raise hn outputTyped
  have raisedCode := TypeRelated.raise henv hn requestedCode.related
  have combinedCode := code_union raisedCode rawCode.related
  have wf := raisedTyped.wf_type.union rawOutputTyped.wf_type
  have finalTyped := raisedTyped.enlarge (Profile.le_union_left _ _) wf
  have finalRawTyped := rawOutputTyped.enlarge (Profile.le_union_right _ _) wf
  exact ⟨{
    rank := M, bound := hn, raw := .singleton factor.output,
    footprint := _, observation := produced, adapter := resultAdapter,
    resources := fun i need hm => (List.mem_append.mp hm).elim
      ((factor.selected.available_closed fn.resources closed) i need) (arg.resources i need),
    support := (raiseProfile M hn result).union rawResult,
    typeFootprint := requestedCert.footprint ++ rawCert.footprint,
    typeCertificate := .union (requestedCert.certificate.raise hn) rawCert.certificate,
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (requestedCert.resources i need) (rawCert.resources i need),
    typed := finalTyped, rawTyped := finalRawTyped, typeCode := combinedCode,
    related := Related.retag henv finalTyped combinedCode (Related.raise henv hn requestedRelated),
    rawRelated := Related.retag henv finalRawTyped combinedCode rawSelf
    live := Related.live henv hscoped hTarget rawSelf }⟩

end Lean4Lean.AnchoredSource.Adapted
