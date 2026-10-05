import Lean4Lean.Theory.Typing.AnchoredSortableDepthRetraction
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthCast
import Lean4Lean.Theory.Typing.AnchoredSortableGradedResult

/-! Application and lambda reconstruction retain all caller declaration bounds
in one actual returned source observation, including generalized argument adapters. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private append_available raiseKey_admitted raiseProfile_subset from
  Lean4Lean.Theory.Typing.AnchoredSortableGradedResult
set_option backward.isDefEq.respectTransparency false

theorem SortableObs.factor_application_allDepth
    (henv : env.Ordered)
    (functionObservation : SortableObs env U registry Γ locals σ function
      (functionDemand : Profile (n + 1)) functionFootprint)
    (functionAdapter : GeneralNormalProfileAdapter env U registry Γ functionDemand
      (Profile.fn requestedKey requestedOutput))
    (argumentObservation : SortableObs env U registry Γ locals σ argument
      (argumentDemand : Profile n) argumentFootprint)
    (argumentAdapter : GeneralNormalProfileAdapter env U registry Γ argumentDemand requestedKey.input) :
    ∃ factor : SortableApplicationFactor env U registry Γ locals σ function argument
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint,
      factor.argumentObservation = argumentObservation ∧
      ∀ current, factor.functionObservation.nativeDepth current ≤ functionObservation.nativeDepth current := by
  obtain ⟨normal, member, ⟨adapter⟩⟩ :=
    functionAdapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, normalEq⟩ := List.mem_map.mp member
  subst normal
  obtain ⟨key, output, normalOrigin, ⟨keys⟩, ⟨result⟩⟩ := adapter.fn_inv
  obtain ⟨selected, selectedBound⟩ := functionObservation.atom_allDepth originalMember
  have fixed : AdapterNormal.atom (n := n + 1) (.fn key output) = .fn key output := by
    rw [← normalOrigin, AdapterNormal.atom_idem]
  change AtomData.fn (AdapterNormal.key key) (AdapterNormal.atom output) =
    AtomData.fn key output at fixed
  have keyFixed := (AtomData.fn.inj fixed).1
  have outputFixed := (AtomData.fn.inj fixed).2
  have inputFixed : AdapterNormal.profile key.input = key.input := congrArg KeyData.input keyFixed
  let selectedObservation := normalOrigin ▸ SortableObs.view selected.observation (AdapterNormal.view henv original)
  have arguments : GeneralNormalProfileAdapter env U registry Γ argumentDemand key.input := by
    change GeneralProfileAdapter env U registry Γ (AdapterNormal.profile argumentDemand)
      (AdapterNormal.profile key.input)
    rw [inputFixed]
    exact GeneralProfileAdapter.comp argumentAdapter keys.arguments
  have result' : GeneralNormalAtomAdapter env U registry Γ output requestedOutput := by
    change GeneralAtomAdapter env U registry Γ (AdapterNormal.atom output) (AdapterNormal.atom requestedOutput)
    rw [outputFixed]
    exact result
  refine ⟨{
    key := key
    output := output
    rawOrigin := original
    origin := originalMember
    normalOrigin := normalOrigin
    selectedFootprint := selected.footprint
    functionObservation := selectedObservation
    selected := selected.atomizes
    argumentObservation := argumentObservation
    argumentAdapter := arguments
    keys := keys
    outputAdapter := result' }, rfl, ?_⟩
  intro current
  have same := SortableObs.nativeDepth_rec current normalOrigin
    (fun _ => locals) (fun _ => σ) (fun _ => function)
    (fun atom => Profile.singleton atom) (fun _ => selected.footprint)
    (SortableObs.view selected.observation (AdapterNormal.view henv original))
  change selectedObservation.nativeDepth current ≤ _
  rw [show selectedObservation.nativeDepth current = selected.observation.nativeDepth current from
    by simpa only [SortableObs.nativeDepth] using same]
  exact selectedBound current


theorem SortableGradedResult.atom_allDepth
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    (result : SortableGradedResult env U registry Γ locals σ available expression (.singleton requested)) :
    ∃ result' : SortableGradedAtomResult env U registry Γ locals σ available expression requested,
      ∀ current, result'.observation.nativeDepth current ≤ result.observation.nativeDepth current := by
  have adapter := result.adapter
  rw [raiseProfile_singleton] at adapter
  obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, he⟩ := List.mem_map.mp member
  subst normal
  obtain ⟨selected, selectedBound⟩ := result.observation.atom_allDepth originalMember
  let observed := SortableObs.view selected.observation (AdapterNormal.view henv original)
  have finalAdapter : GeneralNormalAtomAdapter env U registry Γ (AdapterNormal.atom original)
      (raiseAtom result.rank result.bound requested) := by
    simpa only [GeneralNormalAtomAdapter, AdapterNormal.atom_idem] using entry
  refine ⟨{
    rank := result.rank
    bound := result.bound
    atom := AdapterNormal.atom original
    footprint := selected.footprint
    observation := observed
    adapter := finalAdapter
    resources := selected.atomizes.available_closed result.resources closed
    live := (AdapterNormal.view henv original).live henv hscoped hΓ
      (result.live original originalMember) }, ?_⟩
  intro current
  change observed.nativeDepth current ≤ _
  simpa only [observed, SortableObs.nativeDepth] using selectedBound current


theorem SortableGradedResult.app_allDepth
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    {key : Key n} {output : Atom n}
    (function : SortableGradedResult env U registry Γ locals σ available f (Profile.fn key output))
    (argument : SortableGradedResult env U registry Γ locals σ available a rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry Γ rawInput key.input)
    (admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ)) :
    ∃ result : SortableGradedResult env U registry Γ locals σ available (.app f a) (.singleton output),
      ∀ current, result.observation.nativeDepth current ≤
        max (function.observation.nativeDepth current) (argument.observation.nativeDepth current) := by
  let N := max function.rank (argument.rank + 1)
  have hN : 0 < N := by dsimp [N]; omega
  let M := N - 1
  have hNM : M + 1 = N := by dsimp [M]; omega
  have hfn : function.rank ≤ M + 1 := by dsimp [M, N]; omega
  have harg : argument.rank ≤ M := by dsimp [M, N]; omega
  have hn : n ≤ M := by have := function.bound; dsimp [M, N]; omega
  let hf := function.raiseTo henv hscoped hΓ (M + 1) hfn
  let ha := argument.raiseTo henv hscoped hΓ M harg
  let highKey := raiseKey M hn key
  let highOutput := raiseAtom M hn output
  have functionAdapter : GeneralNormalProfileAdapter env U registry Γ hf.raw
      (Profile.fn highKey highOutput) := by
    have outer := (functionGradeView (env := env) (U := U) (registry := registry)
      (Γ := Γ) hn key output).toGeneralAdapter henv hscoped hΓ
    have h := hf.adapter
    change GeneralNormalProfileAdapter env U registry Γ hf.raw
      (raiseProfile (M + 1) (Nat.succ_le_succ hn) (.singleton (.fn key output))) at h
    rw [raiseProfile_singleton] at h
    exact GeneralProfileAdapter.comp h (.cons (List.mem_singleton_self _) outer (.nil _))
  have argumentAdapter : GeneralNormalProfileAdapter env U registry Γ ha.raw highKey.input :=
    GeneralProfileAdapter.comp ha.adapter
      (GeneralNormalProfileAdapter.raise henv hscoped hΓ hn arguments)
  obtain ⟨factor, argumentEqual, factorBound⟩ := SortableObs.factor_application_allDepth henv hf.observation functionAdapter
    ha.observation argumentAdapter
  have rawLive := hf.live factor.rawOrigin factor.origin
  have selectedLive := (AdapterNormal.view henv factor.rawOrigin).live henv hscoped hΓ rawLive
  rw [factor.normalOrigin] at selectedLive
  have highAdmission : Admitted env U registry Γ highKey (a.subst σ) (a.subst σ) := by
    exact raiseKey_admitted hn henv admitted
  have actualAdmission := factor.keys.pull henv hscoped hΓ selectedLive.1
    (AdapterNormal.normalizeAdmission henv hscoped hΓ highAdmission)
  let produced := SortableObs.app factor.functionObservation factor.argumentObservation
    factor.argumentAdapter actualAdmission
  have resultAdapter : GeneralNormalProfileAdapter env U registry Γ (.singleton factor.output)
      (raiseProfile M hn (.singleton output)) := by
    rw [raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) factor.outputAdapter (.nil _)
  refine ⟨{
    rank := M
    bound := hn
    raw := .singleton factor.output
    footprint := _
    observation := produced
    adapter := resultAdapter
    resources := append_available
      (factor.selected.available_closed hf.resources closed) ha.resources
    live := Profile.Live.singleton_iff.mpr selectedLive.2 }, ?_⟩
  intro current
  change (produced.nativeDepth current : Nat) ≤ _
  simp only [produced, SortableObs.nativeDepth]
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_trans (factorBound current) (by
      simp only [hf, SortableGradedResult.raiseTo, SortableObs.nativeDepth_raise]
      exact Nat.le_max_left _ _)
  · simp only [argumentEqual, ha, SortableGradedResult.raiseTo,
      SortableObs.nativeDepth_raise]
    exact Nat.le_max_right _ _


theorem SortableGradedResult.lam_allDepth
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    {key : Key n} {output : Atom n} {support : Profile n}
    (domain : SortableCert env U registry Γ locals σ annotation true support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (guard : LambdaGuard env U registry Γ σ annotation key support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ n)
    (covered : ∀ need ∈ localNeeds, List.Subset (need.atGrade n) key.input)
    (body : SortableGradedResult env U registry Γ (Locals.push locals) (σ.cons key.anchor)
      (Valuation.push localNeeds available) expression (.singleton output))
    (bodyClosed : (Valuation.push localNeeds available).AtomClosed) :
    ∃ result : SortableGradedResult env U registry Γ locals σ available
      (.lam annotation expression) (Profile.fn key output),
      ∀ current, result.observation.nativeDepth current ≤
        max (domain.nativeDepth current) (body.observation.nativeDepth current) := by
  obtain ⟨selected, selectedBound⟩ := body.atom_allDepth henv hscoped hΓ bodyClosed
  have raisedCovered : ∀ need ∈ localNeeds,
      List.Subset (need.atGrade selected.rank) (raiseProfile selected.rank selected.bound key.input) := by
    intro need member
    have hn := bounded need member
    have hN := Nat.le_trans hn selected.bound
    simp only [Need.atGrade, dif_pos hN]
    rw [← raiseProfile_trans hn selected.bound]
    exact raiseProfile_subset selected.bound (by
      simpa only [Need.atGrade, dif_pos hn, List.Subset, Profile.atoms] using covered need member)
  obtain ⟨packed, outside, normal, included, outsideAvailable⟩ :=
    Footprint.pack_available selected.resources
      (fun need member => Nat.le_trans (bounded need member) selected.bound)
      (fun need member atom ha => raisedCovered need member ha)
  let observed := SortableObs.lam (domain.raise selected.bound) (guard.raise henv selected.bound)
    selected.observation normal included
  have forward : GeneralNormalAtomAdapter env U registry Γ (n := selected.rank + 1)
      (AtomData.fn (raiseKey selected.rank selected.bound key) selected.atom)
      (AtomData.fn (raiseKey selected.rank selected.bound key) (raiseAtom selected.rank selected.bound output)) :=
    .fn (.refl _) selected.adapter
  have backward := ((functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := Γ) selected.bound key output).inverse henv).toGeneralAdapter henv hscoped hΓ
  have adapter : GeneralNormalProfileAdapter env U registry Γ
      (Profile.fn (raiseKey selected.rank selected.bound key) selected.atom)
      (raiseProfile (selected.rank + 1) (Nat.succ_le_succ selected.bound) (Profile.fn key output)) := by
    simp only [Profile.fn, raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) (GeneralAtomAdapter.comp forward backward) (.nil _)
  refine ⟨{
    rank := selected.rank + 1
    bound := Nat.succ_le_succ selected.bound
    raw := _
    footprint := _
    observation := observed
    adapter := adapter
    resources := append_available domainAvailable outsideAvailable
    live := Profile.Live.singleton_iff.mpr
      ⟨raiseKey_admitted selected.bound henv guard.anchor, selected.live⟩ }, ?_⟩
  intro current
  simp only [observed, SortableObs.nativeDepth, SortableCert.nativeDepth_raise]
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans (selectedBound current) (Nat.le_max_right _ _)⟩

end Lean4Lean.AnchoredSource.Adapted
