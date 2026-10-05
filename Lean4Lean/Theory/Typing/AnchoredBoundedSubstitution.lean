import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
import Lean4Lean.Theory.Typing.AnchoredBoundedPruning
import Lean4Lean.Theory.Typing.AnchoredNativeDepthRenaming

/-! Finite dependent substitution preserves the declaration-stage fuel.
Every replacement is an actual bounded source observation; native plans are
closed source leaves and are reused unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged.Substitution
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

/-- An actual source observation plus a finite normalized adapter. The raw
rank is allowed to grow, while every source leaf stays in the fixed valuation. -/
structure GradedResult (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (requested : Profile n) where
  rank : Nat
  bound : n ≤ rank
  raw : Profile rank
  footprint : Footprint
  observation : Obs env U registry Γ locals σ expression raw footprint
  adapter : NormalProfileAdapter env U registry Γ raw (raiseProfile rank bound requested)
  resources : footprint.Available available
  live : Profile.Live env U registry Γ raw
  observationBound : observation.nativeDepth current ≤ fuel

/-- Unpadding changes the requested grade only. In particular, no descent of
the raw function input or inverse application of an adapter is asserted. -/
def GradedResult.unpad {requested : Profile n}
    (result : GradedResult current fuel env U registry Γ locals σ available expression requested.pad) :
    GradedResult current fuel env U registry Γ locals σ available expression requested where
  rank := result.rank
  bound := Nat.le_trans (Nat.le_succ _) result.bound
  raw := result.raw
  footprint := result.footprint
  observation := result.observation
  adapter := by simpa only [raiseProfile_pad] using result.adapter
  resources := result.resources
  live := result.live
  observationBound := result.observationBound

private theorem raised_sortable {n N : Nat} (h : n ≤ N) {p : Profile n}
    (formed : p.HasType (.sort true)) :
    (raiseProfile N h p).HasType (.sort true) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact formed
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using formed
    · have hn : n ≤ N := by omega
      rw [raiseProfile_step hn]
      exact (ih hn).pad_sort

/-- A code seed does not expose the arbitrary higher-grade raw result.
Sortable rigidity selects the genuine padded requested profile before the
existing literal unpad constructor restores the original grade. -/
theorem GradedResult.code
    (henv : env.Ordered) (closed : available.AtomClosed)
    (result : GradedResult current fuel env U registry Γ locals σ available expression requested)
    (formed : requested.HasType (.sort true)) :
    ∃ footprint, ∃ certificate : CodeCert env U registry Γ locals σ expression requested footprint,
      footprint.Available available ∧ certificate.nativeDepth current ≤ fuel := by
  obtain ⟨footprint, certificate, _, resources, bounded⟩ :=
    result.observation.codeCert_of_adapter_bounded (current := current) henv result.adapter
      (raised_sortable result.bound formed) result.resources closed
  exact ⟨footprint, certificate.lowerRaised result.bound, resources, by
    simpa only [CodeCert.nativeDepth_lowerRaised] using Nat.le_trans bounded result.observationBound⟩

/-- Every replacement is a stored finite result for one original source
occurrence; there is no request for observations or semantics at future types. -/
inductive GradedSupply (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ replacement : Subst)
    (available : Valuation) : Footprint → Type where
  | nil : GradedSupply current fuel env U registry Γ locals σ replacement available []
  | cons {index : Nat} {need : Need}
      (value : GradedResult current fuel env U registry Γ locals σ available (replacement index) need.profile)
      (tail : GradedSupply current fuel env U registry Γ locals σ replacement available rest) :
      GradedSupply current fuel env U registry Γ locals σ replacement available ((index, need) :: rest)

 theorem GradedSupply.split
    (supply : GradedSupply current fuel env U registry Γ locals σ replacement available (left ++ right)) :
    Nonempty (GradedSupply current fuel env U registry Γ locals σ replacement available left) ∧
    Nonempty (GradedSupply current fuel env U registry Γ locals σ replacement available right) := by
  induction left with
  | nil => exact ⟨⟨.nil⟩, ⟨supply⟩⟩
  | cons entry rest ih =>
    cases supply with
    | cons value tail =>
      obtain ⟨⟨left⟩, ⟨right⟩⟩ := ih tail
      exact ⟨⟨.cons value left⟩, ⟨right⟩⟩

noncomputable def GradedResult.raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (result : GradedResult current fuel env U registry Γ locals σ available expression requested)
    (N : Nat) (bound : result.rank ≤ N) :
    GradedResult current fuel env U registry Γ locals σ available expression requested where
  rank := N
  bound := Nat.le_trans result.bound bound
  raw := raiseProfile N bound result.raw
  footprint := result.footprint
  observation := result.observation.raise bound
  adapter := by simpa only [raiseProfile_trans] using
    NormalProfileAdapter.raise henv hscoped hΓ bound result.adapter
  resources := result.resources
  live := (raiseProfile_live_iff bound result.raw).mpr result.live
  observationBound := by simpa only [Obs.nativeDepth_raise] using result.observationBound

noncomputable def GradedResult.exact
    {footprint : Footprint}
    (observation : Obs env U registry Γ locals σ expression demand footprint)
    (resources : footprint.Available available)
    (live : Profile.Live env U registry Γ demand)
    (observationBound : observation.nativeDepth current ≤ fuel) :
    GradedResult current fuel env U registry Γ locals σ available expression demand where
  rank := _
  bound := Nat.le_refl _
  raw := demand
  footprint := footprint
  observation := observation
  adapter := by rw [raiseProfile_self]; exact .refl _
  resources := resources
  live := live
  observationBound := observationBound

structure ApplicationFactor (current : Name → Bool) (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (Γ : List VExpr)
    (locals : List Nat) (σ : Subst) (function argument : VExpr)
    (requestedKey : Key n) (requestedOutput : Atom n)
    (functionDemand : Profile (n + 1)) (argumentDemand : Profile n) (functionFootprint argumentFootprint : Footprint) (functionDepth : Nat) where
  key : Key n
  output : Atom n
  rawOrigin : Atom (n + 1)
  origin : rawOrigin ∈ functionDemand.atoms
  normalOrigin : AdapterNormal.atom rawOrigin = .fn key output
  selectedFootprint : Footprint
  functionObservation : Obs env U registry Γ locals σ function
    (Profile.fn key output) selectedFootprint
  selected : selectedFootprint.Atomizes functionFootprint
  selectionBound : functionObservation.nativeDepth current ≤ functionDepth
  argumentObservation : Obs env U registry Γ locals σ argument
    argumentDemand argumentFootprint
  argumentAdapter : NormalProfileAdapter env U registry Γ argumentDemand key.input
  keys : KeyProgram env U registry Γ key (AdapterNormal.key requestedKey)
  outputAdapter : NormalAtomAdapter env U registry Γ output requestedOutput

/-- Both adapted children normalize at the actual returned function row.
The argument cut is finite syntax, recursively composed below that row's
rank. In particular this does not request an argument observation at an
intermediate demand. -/
theorem Obs.factor_application
    (henv : env.Ordered)
    (functionObservation : Obs env U registry Γ locals σ function
      (functionDemand : Profile (n + 1)) functionFootprint)
    (functionAdapter : NormalProfileAdapter env U registry Γ functionDemand
      (Profile.fn requestedKey requestedOutput))
    (argumentObservation : Obs env U registry Γ locals σ argument
      (argumentDemand : Profile n) argumentFootprint)
    (argumentAdapter : NormalProfileAdapter env U registry Γ argumentDemand requestedKey.input) :
    Nonempty (ApplicationFactor current env U registry Γ locals σ function argument
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint
      (functionObservation.nativeDepth current)) := by
  obtain ⟨normal, member, ⟨adapter⟩⟩ :=
    functionAdapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, normalEq⟩ := List.mem_map.mp member
  subst normal
  obtain ⟨key, output, normalOrigin, ⟨keys⟩, ⟨result⟩⟩ := adapter.fn_inv
  obtain ⟨selected, selectedBound⟩ := functionObservation.atom_bounded (current := current) originalMember
  have fixed : AdapterNormal.atom (n := n + 1) (.fn key output) = .fn key output := by
    rw [← normalOrigin, AdapterNormal.atom_idem]
  change AtomData.fn (AdapterNormal.key key) (AdapterNormal.atom output) =
    AtomData.fn key output at fixed
  have keyFixed := (AtomData.fn.inj fixed).1
  have outputFixed := (AtomData.fn.inj fixed).2
  have inputFixed : AdapterNormal.profile key.input = key.input := congrArg KeyData.input keyFixed
  let selectedObservation := normalOrigin ▸ Obs.view selected.observation (AdapterNormal.view henv original)
  have selectedDepth : selectedObservation.nativeDepth current ≤ functionObservation.nativeDepth current := by
    have he : selectedObservation.nativeDepth current = selected.observation.nativeDepth current := by
      exact (Obs.nativeDepth_rec current normalOrigin (fun _ => locals) (fun _ => σ)
        (fun _ => function) (fun a => Profile.singleton a) (fun _ => selected.footprint)
        (.view selected.observation (AdapterNormal.view henv original))).trans
          (by simp only [Obs.nativeDepth])
    rw [he]
    exact selectedBound
  have arguments : NormalProfileAdapter env U registry Γ argumentDemand key.input := by
    change ProfileAdapter env U registry Γ (AdapterNormal.profile argumentDemand)
      (AdapterNormal.profile key.input)
    rw [inputFixed]
    exact ProfileAdapter.comp argumentAdapter keys.arguments
  have result' : NormalAtomAdapter env U registry Γ output requestedOutput := by
    change AtomAdapter env U registry Γ (AdapterNormal.atom output) (AdapterNormal.atom requestedOutput)
    rw [outputFixed]
    exact result
  exact ⟨{
    key := key
    output := output
    rawOrigin := original
    origin := originalMember
    normalOrigin := normalOrigin
    selectedFootprint := selected.footprint
    functionObservation := selectedObservation
    selected := selected.atomizes
    selectionBound := selectedDepth
    argumentObservation := argumentObservation
    argumentAdapter := arguments
    keys := keys
    outputAdapter := result' }⟩


private theorem append_available {first second : Footprint} {available : Valuation}
    (left : first.Available available) (right : second.Available available) :
    (first ++ second).Available available := by
  intro i need hm
  exact (List.mem_append.mp hm).elim (left i need) (right i need)

private theorem raiseKey_admitted {n N : Nat} (h : n ≤ N)
    (henv : env.Ordered) {key : Key n}
    (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ (raiseKey N h key) x y := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    simpa only [raiseKey_self] using admitted
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseKey_self] using admitted
    · have hn : n ≤ N := by omega
      rw [raiseKey_step hn]
      exact Admitted.pad henv (ih hn)

/-- Align the two finite raw grades, then consume the actual returned function
row. The function's finite liveness supplies the raw guard; its assigned type
is not reconstructed or interpreted during syntax substitution. -/
theorem GradedResult.app
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    {key : Key n} {output : Atom n}
    (function : GradedResult current fuel env U registry Γ locals σ available f (Profile.fn key output))
    (argument : GradedResult current fuel env U registry Γ locals σ available a rawInput)
    (arguments : NormalProfileAdapter env U registry Γ rawInput key.input)
    (admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ)) :
    Nonempty (GradedResult current fuel env U registry Γ locals σ available (.app f a) (.singleton output)) := by
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
  have functionAdapter : NormalProfileAdapter env U registry Γ hf.raw
      (Profile.fn highKey highOutput) := by
    have outer := (functionGradeView (env := env) (U := U) (registry := registry)
      (Γ := Γ) hn key output).toAdapter henv hscoped hΓ
    have h := hf.adapter
    change NormalProfileAdapter env U registry Γ hf.raw
      (raiseProfile (M + 1) (Nat.succ_le_succ hn) (.singleton (.fn key output))) at h
    rw [raiseProfile_singleton] at h
    exact ProfileAdapter.comp h (.cons (List.mem_singleton_self _) outer (.nil _))
  have argumentAdapter : NormalProfileAdapter env U registry Γ ha.raw highKey.input :=
    ProfileAdapter.comp ha.adapter
      (NormalProfileAdapter.raise henv hscoped hΓ hn arguments)
  obtain ⟨factor⟩ := Obs.factor_application (current := current) henv hf.observation functionAdapter
    ha.observation argumentAdapter
  have rawLive := hf.live factor.rawOrigin factor.origin
  have selectedLive := (AdapterNormal.view henv factor.rawOrigin).live henv hscoped hΓ rawLive
  rw [factor.normalOrigin] at selectedLive
  have highAdmission : Admitted env U registry Γ highKey (a.subst σ) (a.subst σ) := by
    exact raiseKey_admitted hn henv admitted
  have actualAdmission := factor.keys.pull henv hscoped hΓ selectedLive.1
    (AdapterNormal.normalizeAdmission henv hscoped hΓ highAdmission)
  let produced := Obs.app factor.functionObservation ha.observation
    factor.argumentAdapter actualAdmission
  have resultAdapter : NormalProfileAdapter env U registry Γ (.singleton factor.output)
      (raiseProfile M hn (.singleton output)) := by
    rw [raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) factor.outputAdapter (.nil _)
  exact ⟨{
    rank := M
    bound := hn
    raw := .singleton factor.output
    footprint := _
    observation := produced
    adapter := resultAdapter
    resources := append_available
      (factor.selected.available_closed hf.resources closed) ha.resources
    live := Profile.Live.singleton_iff.mpr selectedLive.2
    observationBound := by
      simp only [produced, Obs.nativeDepth]
      exact Nat.max_le.mpr ⟨Nat.le_trans factor.selectionBound hf.observationBound, ha.observationBound⟩ }⟩

structure GradedAtomResult (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (requested : Atom n) where
  rank : Nat
  bound : n ≤ rank
  atom : Atom rank
  footprint : Footprint
  observation : Obs env U registry Γ locals σ expression (.singleton atom) footprint
  adapter : NormalAtomAdapter env U registry Γ atom (raiseAtom rank bound requested)
  resources : footprint.Available available
  live : Atom.Live env U registry Γ atom
  observationBound : observation.nativeDepth current ≤ fuel

theorem GradedResult.atom
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    (result : GradedResult current fuel env U registry Γ locals σ available expression (.singleton requested)) :
    Nonempty (GradedAtomResult current fuel env U registry Γ locals σ available expression requested) := by
  have adapter := result.adapter
  rw [raiseProfile_singleton] at adapter
  obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, he⟩ := List.mem_map.mp member
  subst normal
  obtain ⟨selected, selectedBound⟩ := result.observation.atom_bounded (current := current) originalMember
  let observed := Obs.view selected.observation (AdapterNormal.view henv original)
  have finalAdapter : NormalAtomAdapter env U registry Γ (AdapterNormal.atom original)
      (raiseAtom result.rank result.bound requested) := by
    simpa only [NormalAtomAdapter, AdapterNormal.atom_idem] using entry
  exact ⟨{
    rank := result.rank
    bound := result.bound
    atom := AdapterNormal.atom original
    footprint := selected.footprint
    observation := observed
    adapter := finalAdapter
    resources := selected.atomizes.available_closed result.resources closed
    live := (AdapterNormal.view henv original).live henv hscoped hΓ
      (result.live original originalMember)
    observationBound := by simpa only [observed, Obs.nativeDepth] using Nat.le_trans selectedBound result.observationBound }⟩

private theorem raiseProfile_subset {n N : Nat} (h : n ≤ N) {p q : Profile n}
    (included : List.Subset p q) : List.Subset (raiseProfile N h p) (raiseProfile N h q) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact included
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseProfile_self] using included
    · have hn : n ≤ N := by omega
      simp only [raiseProfile_step hn]
      intro atom member
      obtain ⟨old, ho, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨old, ih hn ho, rfl⟩

/-- The lambda retains its declared input after finite body substitution.
Only consumed local leaves are packed; their original bounds imply literal
coverage at the body's returned grade. -/
theorem GradedResult.lam
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    {key : Key n} {output : Atom n} {support : Profile n}
    (domain : CodeCert env U registry Γ locals σ annotation support domainFootprint)
    (domainBound : domain.nativeDepth current ≤ fuel)
    (domainAvailable : domainFootprint.Available available)
    (guard : LambdaGuard env U registry Γ σ annotation key support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ n)
    (covered : ∀ need ∈ localNeeds, List.Subset (need.atGrade n) key.input)
    (body : GradedResult current fuel env U registry Γ (Locals.push locals) (σ.cons key.anchor)
      (Valuation.push localNeeds available) expression (.singleton output))
    (bodyClosed : (Valuation.push localNeeds available).AtomClosed) :
    Nonempty (GradedResult current fuel env U registry Γ locals σ available
      (.lam annotation expression) (Profile.fn key output)) := by
  obtain ⟨selected⟩ := body.atom henv hscoped hΓ bodyClosed
  have raisedCovered : ∀ need ∈ localNeeds,
      List.Subset (need.atGrade selected.rank) (raiseProfile selected.rank selected.bound key.input) := by
    intro need member
    have hn := bounded need member
    have hN := Nat.le_trans hn selected.bound
    simp only [Need.atGrade, dif_pos hN]
    rw [← raiseProfile_trans hn selected.bound]
    exact raiseProfile_subset selected.bound (by
      simpa only [Need.atGrade, dif_pos hn] using covered need member)
  obtain ⟨packed, outside, normal, included, outsideAvailable⟩ :=
    Footprint.pack_available selected.resources
      (fun need member => Nat.le_trans (bounded need member) selected.bound)
      (fun need member atom ha => raisedCovered need member ha)
  let observed := Obs.lam (domain.raise selected.bound) (guard.raise henv selected.bound)
    selected.observation normal included
  have forward : NormalAtomAdapter env U registry Γ (n := selected.rank + 1)
      (AtomData.fn (raiseKey selected.rank selected.bound key) selected.atom)
      (AtomData.fn (raiseKey selected.rank selected.bound key) (raiseAtom selected.rank selected.bound output)) :=
    .fn (.refl _) selected.adapter
  have backward := ((functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := Γ) selected.bound key output).inverse henv).toAdapter henv hscoped hΓ
  have adapter : NormalProfileAdapter env U registry Γ
      (Profile.fn (raiseKey selected.rank selected.bound key) selected.atom)
      (raiseProfile (selected.rank + 1) (Nat.succ_le_succ selected.bound) (Profile.fn key output)) := by
    simp only [Profile.fn, raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) (AtomAdapter.comp forward backward) (.nil _)
  exact ⟨{
    rank := selected.rank + 1
    bound := Nat.succ_le_succ selected.bound
    raw := _
    footprint := _
    observation := observed
    adapter := adapter
    resources := append_available domainAvailable outsideAvailable
    live := Profile.Live.singleton_iff.mpr
      ⟨raiseKey_admitted selected.bound henv guard.anchor, selected.live⟩
    observationBound := by
      simp only [observed, Obs.nativeDepth, Obs.nativeDepth_raise, CodeCert.nativeDepth_raise]
      exact Nat.max_le.mpr ⟨domainBound, selected.observationBound⟩ }⟩

private noncomputable def raiseView {n N : Nat} (h : n ≤ N)
    {a b : Atom n} (view : AtomView env U registry Γ a b) :
    AtomView env U registry Γ (raiseAtom N h a) (raiseAtom N h b) := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact view
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseAtom_self] using view
    · have hn : n ≤ N := by omega
      simp only [raiseAtom_step hn]
      exact .pad (ih hn)

noncomputable def GradedResult.view
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (result : GradedResult current fuel env U registry Γ locals σ available expression (.singleton a))
    (view : AtomView env U registry Γ a b) :
    GradedResult current fuel env U registry Γ locals σ available expression (.singleton b) := by
  refine ⟨result.rank, result.bound, result.raw, result.footprint, result.observation,
    ?_, result.resources, result.live, result.observationBound⟩
  have first := result.adapter
  rw [raiseProfile_singleton] at first ⊢
  exact ProfileAdapter.comp first (.cons (List.mem_singleton_self _)
    ((raiseView result.bound view).toAdapter henv hscoped hΓ) (.nil _))

noncomputable def GradedResult.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {requested : Profile n}
    (result : GradedResult current fuel env U registry Γ locals σ available expression requested) :
    GradedResult current fuel env U registry Γ locals σ available expression requested.pad := by
  let N := max result.rank (n + 1)
  let lifted := result.raiseTo henv hscoped hΓ N (Nat.le_max_left ..)
  refine ⟨N, Nat.le_max_right .., lifted.raw, lifted.footprint, lifted.observation,
    ?_, lifted.resources, lifted.live, lifted.observationBound⟩
  rw [raiseProfile_pad]
  exact lifted.adapter

private def ProfileAdapter.appendTarget
    (first : ProfileAdapter env U registry Γ source left)
    (second : ProfileAdapter env U registry Γ source right) :
    ProfileAdapter env U registry Γ source (left.union right) := by
  match first with
  | .nil _ => exact second
  | .cons member head tail => exact .cons member head (ProfileAdapter.appendTarget tail second)
termination_by sizeOf first
decreasing_by simp_wf; omega

private noncomputable def ProfileAdapter.union
    (first : ProfileAdapter env U registry Γ p p')
    (second : ProfileAdapter env U registry Γ q q') :
    ProfileAdapter env U registry Γ (p.union q) (p'.union q') :=
  ProfileAdapter.appendTarget
    (ProfileAdapter.comp (ProfileAdapter.select (fun _ h => List.mem_append_left _ h)) first)
    (ProfileAdapter.comp (ProfileAdapter.select (fun _ h => List.mem_append_right _ h)) second)

noncomputable def GradedResult.union
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (left : GradedResult current fuel env U registry Γ locals σ available expression p)
    (right : GradedResult current fuel env U registry Γ locals σ available expression q) :
    GradedResult current fuel env U registry Γ locals σ available expression (p.union q) := by
  let N := max left.rank right.rank
  let a := left.raiseTo henv hscoped hΓ N (Nat.le_max_left ..)
  let b := right.raiseTo henv hscoped hΓ N (Nat.le_max_right ..)
  refine ⟨N, a.bound, a.raw.union b.raw, a.footprint ++ b.footprint,
    .union a.observation b.observation, ?_, append_available a.resources b.resources,
    Profile.Live.union_iff.mpr ⟨a.live, b.live⟩, by
      simpa only [Obs.nativeDepth] using Nat.max_le.mpr ⟨a.observationBound, b.observationBound⟩⟩
  rw [raiseProfile_union]
  have ha : NormalProfileAdapter env U registry Γ (a.raw : Profile N) (raiseProfile N a.bound p) := a.adapter
  have hb : NormalProfileAdapter env U registry Γ (b.raw : Profile N) (raiseProfile N b.bound q) := b.adapter
  simpa only [NormalProfileAdapter, AdapterNormal.profile, Profile.union, Profile.atoms,
    Profile.mk, List.map_append] using ProfileAdapter.union ha hb

private theorem available_shift {footprint : Footprint} {available : Valuation}
    (resources : footprint.Available available) :
    (footprint.sourceLift (.skip .refl)).Available (Valuation.push head available) := by
  intro i need member
  obtain ⟨⟨index, original⟩, hm, he⟩ := List.mem_map.mp member
  cases he
  exact resources _ _ hm

noncomputable def GradedResult.sourceLift
    (result : GradedResult current fuel env U registry Γ locals σ available expression requested)
    (anchor : VExpr) (head : List Need) :
    GradedResult current fuel env U registry Γ (Locals.push locals) (σ.cons anchor)
      (Valuation.push head available) expression.lift requested where
  rank := result.rank
  bound := result.bound
  raw := result.raw
  footprint := result.footprint.sourceLift (.skip .refl)
  observation := (lift_eq_lift' (e := expression)).symm ▸
    result.observation.renameSource (.skip .refl) (σ.cons anchor) rfl (Locals.push locals)
  adapter := result.adapter
  resources := available_shift result.resources
  live := result.live
  observationBound := by
    rw [Obs.nativeDepth_rec current (lift_eq_lift' (e := expression)).symm
      (fun _ => Locals.push locals) (fun _ => σ.cons anchor) (fun e => e)
      (fun _ => result.raw) (fun _ => result.footprint.sourceLift (.skip .refl))]
    simpa only [Obs.nativeDepth_renameSource] using result.observationBound

/-- Fresh local replacements are literal variables. External replacements are
source-lifted, so none of their old leaves becomes the new bound variable. -/
theorem GradedSupply.underBinder
    {input : Profile n} {head : List Need}
    (normal : BinderPack n input required outside)
    (inside : Profile.Live env U registry Γ input)
    (headContains : ∀ need ∈ required.localNeeds, need ∈ head)
    (supply : GradedSupply current fuel env U registry Γ locals σ replacement available outside)
    (anchor : VExpr) :
    Nonempty (GradedSupply current fuel env U registry Γ (Locals.push locals) (σ.cons anchor)
      replacement.lift (Valuation.push head available) required) := by
  induction normal with
  | nil => exact ⟨.nil⟩
  | «local» need bound rest ih =>
    obtain ⟨first, restLive⟩ := Profile.Live.union_iff.mp inside
    have lower : Profile.Live env U registry Γ need.profile := by
      simp only [Need.atGrade, dif_pos bound] at first
      exact (raiseProfile_live_iff bound need.profile).mp first
    obtain ⟨tail⟩ := ih restLive
      (fun original hm => headContains original (List.mem_cons_of_mem _ hm)) supply
    have resources : Footprint.Available [(0, need)] (Valuation.push head available) := by
      intro index original hm
      cases List.mem_singleton.mp hm
      exact headContains need List.mem_cons_self
    exact ⟨.cons (GradedResult.exact (.var _ _ 0 need.profile) resources lower (by simp only [Obs.nativeDepth]; exact Nat.zero_le _)) tail⟩
  | external index need rest ih =>
    cases supply with
    | cons value tail =>
      obtain ⟨result⟩ := ih inside headContains tail
      exact ⟨.cons (value.sourceLift anchor head) result⟩

structure CertificateResult (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (expression : VExpr) (profile : Profile n) where
  footprint : Footprint
  certificate : CodeCert env U registry Γ locals σ expression profile footprint
  resources : footprint.Available available
  certificateBound : certificate.nativeDepth current ≤ fuel

structure RowsResult (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B : VExpr) (ambient : Profile n) (rows : List (Key n × Profile n)) where
  footprint : Footprint
  bodies : PiRows env U registry Γ locals σ A B ambient rows footprint
  resources : footprint.Available available
  bodiesBound : bodies.nativeDepth current ≤ fuel

private theorem replacement_lift (replacement realization : Subst) (anchor : VExpr) :
    replacement.lift.comp (realization.cons anchor) =
      (replacement.comp realization).cons anchor := by
  funext index
  cases index <;> simp only [Subst.comp, Subst.lift, Subst.cons, subst_bvar, lift_subst_cons]

private theorem anchor_live
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {key : Key n} (anchor : Admitted env U registry Γ key key.anchor key.anchor) :
    Profile.Live env U registry Γ key.input := by
  obtain ⟨_, _, _, _, _, _, related, _⟩ := anchor
  exact Related.live henv hscoped hΓ related

private def obsFootprint {footprint : Footprint}
    (_ : Obs env U registry Γ locals σ expression demand footprint) : Footprint := footprint

private def certFootprint {footprint : Footprint}
    (_ : CodeCert env U registry Γ locals σ expression demand footprint) : Footprint := footprint

private def guardAnchor {key : Key n}
    (_ : LambdaGuard env U registry Γ σ annotation key support) : VExpr := key.anchor

mutual
theorem Obs.substitute
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (observation : Obs env U registry Γ locals sourceRealization expression demand required)
    (depth : observation.nativeDepth current ≤ fuel)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : GradedSupply current fuel env U registry Γ newLocals realization replacement available required) :
    Nonempty (GradedResult current fuel env U registry Γ newLocals realization available
      (expression.subst replacement) demand) := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    exact ⟨GradedResult.exact
      (.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body)
      (fun _ _ h => nomatch h) (body.live henv hscoped hΓ (fun _ _ h => nomatch h)) (by simpa only [Obs.nativeDepth] using depth)⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨GradedResult.exact
      (.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree)
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h)) (by simpa only [Obs.nativeDepth] using depth)⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨GradedResult.exact
      (.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree)
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h)) (by simpa only [Obs.nativeDepth] using depth)⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact ⟨GradedResult.exact
      (.constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree)
      (fun _ _ h => nomatch h) (tree.live henv hscoped hΓ (fun _ _ h => nomatch h)) (by simpa only [Obs.nativeDepth] using depth)⟩
  | .var _ _ _ _ =>
    cases supply with
    | cons value tail => exact ⟨value⟩
  | .empty =>
    exact ⟨GradedResult.exact .empty (fun _ _ h => nomatch h) .empty (by simp only [Obs.nativeDepth]; exact Nat.zero_le _)⟩
  | .sort relevant =>
    exact ⟨GradedResult.exact (.sort relevant) (fun _ _ h => nomatch h)
      (by cases n <;> simp [Profile.Live, Profile.sort, Atom.Live, Profile.atoms]) (by simp only [Obs.nativeDepth]; exact Nat.zero_le _)⟩
  | .app fn arg arguments admitted =>
    obtain ⟨⟨fnSupply⟩, ⟨argSupply⟩⟩ := supply.split
    obtain ⟨hf⟩ := Obs.substitute henv hscoped hΓ fn
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed fnSupply
    obtain ⟨ha⟩ := Obs.substitute henv hscoped hΓ arg
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed argSupply
    exact GradedResult.app henv hscoped hΓ closed hf ha arguments
      (by simpa only [subst_subst, realized] using admitted)
  | .lam domain guard body normal covered =>
    obtain ⟨⟨domainSupply⟩, ⟨externalSupply⟩⟩ := supply.split
    obtain ⟨hd⟩ := CodeCert.substitute henv hscoped hΓ domain
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed domainSupply
    let bodyFootprint := obsFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := Obs.substitute henv hscoped hΓ body
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    exact GradedResult.lam henv hscoped hΓ closed hd.certificate hd.certificateBound hd.resources
      (guard.sourceSubstitute replacement realization realized) head
      (fun need hm => (localCoverage need hm).1)
      (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha)) hb headClosed
  | .pi domain guard bodies =>
    obtain ⟨⟨domainSupply⟩, ⟨rowSupply⟩⟩ := supply.split
    obtain ⟨hd⟩ := CodeCert.substitute henv hscoped hΓ domain
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed domainSupply
    obtain ⟨hb⟩ := PiRows.substitute henv hscoped hΓ bodies
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed rowSupply
    exact ⟨GradedResult.exact
      (.pi hd.certificate (guard.sourceSubstitute replacement realization realized) hb.bodies)
      (append_available hd.resources hb.resources) (by
        intro atom member
        cases List.mem_singleton.mp member
        trivial) (by simpa only [Obs.nativeDepth] using Nat.max_le.mpr ⟨hd.certificateBound, hb.bodiesBound⟩)⟩
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := Obs.substitute henv hscoped hΓ left
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := Obs.substitute henv hscoped hΓ right
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed rightSupply
    exact ⟨hl.union henv hscoped hΓ hr⟩
  | .view source view =>
    obtain ⟨hs⟩ := Obs.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.view henv hscoped hΓ view⟩
  | .pad source =>
    obtain ⟨hs⟩ := Obs.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.pad henv hscoped hΓ⟩
  | .unpad source =>
    obtain ⟨hs⟩ := Obs.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨hs.unpad⟩
  | .rowShift source =>
    obtain ⟨hs⟩ := Obs.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨(hs.pad henv hscoped hΓ).view henv hscoped hΓ (.commutePadFn _ _)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem CodeCert.substitute
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {expression : VExpr}
    {demand : Profile n} {required : Footprint}
    (certificate : CodeCert env U registry Γ locals sourceRealization expression demand required)
    (depth : certificate.nativeDepth current ≤ fuel)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : GradedSupply current fuel env U registry Γ newLocals realization replacement available required) :
    Nonempty (CertificateResult current fuel env U registry Γ newLocals realization available
      (expression.subst replacement) demand) := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨result⟩ := Obs.substitute henv hscoped hΓ observation
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    obtain ⟨footprint, cert, resources, certificateBound⟩ := result.code henv closed formed
    exact ⟨⟨footprint, cert, resources, certificateBound⟩⟩
  | .union left right =>
    obtain ⟨⟨leftSupply⟩, ⟨rightSupply⟩⟩ := supply.split
    obtain ⟨hl⟩ := CodeCert.substitute henv hscoped hΓ left
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed leftSupply
    obtain ⟨hr⟩ := CodeCert.substitute henv hscoped hΓ right
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed rightSupply
    exact ⟨⟨_, .union hl.certificate hr.certificate, append_available hl.resources hr.resources, by simpa only [CodeCert.nativeDepth] using Nat.max_le.mpr ⟨hl.certificateBound, hr.certificateBound⟩⟩⟩
  | .pad source =>
    obtain ⟨hs⟩ := CodeCert.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .pad hs.certificate, hs.resources, by simpa only [CodeCert.nativeDepth] using hs.certificateBound⟩⟩
  | .familyPad source =>
    obtain ⟨hs⟩ := CodeCert.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .familyPad hs.certificate, hs.resources, by simpa only [CodeCert.nativeDepth] using hs.certificateBound⟩⟩
  | .unpad source =>
    obtain ⟨hs⟩ := CodeCert.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .unpad hs.certificate, hs.resources, by simpa only [CodeCert.nativeDepth] using hs.certificateBound⟩⟩
  | .down source =>
    obtain ⟨hs⟩ := CodeCert.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .down hs.certificate, hs.resources, by simpa only [CodeCert.nativeDepth] using hs.certificateBound⟩⟩
  | .map view source =>
    obtain ⟨hs⟩ := CodeCert.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .map view hs.certificate, hs.resources, by simpa only [CodeCert.nativeDepth] using hs.certificateBound⟩⟩
  | .select source member =>
    obtain ⟨hs⟩ := CodeCert.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .select hs.certificate member, hs.resources, by simpa only [CodeCert.nativeDepth] using hs.certificateBound⟩⟩
  | .focusMinimal source minimal focusedBound =>
    obtain ⟨hs⟩ := CodeCert.substitute henv hscoped hΓ source
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed supply
    exact ⟨⟨_, .focusMinimal hs.certificate minimal focusedBound, hs.resources, by simpa only [CodeCert.nativeDepth] using hs.certificateBound⟩⟩
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

theorem PiRows.substitute
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {sourceRealization : Subst} {A B : VExpr}
    {ambient : Profile n} {rows : List (Key n × Profile n)} {required : Footprint}
    (bodies : PiRows env U registry Γ locals sourceRealization A B ambient rows required)
    (depth : bodies.nativeDepth current ≤ fuel)
    (replacement realization : Subst) (realized : replacement.comp realization = sourceRealization)
    (newLocals : List Nat) (available : Valuation) (closed : available.AtomClosed)
    (supply : GradedSupply current fuel env U registry Γ newLocals realization replacement available required) :
    Nonempty (RowsResult current fuel env U registry Γ newLocals realization available
      (A.subst replacement) (B.subst replacement.lift) ambient rows) := by
  match bodies with
  | .nil => exact ⟨⟨[], .nil, (fun _ _ h => nomatch h), by simp only [PiRows.nativeDepth]; exact Nat.zero_le _⟩⟩
  | .cons guard body normal covered tail =>
    obtain ⟨⟨externalSupply⟩, ⟨tailSupply⟩⟩ := supply.split
    let bodyFootprint := certFootprint body
    let head := bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons
    have headClosed := Valuation.push_atomized_closed closed bodyFootprint.localNeeds
    have localCoverage := normal.atomized_localNeeds
    have localLive := (anchor_live henv hscoped hΓ guard.anchor).subset (fun _ hm => covered _ hm)
    obtain ⟨bodySupply⟩ := externalSupply.underBinder normal localLive
      (fun _ hm => List.mem_append_left _ hm) (guardAnchor guard)
    obtain ⟨hb⟩ := CodeCert.substitute henv hscoped hΓ body
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement.lift
      (realization.cons _) (by rw [replacement_lift, realized]; rfl)
      (Locals.push newLocals) (Valuation.push head available) headClosed bodySupply
    obtain ⟨packed, outside, normal', covered', resources⟩ :=
      Footprint.pack_available hb.resources (fun need hm => (localCoverage need hm).1)
        (fun need hm atom ha => covered atom ((localCoverage need hm).2 atom ha))
    obtain ⟨ht⟩ := PiRows.substitute henv hscoped hΓ tail
      (by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] at depth; omega) replacement realization realized
      newLocals available closed tailSupply
    exact ⟨⟨_, .cons (guard.sourceSubstitute replacement realization realized)
      hb.certificate normal' covered' ht.bodies, append_available resources ht.resources, by
        simpa only [PiRows.nativeDepth] using Nat.max_le.mpr ⟨hb.certificateBound, ht.bodiesBound⟩⟩⟩
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega
end

end Lean4Lean.AnchoredSource.Adapted.Staged.Substitution
