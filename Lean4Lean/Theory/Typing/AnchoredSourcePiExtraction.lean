import Lean4Lean.Theory.Typing.AnchoredSourceSubstitution

/-! Actual source provenance for an input-transformed Pi row.
This is the difficult local operation of Pi certificate extraction: replace
old local certificate demands using the concrete forward source views, while
retaining the actual codomain expression, anchor, result profile, and fixed
external valuation. It does not assert arbitrary Pi-certificate extraction.
-/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private def inputNeeds (input : Profile n) : List Need :=
  [⟨n, input⟩] ++ ([⟨n, input⟩] : List Need).flatMap Need.singletons

private def inputFootprint (input : Profile n) : Footprint :=
  input.map fun atom => (0, ⟨n, .singleton atom⟩)

/-- Replay each actual atomic source view at the bound variable. Every source
atom remains a literal variable demand; no semantic observation is invented. -/
private def variableView
    (view : ProfileView env U registry target input output)
    (locals : List Nat) (realization : Subst) :
    Obs env U registry target locals realization (.bvar 0) output
      (inputFootprint input) := by
  match input, output, view with
  | _, _, .nil => exact .empty
  | _, _, .cons head tail =>
    exact .union (.view (.var locals realization 0 _) head)
      (variableView tail locals realization)
termination_by sizeOf view

private theorem inputFootprint_available (input : Profile n) (available : Valuation) :
    (inputFootprint input).Available (Valuation.push (inputNeeds input) available) := by
  intro index need member
  obtain ⟨atom, atomMember, equality⟩ := List.mem_map.mp member
  cases equality
  apply List.mem_append_right
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact List.mem_map.mpr ⟨atom, atomMember, rfl⟩

private theorem inputNeeds_bounded (input : Profile n) :
    ∀ need ∈ inputNeeds input,
      need.rank ≤ n ∧ ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms := by
  intro need member
  rcases List.mem_append.mp member with whole | singleton
  · cases List.mem_singleton.mp whole
    exact ⟨Nat.le_refl n, by simp [Need.atGrade]⟩
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at singleton
    obtain ⟨atom, atomMember, equality⟩ := List.mem_map.mp singleton
    cases equality
    refine ⟨Nat.le_refl n, ?_⟩
    intro other belongs
    have equal : other = atom := by
      simpa [Need.atGrade, Profile.atoms, Profile.singleton, Profile.mk] using belongs
    exact equal ▸ atomMember

/-- Identity substitution changes only how the original local leaves are
observed. In particular an active application keeps its whole argument. -/
private theorem SourceSupply.rebindInput
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {input output packed : Profile n}
    {required outside : Footprint}
    (view : ProfileView env U registry target input output)
    (normal : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ output.atoms)
    (resources : outside.Available available)
    (closed : available.AtomClosed) :
    ∃ footprint,
      Nonempty (SourceSupply env U registry target locals realization Subst.id required footprint) ∧
      footprint.Available (Valuation.push (inputNeeds input) available) := by
  have localClosed := Valuation.push_atomized_closed closed [⟨n, input⟩]
  induction normal with
  | nil => exact ⟨[], ⟨.nil⟩, fun _ _ member => nomatch member⟩
  | «local» need bound rest ih =>
    obtain ⟨headFootprint, ⟨headObservation⟩, headSelection⟩ :=
      (variableView view locals realization).localDemand need bound
        (fun atom member => covered atom (List.mem_append_left _ member))
    obtain ⟨tailFootprint, ⟨tailSupply⟩, tailAvailable⟩ :=
      ih (fun atom member => covered atom (List.mem_append_right _ member)) resources
    refine ⟨headFootprint ++ tailFootprint, ⟨.cons headObservation tailSupply⟩, ?_⟩
    have headAvailable := headSelection.available_closed
      (inputFootprint_available input available) localClosed
    intro index demand member
    exact (List.mem_append.mp member).elim
      (headAvailable index demand) (tailAvailable index demand)
  | external index need rest ih =>
    obtain ⟨tailFootprint, ⟨tailSupply⟩, tailAvailable⟩ :=
      ih covered (fun i demand member => resources i demand (List.mem_cons_of_mem _ member))
    refine ⟨(index + 1, need) :: tailFootprint,
      ⟨.cons (.var locals realization (index + 1) need.profile) tailSupply⟩, ?_⟩
    intro i demand member
    rcases List.mem_cons.mp member with equality | member
    · cases equality
      exact resources index need List.mem_cons_self
    · exact tailAvailable i demand member

/-- Rebind the actual source codomain certificate along the forward input
view. The result is still a certificate of `B`, at the same realization and
result support; its local demands are literally covered by the new input. -/
theorem CodeCert.rebind_input
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {B : VExpr} {input oldInput packed : Profile n}
    {result : Profile m} {required outside : Footprint}
    (certificate : CodeCert env U registry target locals realization B result required)
    (view : ProfileView env U registry target input oldInput)
    (normal : BinderPack n packed required outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ oldInput.atoms)
    (resources : outside.Available available)
    (closed : available.AtomClosed) :
    ∃ footprint externalFootprint newPacked,
      Nonempty (CodeCert env U registry target locals realization B result footprint) ∧
      BinderPack n newPacked footprint externalFootprint ∧
      (∀ atom ∈ newPacked.atoms, atom ∈ input.atoms) ∧
      externalFootprint.Available available := by
  obtain ⟨footprint, ⟨supply⟩, available⟩ :=
    SourceSupply.rebindInput view normal covered resources closed
  obtain ⟨changed⟩ := certificate.substitute Subst.id realization
    (by funext index; rfl) locals supply
  have changed : CodeCert env U registry target locals realization B result footprint := by
    simpa only [subst_id] using changed
  obtain ⟨newPacked, externalFootprint, pack, coverage, externalAvailable⟩ :=
    Footprint.pack_available available
      (fun need member => (inputNeeds_bounded input need member).1)
      (fun need member => (inputNeeds_bounded input need member).2)
  exact ⟨footprint, externalFootprint, newPacked, ⟨changed⟩, pack, coverage, externalAvailable⟩

/-- The domain certificate follows the finite backward support map, rather
than reconstructing the basis supports used by the target Pi profile. -/
theorem CodeCert.map_profile_view
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {A : VExpr} {input output support : Profile n}
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals realization A support footprint)
    (view : ProfileView env U registry target input output)
    (resources : footprint.Available available) :
    ∃ selectedFootprint,
      Nonempty (CodeCert env U registry target locals realization A
        (view.mapType support) selectedFootprint) ∧ selectedFootprint.Available available := by
  match input, output, view with
  | _, _, .nil => exact ⟨footprint, ⟨certificate⟩, resources⟩
  | _, _, .cons head tail =>
    obtain ⟨restFootprint, ⟨rest⟩, restAvailable⟩ :=
      certificate.map_profile_view tail resources
    refine ⟨footprint ++ restFootprint, ⟨.union (.map head certificate) rest⟩, ?_⟩
    intro index need member
    exact (List.mem_append.mp member).elim (resources index need) (restAvailable index need)
termination_by sizeOf view

/-- The complete reduced input-map producer retains actual source A/B
certificates. It changes local provenance syntactically and obtains every
semantic guard by the already closed concrete view interpreter. -/
theorem PiRows.input_map
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {realization : Subst} {available : Valuation}
    {A B : VExpr} {key : Key n} {input support result packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (domain : CodeCert env U registry target locals realization A support domainFootprint)
    (guard : LambdaGuard env U registry target realization A key support)
    (body : CodeCert env U registry target (Locals.push locals)
      (realization.cons key.anchor) B result bodyFootprint)
    (normal : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
    (forward : ProfileView env U registry target input key.input)
    (backward : ProfileView env U registry target key.input input)
    (domainAvailable : domainFootprint.Available available)
    (outsideAvailable : outside.Available available)
    (closed : available.AtomClosed) :
    ∃ newDomainFootprint rowFootprint,
      Nonempty (CodeCert env U registry target locals realization A
        (backward.mapType support) newDomainFootprint) ∧
      Nonempty (PiRows env U registry target locals realization A B
        (backward.mapType support) [(inputKey key input, result)] rowFootprint) ∧
      (newDomainFootprint ++ rowFootprint).Available available := by
  obtain ⟨newDomainFootprint, ⟨newDomain⟩, newDomainAvailable⟩ :=
    domain.map_profile_view backward domainAvailable
  obtain ⟨newBodyFootprint, externalFootprint, newPacked, ⟨newBody⟩,
      newNormal, newCovered, externalAvailable⟩ :=
    body.rebind_input forward normal covered outsideAvailable closed
  have codeMap : ∀ {p q : Profile n} (v : ProfileView env U registry target p q)
      {l r : VExpr} {d : Profile n}, TypeRelated env U registry target l r d →
        TypeRelated env U registry target l r (v.mapType d) := by
    intro p q view l r d code
    exact view.codeMapWith (fun atomView _ _ _ h => atomView.codeMap henv hscoped h) code
  have termMap : ∀ {p q : Profile n} (v : ProfileView env U registry target p q)
      {l r T : VExpr} {d : Profile n}, p.HasType d →
        Related env U registry target l r T p d →
          Related env U registry target l r T q (v.mapType d) := by
    intro p q view l r T d typed related
    exact view.termMapWith henv hscoped hTarget
      (fun atomView _ _ _ h => atomView.codeMap henv hscoped h)
      (fun atomView _ _ _ _ h => atomView.termMap henv hscoped hTarget h) typed related
  have anchor : Admitted env U registry target (inputKey key input) key.anchor key.anchor := by
    obtain ⟨raw, pair, anchorSupport, typed, formed, code, left, right⟩ := guard.anchor
    exact ⟨raw, pair, backward.mapType anchorSupport, backward.mapType_typed typed,
      backward.mapType_sort formed, codeMap backward code,
      termMap backward typed left, termMap backward typed right⟩
  have newGuard : LambdaGuard env U registry target realization A
      (inputKey key input) (backward.mapType support) :=
    ⟨backward.mapType_typed guard.inputTyped, backward.mapType_sort guard.formed,
      guard.path, codeMap backward guard.domains, anchor⟩
  have row := PiRows.cons newGuard newBody newNormal newCovered PiRows.nil
  simp only [List.append_nil] at row
  refine ⟨newDomainFootprint, externalFootprint, ⟨newDomain⟩, ⟨row⟩, ?_⟩
  intro index need member
  exact (List.mem_append.mp member).elim
    (newDomainAvailable index need) (externalAvailable index need)

end Lean4Lean.AnchoredSource
