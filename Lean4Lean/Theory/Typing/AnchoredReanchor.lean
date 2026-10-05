import Lean4Lean.Theory.Typing.AnchoredViewTyping

/-! Concrete reanchoring of a function row and all covering Pi capabilities.
The seed is actual admission evidence; copied rows recover old admission by
prepending that seed. Existing rows and all output supports are retained. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

private theorem exposureInsertion {Γ Δ : List VExpr} {e head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (E : Exposure env U registry Γ e Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := E.insertion henv

/-- Reanchor only matching rows, preserving both actual displayed endpoints. -/
def PiWitness.reanchor
    {Γ : List VExpr} {left right A B anchor : VExpr} {key : Key n}
    {domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (seed : Admitted env U registry Γ key anchor anchor)
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) :
    PiWitness env U registry (relations env U registry n)
      Γ left right A B domain (reanchorRows key (reanchorKey key anchor) rows) := by
  refine { display with rowDomains := ?_, rowBodies := ?_ }
  · intro k result hm
    rcases mem_reanchorRows.mp hm with old | ⟨rfl, old⟩
    · exact display.rowDomains k result old
    · exact display.rowDomains key result old
  · intro k result hm Δ ρ future x y admitted
    rcases mem_reanchorRows.mp hm with old | ⟨rfl, old⟩
    · exact display.rowBodies k result old Δ ρ future x y admitted
    · have seed' := Admitted.future henv future ((exposureInsertion henv display.leftExposure).admitted henv seed)
      simp only [← lift'_comp, ← Key.rename_comp] at seed'
      have oldAdmission := Admitted.prepend_anchor henv hscoped seed' admitted
      exact display.rowBodies key result old Δ ρ future x y oldAdmission

/-- Every mapped Pi atom has all old rows and the justified reanchored copies. -/
theorem TypeRelated.reanchor
    {Γ : List VExpr} {left right anchor : VExpr} {key : Key n}
    {profile : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (seed : Admitted env U registry Γ key anchor anchor)
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right
      (reanchorTypes key (reanchorKey key anchor) profile) := by
  intro Δ ρ future atom ha
  rw [reanchorTypes_rename] at ha
  obtain ⟨oldAtom, hm, rfl⟩ := List.mem_map.mp ha
  have hc := h Δ ρ future oldAtom hm
  cases oldAtom with
  | sort relevant => exact hc
  | family _ | ctor _ | record _ => exact hc
  | fn k output => exact False.elim hc
  | pad lowerAtom => exact hc
  | pi A B domain rows =>
    obtain ⟨display⟩ := hc
    exact ⟨display.reanchor henv hscoped (Admitted.future henv future seed)⟩

/-- The newly frozen anchor carries its own admission evidence. -/
theorem FunctionBehavior.reanchor
    {Γ : List VExpr} {left right type anchor : VExpr} {key : Key n} {output : Atom n}
    {profile : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (seed : Admitted env U registry Γ key anchor anchor)
    (h : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type (reanchorKey key anchor) output
      (reanchorTypes key (reanchorKey key anchor) profile) := by
  obtain ⟨_, A, B, domain, rows, result, hmem, hrow, typed, display, behavior⟩ := h
  refine ⟨seed.reset_anchor, A, B, domain, reanchorRows key (reanchorKey key anchor) rows,
    result, List.mem_map.mpr ⟨_, hmem, rfl⟩, reanchorRows.changed hrow, typed,
    display.reanchor henv hscoped seed, ?_⟩
  intro Δ ρ future x y admitted
  have seed' := Admitted.future henv future ((exposureInsertion henv display.leftExposure).admitted henv seed)
  simp only [← lift'_comp, ← Key.rename_comp] at seed'
  exact behavior Δ ρ future x y (Admitted.prepend_anchor henv hscoped seed' admitted)

/-- Reanchor a whole saturated atomic function observation. The concrete
support map is fixed before any future context or admitted argument. -/
theorem Related.reanchor
    {Γ : List VExpr} {left right type anchor : VExpr} {key : Key n} {output : Atom n}
    {profile : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (seed : Admitted env U registry Γ key anchor anchor)
    (h : Related env U registry Γ left right type (Profile.fn key output) profile) :
    Related env U registry Γ left right type
      (Profile.fn (reanchorKey key anchor) output)
      (reanchorTypes key (reanchorKey key anchor) profile) := by
  intro requested hrequested Δ ρ future
  cases List.mem_singleton.mp hrequested
  have hs := h (.fn key output) (List.mem_singleton_self _) Δ ρ future
  rcases hs with hempty | ⟨Ω, τ, insertion, typed, code, values⟩
  · cases hempty
  · have seed' := Admitted.future henv insertion.toFuture (Admitted.future henv future seed)
    change (Profile.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ)).HasType
      ((profile.rename ρ).rename τ) at typed
    change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
      ((type.lift' ρ).lift' τ) ((profile.rename ρ).rename τ) at code
    have newTyped := AtomView.mapType_typed (AtomView.reanchor seed') typed
    have newCode := TypeRelated.reanchor henv hscoped seed' code
    have behavior := values (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
      (List.mem_singleton_self _)
    have newBehavior := FunctionBehavior.reanchor henv hscoped seed' behavior
    right
    refine ⟨Ω, τ, insertion, ?_, ?_, ?_⟩
    · simpa only [AtomView.mapType, reanchorTypes_rename, Profile.fn,
        Profile.rename_singleton, Atom.rename_fn, reanchorKey, Key.rename] using newTyped
    · change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
        ((type.lift' ρ).lift' τ)
        (((reanchorTypes key (reanchorKey key anchor) profile).rename ρ).rename τ)
      simpa only [reanchorTypes_rename, reanchorKey, Key.rename] using newCode
    · intro atom ha
      cases List.mem_singleton.mp ha
      simpa only [reanchorTypes_rename, reanchorKey, Key.rename, Atom.rename_fn,
        TermAtom] using newBehavior

end Lean4Lean.AnchoredSemantics
