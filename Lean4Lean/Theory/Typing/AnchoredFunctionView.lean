import Lean4Lean.Theory.Typing.AnchoredViewTyping

/-! Hereditary output views reuse the actual displayed Pi and its admitted
arguments. Only interpretation of the strictly smaller-rank child view is
an induction hypothesis; the finite result-support map is already fixed. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

private theorem exposureInsertion {Γ Δ : List VExpr} {e head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (E : Exposure env U registry Γ e Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := E.insertion henv

def PiWitness.outputView
    (henv : env.Ordered)
    (lowerCode : ∀ {Δ} {a b : Atom n} (view : AtomView env U registry Δ a b)
      {left right : VExpr} {profile : Profile n},
      TypeRelated env U registry Δ left right profile →
      TypeRelated env U registry Δ left right (view.mapType profile))
    {Γ : List VExpr} {left right A B : VExpr} {key : Key n}
    {output output' : Atom n} {domain : Profile n} {rows : List (Key n × Profile n)}
    (view : AtomView env U registry Γ output output')
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) :
    PiWitness env U registry (relations env U registry n)
      Γ left right A B domain (outputRows key view.mapType rows) := by
  refine { display with rowDomains := ?_, rowBodies := ?_ }
  · intro k result hm
    rcases mem_outputRows.mp hm with old | ⟨rfl, oldResult, old, rfl⟩
    · exact display.rowDomains k result old
    · exact display.rowDomains k oldResult old
  · intro k result hm Δ ρ future x y admitted
    rcases mem_outputRows.mp hm with old | ⟨rfl, oldResult, old, rfl⟩
    · exact display.rowBodies k result old Δ ρ future x y admitted
    · have insertion := exposureInsertion henv display.leftExposure
      let view' := (view.mixed henv insertion).future henv future
      obtain ⟨hl, hr, hc⟩ := display.rowBodies k oldResult old Δ ρ future x y admitted
      have hl' := lowerCode view' hl
      have hr' := lowerCode view' hr
      have hc' := lowerCode view' hc
      simpa only [view', Profile.rename_comp, ← AtomView.mapType_future, ← AtomView.mapType_mixed, TypeRelated] using
        And.intro hl' (And.intro hr' hc')

theorem TypeRelated.outputView
    (henv : env.Ordered) (_hscoped : registry.Scoped)
    (lowerCode : ∀ {Δ} {a b : Atom n} (view : AtomView env U registry Δ a b)
      {left right : VExpr} {profile : Profile n},
      TypeRelated env U registry Δ left right profile →
      TypeRelated env U registry Δ left right (view.mapType profile))
    {Γ : List VExpr} {left right : VExpr} {key : Key n} {output output' : Atom n}
    {profile : Profile (n + 1)} (view : AtomView env U registry Γ output output')
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (outputTypes key view.mapType profile) := by
  intro Δ ρ future atom ha
  rw [outputTypes_rename key view.mapType (view.future henv future).mapType
    (fun p => view.mapType_future henv future p)] at ha
  obtain ⟨oldAtom, hm, rfl⟩ := List.mem_map.mp ha
  have hc := h Δ ρ future oldAtom hm
  cases oldAtom with
  | sort relevant => exact hc
  | family _ | ctor _ | record _ => exact hc
  | fn k output => exact False.elim hc
  | pad lowerAtom => exact hc
  | pi A B domain rows =>
    obtain ⟨display⟩ := hc
    exact ⟨display.outputView henv lowerCode (view.future henv future)⟩

theorem FunctionBehavior.outputView
    (henv : env.Ordered)
    (lowerCode : ∀ {Δ} {a b : Atom n} (view : AtomView env U registry Δ a b)
      {left right : VExpr} {profile : Profile n},
      TypeRelated env U registry Δ left right profile →
      TypeRelated env U registry Δ left right (view.mapType profile))
    (lowerTerm : ∀ {Δ} {a b : Atom n} (view : AtomView env U registry Δ a b)
      {left right type : VExpr} {profile : Profile n},
      OnCtx Δ (env.IsType U) →
      Related env U registry Δ left right type (.singleton a) profile →
      Related env U registry Δ left right type (.singleton b) (view.mapType profile))
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output output' : Atom n}
    {profile : Profile (n + 1)} (view : AtomView env U registry Γ output output')
    (h : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output' (outputTypes key view.mapType profile) := by
  obtain ⟨seed, A, B, domain, rows, result, hmem, hrow, typed, display, behavior⟩ := h
  refine ⟨seed, A, B, domain, outputRows key view.mapType rows, view.mapType result,
    List.mem_map.mpr ⟨_, hmem, rfl⟩, outputRows.changed hrow, view.mapType_typed typed,
    display.outputView henv lowerCode view, ?_⟩
  intro Δ ρ future x y admitted
  have insertion := exposureInsertion henv display.leftExposure
  let view' := (view.mixed henv insertion).future henv future
  obtain ⟨hl, hr, hc⟩ := behavior Δ ρ future x y admitted
  simp only [Atom.rename_comp] at hl hr hc
  have hl' := lowerTerm view' (future.targetWF henv) hl
  have hr' := lowerTerm view' (future.targetWF henv) hr
  have hc' := lowerTerm view' (future.targetWF henv) hc
  simpa only [view', Profile.rename_comp, ← AtomView.mapType_future, ← AtomView.mapType_mixed, Atom.rename_comp, Related, PiWitness.outputView] using
    And.intro hl' (And.intro hr' hc')

theorem Related.outputView
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lowerCode : ∀ {Δ} {a b : Atom n} (view : AtomView env U registry Δ a b)
      {left right : VExpr} {profile : Profile n},
      TypeRelated env U registry Δ left right profile →
      TypeRelated env U registry Δ left right (view.mapType profile))
    (lowerTerm : ∀ {Δ} {a b : Atom n} (view : AtomView env U registry Δ a b)
      {left right type : VExpr} {profile : Profile n},
      OnCtx Δ (env.IsType U) →
      Related env U registry Δ left right type (.singleton a) profile →
      Related env U registry Δ left right type (.singleton b) (view.mapType profile))
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output output' : Atom n}
    {profile : Profile (n + 1)} (_hΓ : OnCtx Γ (env.IsType U))
    (view : AtomView env U registry Γ output output')
    (h : Related env U registry Γ left right type (Profile.fn key output) profile) :
    Related env U registry Γ left right type
      (Profile.fn key output') (outputTypes key view.mapType profile) := by
  intro requested hrequested Δ ρ future
  cases List.mem_singleton.mp hrequested
  have hs := h (.fn key output) (List.mem_singleton_self _) Δ ρ future
  rcases hs with hempty | ⟨Ω, τ, insertion, typed, code, values⟩
  · cases hempty
  · let view' := (view.future henv future).future henv insertion.toFuture
    change (Profile.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ)).HasType
      ((profile.rename ρ).rename τ) at typed
    change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
      ((type.lift' ρ).lift' τ) ((profile.rename ρ).rename τ) at code
    have newTyped := AtomView.mapType_typed (AtomView.fn ((key.rename ρ).rename τ) view') typed
    have newCode := TypeRelated.outputView henv hscoped lowerCode
      (key := (key.rename ρ).rename τ) view' code
    have behavior := values (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
      (List.mem_singleton_self _)
    have newBehavior := FunctionBehavior.outputView henv lowerCode lowerTerm view' behavior
    have hmap : ((outputTypes key view.mapType profile).rename ρ).rename τ =
        outputTypes ((key.rename ρ).rename τ) view'.mapType ((profile.rename ρ).rename τ) := by
      rw [outputTypes_rename key view.mapType (view.future henv future).mapType
        (fun p => view.mapType_future henv future p)]
      exact outputTypes_rename (key.rename ρ) _ _
        (fun p => (view.future henv future).mapType_future henv insertion.toFuture p) _
    right
    refine ⟨Ω, τ, insertion, ?_, ?_, ?_⟩
    · simpa only [AtomView.mapType, Profile.fn, Profile.rename_singleton, Atom.rename_fn,
        hmap] using newTyped
    · change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
        ((type.lift' ρ).lift' τ)
        (((outputTypes key view.mapType profile).rename ρ).rename τ)
      exact hmap ▸ newCode
    · intro atom ha
      cases List.mem_singleton.mp ha
      simpa only [hmap, Atom.rename_fn, TermAtom] using newBehavior

end Lean4Lean.AnchoredSemantics
