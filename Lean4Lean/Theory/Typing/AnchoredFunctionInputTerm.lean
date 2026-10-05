import Lean4Lean.Theory.Typing.AnchoredFunctionInput

/-! Function values adapt input demands using the actual paired forward and
backward views. Their outputs and chosen proof display stay unchanged. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

private theorem exposureInsertion {Γ Δ : List VExpr} {e head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (E : Exposure env U registry Γ e Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := E.insertion henv

theorem FunctionBehavior.inputView
    (henv : env.Ordered)
    (lowerCode : ∀ {Δ : List VExpr} {p q : Profile n}
      (v : ProfileView env U registry Δ p q) {l r : VExpr} {d : Profile n},
      TypeRelated env U registry Δ l r d → TypeRelated env U registry Δ l r (v.mapType d))
    (lowerTerm : ∀ {Δ : List VExpr}, OnCtx Δ (env.IsType U) →
      ∀ {p q : Profile n} (v : ProfileView env U registry Δ p q)
      {l r A : VExpr} {d : Profile n}, p.HasType d →
      Related env U registry Δ l r A p d → Related env U registry Δ l r A q (v.mapType d))
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {input : Profile n}
    {output : Atom n} {profile : Profile (n + 1)}
    (forward : ProfileView env U registry Γ input key.input)
    (backward : ProfileView env U registry Γ key.input input)
    (typed : (Profile.fn key output).HasType profile)
    (h : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type (inputKey key input) output
      (inputTypes key input backward.mapType profile) := by
  classical
  obtain ⟨seed, A, B, domain, rows, result, hmem, hrow, ht, display, behavior⟩ := h
  have hw := typed.wf_type _ hmem
  have inputTyped : key.input.HasType domain := (hw.2 key result hrow).1
  have newSeed := backward.admissionMapWith display.leftExposure.generated.baseWF
    lowerCode lowerTerm seed
  refine ⟨newSeed, A, B, inputDomain key.input backward.mapType domain,
    reanchorRows key (inputKey key input) rows, result,
    List.mem_map.mpr ⟨_, hmem, ?_⟩, reanchorRows.changed hrow, ht,
    display.inputView henv lowerCode lowerTerm forward backward inputTyped, ?_⟩
  · simp only [inputTyped, if_pos]
  · intro Δ ρ future x y admitted
    have front : ProfileView env U registry Δ (input.rename (display.map.comp ρ))
        (key.input.rename (display.map.comp ρ)) := by
      simpa only [Profile.rename_comp] using
        (forward.mixed henv (exposureInsertion henv display.leftExposure)).future henv future
    have oldAdmission := front.admissionMapWith (future.targetWF henv)
      lowerCode lowerTerm admitted
    have oldAdmission' : Admitted env U registry Δ (key.rename (display.map.comp ρ)) x y := by
      simpa only [inputKey, Key.rename, PiWitness.inputView] using oldAdmission
    exact behavior Δ ρ future x y oldAdmission'

/-- The selected old core supplies the intrinsic gate for its function row;
no new typing or semantic premise is requested from the caller. -/
theorem Related.inputView
    (henv : env.Ordered)
    (lowerCode : ∀ {Δ : List VExpr} {p q : Profile n}
      (v : ProfileView env U registry Δ p q) {l r : VExpr} {d : Profile n},
      TypeRelated env U registry Δ l r d → TypeRelated env U registry Δ l r (v.mapType d))
    (lowerTerm : ∀ {Δ : List VExpr}, OnCtx Δ (env.IsType U) →
      ∀ {p q : Profile n} (v : ProfileView env U registry Δ p q)
      {l r A : VExpr} {d : Profile n}, p.HasType d →
      Related env U registry Δ l r A p d → Related env U registry Δ l r A q (v.mapType d))
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {input : Profile n}
    {output : Atom n} {profile : Profile (n + 1)}
    (forward : ProfileView env U registry Γ input key.input)
    (backward : ProfileView env U registry Γ key.input input)
    (h : Related env U registry Γ left right type (Profile.fn key output) profile) :
    Related env U registry Γ left right type (Profile.fn (inputKey key input) output)
      (inputTypes key input backward.mapType profile) := by
  intro requested hrequested Δ ρ future
  cases List.mem_singleton.mp hrequested
  have hs := h (.fn key output) (List.mem_singleton_self _) Δ ρ future
  rcases hs with hempty | ⟨Ω, τ, insertion, typed, code, values⟩
  · cases hempty
  · let forward' := (forward.future henv future).future henv insertion.toFuture
    let backward' := (backward.future henv future).future henv insertion.toFuture
    change (Profile.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ)).HasType
      ((profile.rename ρ).rename τ) at typed
    change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
      ((type.lift' ρ).lift' τ) ((profile.rename ρ).rename τ) at code
    have newTyped := inputTypes.typed
      (fun _ h => backward'.mapType_sort h) (fun _ h => backward'.mapType_typed h) typed
    have newCode := TypeRelated.inputView (key := (key.rename ρ).rename τ)
      henv lowerCode lowerTerm forward' backward' code
    have behavior := values (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
      (List.mem_singleton_self _)
    have newBehavior := FunctionBehavior.inputView henv lowerCode lowerTerm
      forward' backward' typed behavior
    have hmap : ((inputTypes key input backward.mapType profile).rename ρ).rename τ =
        inputTypes ((key.rename ρ).rename τ) ((input.rename ρ).rename τ)
          backward'.mapType ((profile.rename ρ).rename τ) := by
      rw [inputTypes.rename key input profile ρ backward.mapType
        (backward.future henv future).mapType (backward.mapType_future henv future)]
      exact inputTypes.rename (key.rename ρ) (input.rename ρ) (profile.rename ρ) τ
        _ _ (fun d => (backward.future henv future).mapType_future henv insertion.toFuture d)
    right
    refine ⟨Ω, τ, insertion, ?_, ?_, ?_⟩
    · simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn, inputKey,
        Key.rename, hmap] using newTyped
    · change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
        ((type.lift' ρ).lift' τ)
        (((inputTypes key input backward.mapType profile).rename ρ).rename τ)
      exact hmap ▸ newCode
    · intro atom ha
      cases List.mem_singleton.mp ha
      simpa only [hmap, Atom.rename_fn, TermAtom, inputKey, Key.rename] using newBehavior

end Lean4Lean.AnchoredSemantics
