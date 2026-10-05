import Lean4Lean.Theory.Typing.AnchoredAtomAction

/-! Hereditary function-output actions use the actual private Pi displays
and original admissions. All support maps are computed by finite syntax. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

theorem FunctionBehavior.outputAction
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lowerTerm : ∀ {Δ} {a b : Atom n} (action : AtomAction env U registry Δ a b)
      {left right type : VExpr} {profile : Profile n},
      OnCtx Δ (env.IsType U) → (Profile.singleton a).HasType profile →
      Related env U registry Δ left right type (.singleton a) profile →
      Related env U registry Δ left right type (.singleton b) (action.support.apply profile))
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output output' : Atom n}
    {profile : Profile (n + 1)} (action : AtomAction env U registry Γ output output')
    (h : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output' (outputTypes key action.support.apply profile) := by
  obtain ⟨seed, A, B, domain, rows, result, hmem, hrow, typed, display, behavior⟩ := h
  refine ⟨seed, A, B, domain, outputRows key action.support.apply rows, action.support.apply result,
    List.mem_map.mpr ⟨_, hmem, rfl⟩, outputRows.changed hrow, action.typed typed,
    display.outputSupport henv (fun {_} a {_ _ _} h => a.codeMap henv hscoped h) action.support, ?_⟩
  intro Δ ρ future x y admitted
  have insertion := display.leftExposure.insertion henv
  let action' := (action.mixed henv insertion).future henv future
  obtain ⟨hl, hr, hc⟩ := behavior Δ ρ future x y admitted
  simp only [Atom.rename_comp] at hl hr hc
  have shiftedTyped := (Profile.rename_hasType_iff (ρ := ρ)).mpr
    ((Profile.rename_hasType_iff (ρ := display.map)).mpr typed)
  simp only [Profile.rename_singleton, ← Profile.rename_comp] at shiftedTyped
  have hl' := lowerTerm action' (future.targetWF henv) shiftedTyped hl
  have hr' := lowerTerm action' (future.targetWF henv) shiftedTyped hr
  have hc' := lowerTerm action' (future.targetWF henv) shiftedTyped hc
  simpa only [action', AtomAction.support_future, AtomAction.support_mixed,
    Profile.rename_comp, ← SupportAction.apply_future, ← SupportAction.apply_mixed,
    Atom.rename_comp, Related, PiWitness.outputSupport] using And.intro hl' (And.intro hr' hc')

theorem Related.outputAction
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (lowerTerm : ∀ {Δ} {a b : Atom n} (action : AtomAction env U registry Δ a b)
      {left right type : VExpr} {profile : Profile n},
      OnCtx Δ (env.IsType U) → (Profile.singleton a).HasType profile →
      Related env U registry Δ left right type (.singleton a) profile →
      Related env U registry Δ left right type (.singleton b) (action.support.apply profile))
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output output' : Atom n}
    {profile : Profile (n + 1)}
    (action : AtomAction env U registry Γ output output')
    (h : Related env U registry Γ left right type (Profile.fn key output) profile) :
    Related env U registry Γ left right type
      (Profile.fn key output') (outputTypes key action.support.apply profile) := by
  intro requested hrequested Δ ρ future
  cases List.mem_singleton.mp hrequested
  have hs := h (.fn key output) (List.mem_singleton_self _) Δ ρ future
  rcases hs with hempty | ⟨Ω, τ, insertion, typed, code, values⟩
  · cases hempty
  · let action' := (action.future henv future).future henv insertion.toFuture
    change (Profile.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ)).HasType
      ((profile.rename ρ).rename τ) at typed
    change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
      ((type.lift' ρ).lift' τ) ((profile.rename ρ).rename τ) at code
    have newTyped := (AtomAction.fn ((key.rename ρ).rename τ) action').typed typed
    have newCode := code.outputSupportWith henv
      (fun {_} a {_ _ _} h => a.codeMap henv hscoped h) (key := (key.rename ρ).rename τ) action'.support
    have behavior := values (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
      (List.mem_singleton_self _)
    have newBehavior := FunctionBehavior.outputAction henv hscoped lowerTerm action' behavior
    have hmap : ((outputTypes key action.support.apply profile).rename ρ).rename τ =
        outputTypes ((key.rename ρ).rename τ) action'.support.apply ((profile.rename ρ).rename τ) := by
      simp only [action', AtomAction.support_future]
      rw [outputTypes_rename key action.support.apply (action.support.future henv future).apply
        (fun p => action.support.apply_future henv future p)]
      exact outputTypes_rename (key.rename ρ) _ _
        (fun p => (action.support.future henv future).apply_future henv insertion.toFuture p) _
    right
    refine ⟨Ω, τ, insertion, ?_, ?_, ?_⟩
    · simpa only [AtomAction.support, SupportAction.apply, Profile.fn,
        Profile.rename_singleton, Atom.rename_fn, hmap] using newTyped
    · change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
        ((type.lift' ρ).lift' τ)
        (((outputTypes key action.support.apply profile).rename ρ).rename τ)
      exact hmap ▸ newCode
    · intro atom ha
      cases List.mem_singleton.mp ha
      simpa only [hmap, Atom.rename_fn, TermAtom] using newBehavior

theorem AtomAction.termMap
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (hΓ : OnCtx Γ (env.IsType U))
    (typed : (Profile.singleton a).HasType profile)
    (related : Related env U registry Γ left right type (.singleton a) profile) :
    Related env U registry Γ left right type (.singleton b) (action.support.apply profile) := by
  match n, a, b, action with
  | _, _, _, .view v => exact v.termMap henv hscoped hΓ related
  | _, _, _, .code leaf formed =>
    exact leaf.termMap henv hscoped hΓ formed typed
      (related.typeCode henv hscoped hΓ (by intro h; cases h)) related
  | _ + 1, _, _, .fn key child =>
    exact related.outputAction henv hscoped
      (fun {_ _ _} action {_ _ _ _} hΔ typed related => action.termMap henv hscoped hΔ typed related) child
  | _ + 1, _, _, .pad child =>
    change (Profile.singleton _).pad.HasType _ at typed
    change Related env U registry Γ left right type (Profile.singleton _).pad profile at related
    exact (child.termMap henv hscoped hΓ typed.pad_inv (Related.unpad henv hΓ related)).pad henv
  | _, _, _, .comp first second =>
    exact second.termMap henv hscoped hΓ (first.typed typed) (first.termMap henv hscoped hΓ typed related)
termination_by (n, sizeOf action)
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSemantics
