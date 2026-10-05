import Lean4Lean.Theory.Typing.AnchoredFramedFunctionSeed

/-! A function's observed output retains a type support from the base
profile even though its actual codomain may use a private display context. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem row_output_origin {profile : Profile (n + 1)} {ρ : Lift}
    {A B : VExpr} {domain result : Profile n} {rows : List (Key n × Profile n)}
    {key : Key n}
    (cover : (AtomData.pi A B domain rows : Atom (n + 1)) ∈ (profile.rename ρ).atoms)
    (row : (key, result) ∈ rows) :
    ∃ base : Profile n, result = base.rename ρ := by
  obtain ⟨origin, _, same⟩ := List.mem_map.mp cover
  cases origin with
  | sort | fn | pad | family | ctor | record => cases same
  | pi a b d rs =>
    simp only [Atom.rename_pi] at same
    cases same
    obtain ⟨⟨k, r⟩, _, sameRow⟩ := List.mem_map.mp row
    exact ⟨r, (Prod.mk.inj sameRow).2.symm⟩


theorem Related.fn_output_inFrame
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} {left right type : VExpr}
    {key : Key n} {output : Atom n} {support : Profile (n + 1)}
    (henv : env.Ordered)
    (frame : ProofInsertion env U Γ Δ ρ)
    (related : Related env U registry Δ left right type
      (Profile.fn (key.rename ρ) (output.rename ρ)) (support.rename ρ)) :
    ∃ Ω τ, ProofInsertion env U Γ Ω τ ∧ ∃ l r A, ∃ result : Profile n,
      Related env U registry Ω l r A (.singleton (output.rename τ)) (result.rename τ) := by
  have original := related (.fn (key.rename ρ) (output.rename ρ))
    (List.mem_singleton_self _) Δ .refl (.refl (frame.targetWF henv))
  simp only [lift'_refl, Profile.rename_refl] at original
  rcases original with empty | ⟨Ω, τ, insertion, _, _, values⟩
  · cases empty
  · have behavior := values (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
      (List.mem_singleton_self _)
    obtain ⟨seed, A, B, domain, rows, result, cover, row, _, display, applyRow⟩ := behavior
    obtain ⟨baseResult, result_eq⟩ := row_output_origin
      (ρ := ρ.comp τ) (by simpa only [Profile.rename_comp] using cover) row
    have localFrame := display.leftExposure.generated.comp display.leftExposure.post henv
    have admitted := (display.leftExposure.insertion henv).admitted henv seed
    have outputs := applyRow display.context .refl (.refl (display.leftExposure.targetWF henv))
      ((((key.rename ρ).rename τ).anchor).lift' display.map)
      ((((key.rename ρ).rename τ).anchor).lift' display.map) (by
        simpa only [Lift.comp, Admitted] using admitted)
    have full : ProofInsertion env U Γ display.leftExposure.postContext
        ((ρ.comp τ).comp display.map) := by
      simpa only [display.leftExposure.map_eq] using
        (frame.comp insertion henv).comp localFrame henv
    have output := (display.leftExposure.terminal.symm henv).term henv outputs.1
    let arg := (((key.rename ρ).rename τ).anchor).lift' display.map
    let value := VExpr.app ((left.lift' τ).lift' display.map) arg
    refine ⟨_, _, full, value, value, (display.leftBody.lift' Lift.refl.cons).inst arg,
      baseResult, ?_⟩
    simpa only [value, arg, Lift.comp, result_eq, ← Profile.rename_comp, ← Atom.rename_comp,
      Related] using output

end Lean4Lean.AnchoredSemantics
