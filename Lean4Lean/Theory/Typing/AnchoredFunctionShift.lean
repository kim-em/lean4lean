import Lean4Lean.Theory.Typing.AnchoredRankShift

/-! Raise a function demand while keeping a fixed finite type cover across
future worlds. This is the function side of the padding/eta commuting step. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

theorem Related.rankShift_fn
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 1)} (henv : env.Ordered)
    (H : Related env U registry Γ left right type (.fn key output) typeProfile) :
    Related env U registry Γ left right type
      (.fn key.pad (.pad output)) typeProfile.rankShift := by
  intro atom ha Δ ρ W
  have he : atom = .fn key.pad (.pad output) := List.mem_singleton.mp ha
  subst atom
  have old := H _ (List.mem_singleton_self _) Δ ρ W
  rcases old with hempty | ⟨Ω, τ, I, htyped, htype, hterms⟩
  · cases hempty
  · have oldBehavior := hterms _ (List.mem_singleton_self _)
    obtain ⟨A, B, domain, rows, hmem, behavior⟩ :=
      FunctionBehavior.rankShift henv oldBehavior
    change (Profile.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ)).HasType
      ((typeProfile.rename ρ).rename τ) at htyped
    have newTyped := htyped.rankShiftFn
    have newCode := TypeRelated.rankShift henv htype
    have newBehavior : FunctionBehavior env U registry (relations env U registry (n + 1))
        Ω ((left.lift' ρ).lift' τ) ((right.lift' ρ).lift' τ)
        ((type.lift' ρ).lift' τ)
        ((key.rename ρ).rename τ).pad (.pad ((output.rename ρ).rename τ))
        ((typeProfile.rename ρ).rename τ).rankShift := by
      obtain ⟨anchor, A', B', domain', rows', result, hm, hr, ht, display, behavior⟩ := behavior
      refine ⟨anchor, A', B', domain', rows', result, ?_, hr, ht, display, behavior⟩
      have he := List.mem_singleton.mp hm
      rw [he]
      exact List.mem_map.mpr ⟨.pi A B domain rows, hmem, rfl⟩
    right
    refine ⟨Ω, τ, I, ?_, ?_, ?_⟩
    · change (Profile.fn ((key.pad.rename ρ).rename τ)
        (.pad ((output.rename ρ).rename τ))).HasType _
      simpa only [Key.pad_rename, Profile.rankShift_rename] using newTyped
    · change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
        ((type.lift' ρ).lift' τ) ((typeProfile.rankShift.rename ρ).rename τ)
      simpa only [Profile.rankShift_rename] using newCode
    · intro requested hr
      have he : requested =
          .fn ((key.rename ρ).rename τ).pad (.pad ((output.rename ρ).rename τ)) := by
        have e := List.mem_singleton.mp hr
        change requested = .fn ((key.pad.rename ρ).rename τ)
          (.pad ((output.rename ρ).rename τ)) at e
        simpa only [← Key.pad_rename] using e
      subst requested
      change FunctionBehavior env U registry (relations env U registry (n + 1))
        Ω ((left.lift' ρ).lift' τ) ((right.lift' ρ).lift' τ)
        ((type.lift' ρ).lift' τ) ((key.rename ρ).rename τ).pad
        (.pad ((output.rename ρ).rename τ)) ((typeProfile.rankShift.rename ρ).rename τ)
      simpa only [Profile.rankShift_rename] using newBehavior

/-- A padded existing function row can be used as a row whose input and
output are padded. The new type support is computed from the old support;
no new source observation or semantic bridge is assumed. -/
theorem Related.commute_pad_fn
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right type : VExpr} {key : Key n} {output : Atom n}
    {typeProfile : Profile (n + 2)} (henv : env.Ordered)
    (hΓ : OnCtx Γ (env.IsType U))
    (H : Related env U registry Γ left right type (Profile.fn key output).pad typeProfile) :
    Related env U registry Γ left right type
      (.fn key.pad (.pad output)) typeProfile.down.rankShift :=
  Related.rankShift_fn henv (Related.unpad henv hΓ H)

end Lean4Lean.AnchoredSemantics
