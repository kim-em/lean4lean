import Lean4Lean.Theory.Typing.AnchoredPadding

/-! Sortable code observations are also term observations at any genuine
assigned-type capability which intrinsically types the demand. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem Related.of_code
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {Γ : List VExpr} {left right type : VExpr}
    {value typeProfile : Profile n}
    (sortable : value.HasType (.sort true))
    (typed : value.HasType typeProfile)
    (valueCode : TypeRelated env U registry Γ left right value)
    (typeCode : TypeRelated env U registry Γ type type typeProfile) :
    Related env U registry Γ left right type value typeProfile := by
  induction n generalizing Γ left right type with
  | zero =>
    intro atom member Δ ρ future
    have ht := (Profile.rename_hasType_iff (ρ := ρ)).mpr (typed.singleton_of_mem member)
    have hc := typeCode.future henv future
    have hv := (valueCode.singleton member).future henv future
    refine .inr ⟨Δ, .refl, .refl (future.targetWF henv), ?_⟩
    simp only [lift'_refl, Profile.rename_refl]
    exact ⟨ht, hc, hv⟩
  | succ n ih =>
    intro atom member Δ ρ future
    have ht := (Profile.rename_hasType_iff (ρ := ρ)).mpr (typed.singleton_of_mem member)
    have hs := (Profile.rename_hasType_iff (ρ := ρ)).mpr (sortable.singleton_of_mem member)
    rw [Profile.rename_sort] at hs
    have hc := typeCode.future henv future
    have hv := (valueCode.singleton member).future henv future
    refine .inr ⟨Δ, .refl, .refl (future.targetWF henv), ?_⟩
    simp only [lift'_refl, Profile.rename_refl]
    refine ⟨ht, hc, ?_⟩
    intro actual hm
    have he : actual = atom.rename ρ := List.mem_singleton.mp hm
    subst actual
    cases atom with
    | sort | pi | family => exact hv
    | fn | ctor | record =>
      obtain ⟨cover, hm, impossible⟩ := hs.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp hm
      contradiction
    | pad lower =>
      rw [← Profile.pad_singleton, ← Profile.pad_rename, Profile.rename_singleton] at ht hs hv
      have hlow : (Profile.singleton (lower.rename ρ)).HasType (.sort true) := by
        simpa only [Profile.down_sort] using hs.pad_inv
      exact ih hlow ht.pad_inv ((TypeRelated.pad_iff henv).mp hv) (hc.down henv)

end Lean4Lean.AnchoredSemantics
