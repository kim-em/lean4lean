import Lean4Lean.Theory.Typing.AnchoredFunctionConversion

/-! Conversion of concrete term evidence across related raw types. The
value demand remains fixed; only its type and finite type support change.
The function case decreases the observation rank. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem Related.convert
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {value oldTypeProfile newTypeProfile : Profile n}
    (htyped : value.HasType newTypeProfile)
    (hbridge : TypeRelated env U registry Γ oldType newType newTypeProfile)
    (hold : Related env U registry Γ left right oldType value oldTypeProfile) :
    Related env U registry Γ left right newType value newTypeProfile := by
  induction n generalizing Γ left right oldType newType with
  | zero =>
    intro requested hr
    have htyped := htyped.singleton_of_mem hr
    intro Δ ρ W
    rcases hold requested hr Δ ρ W with hempty | ⟨Ω, τ, I, _, _, hvalue⟩
    · exact .inl hempty
    · have htyped' := (Profile.rename_hasType_iff (ρ := τ)).mpr
        ((Profile.rename_hasType_iff (ρ := ρ)).mpr htyped)
      have hbridge' := TypeRelated.future henv I.toFuture (TypeRelated.future henv W hbridge)
      exact .inr ⟨Ω, τ, I, htyped',
        (hbridge'.symm henv htyped'.wf_type).left_diagonal, hvalue⟩
  | succ n ih =>
    intro requested hr
    have htyped := htyped.singleton_of_mem hr
    intro Δ ρ W
    rcases hold requested hr Δ ρ W with hempty | ⟨Ω, τ, I, _, _, hvalue⟩
    · exact .inl hempty
    · have htyped' := (Profile.rename_hasType_iff (ρ := τ)).mpr
        ((Profile.rename_hasType_iff (ρ := ρ)).mpr htyped)
      have hbridge' := TypeRelated.future henv I.toFuture (TypeRelated.future henv W hbridge)
      refine .inr ⟨Ω, τ, I, htyped',
        (hbridge'.symm henv htyped'.wf_type).left_diagonal, ?_⟩
      intro atom ha
      have hv := hvalue atom ha
      cases atom with
      | sort relevant => exact hv
      | pi A B domain rows => exact hv
      | family data => exact hv
      | ctor data =>
        have member := (htyped'.singleton_of_mem ha).ctor_family_mem
        have bridge : RankedData.FamilyRelation env U registry (relations env U registry n)
            Ω (oldType.lift' (ρ.comp τ)) (newType.lift' (ρ.comp τ)) data.family := by
          intro Ξ i future
          simpa only [← lift'_comp, Atom.rename_family, FamilyData.rename, CodeAtom] using
            hbridge' Ξ i future _ (List.mem_map.mpr ⟨_, member, rfl⟩)
        exact RankedData.ConstructorRelation.convert henv ((rankLaws henv n).lowerEquality henv) hv
          (by simpa only [← lift'_comp] using bridge)
      | record data =>
        have member := (htyped'.singleton_of_mem ha).record_family_mem
        have bridge : RankedData.FamilyRelation env U registry (relations env U registry n)
            Ω (oldType.lift' (ρ.comp τ)) (newType.lift' (ρ.comp τ)) data.family := by
          intro Ξ i future
          simpa only [← lift'_comp, Atom.rename_family, FamilyData.rename, CodeAtom] using
            hbridge' Ξ i future _ (List.mem_map.mpr ⟨_, member, rfl⟩)
        exact RankedData.RecordRelation.convert henv ((rankLaws henv n).lowerEquality henv) hv
          (by simpa only [← lift'_comp] using bridge)
      | fn key output =>
        exact FunctionBehavior.convert henv (fun Γ l r A B p oldD newD ht hb h =>
          ih ht hb h) (htyped'.singleton_of_mem ha) hbridge' hv
      | pad lowerAtom =>
        have hp : (Profile.singleton lowerAtom).HasType
            (((newTypeProfile.rename ρ).rename τ).down) :=
          Profile.HasType.pad_inv (by
            simpa only [Profile.pad_singleton] using htyped'.singleton_of_mem ha)
        exact ih hp (TypeRelated.down henv hbridge') hv

/-- Change the raw domain stored in a frozen key using explicit raw and
semantic conversion evidence. Its anchor and input demand stay fixed. -/
theorem Admitted.rekey
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {key : Key n} {left right newDomain : VExpr}
    {newSupport : Profile n}
    (henv : env.Ordered)
    (path : TypeConversion env U Γ key.domain newDomain)
    (typed : key.input.HasType newSupport)
    (formation : newSupport.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ key.domain newDomain newSupport)
    (h : Admitted env U registry Γ key left right) :
    Admitted env U registry Γ { key with domain := newDomain } left right := by
  obtain ⟨anchor, pair, oldSupport, _, _, _, first, second⟩ := h
  exact ⟨path.cast anchor, path.cast pair, newSupport, typed, formation,
    (bridge.symm henv typed.wf_type).left_diagonal,
    Related.convert henv typed bridge first, Related.convert henv typed bridge second⟩

end Lean4Lean.AnchoredSemantics
