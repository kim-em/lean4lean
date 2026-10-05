import Lean4Lean.Theory.Typing.AnchoredFunctionRetag
import Lean4Lean.Theory.Typing.AnchoredPadding

/-! Changing the type support of a fixed finite value demand. The function
case compares actual canonical displays and recurses on the atomic output's
rank. No observation of a source term is a premise of this target theorem. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

/-- A fixed value demand has the same behavior at every supported type
profile of the same raw type. Domain support is therefore free to live in
the typing witness instead of becoming part of the function's value key. -/
theorem Related.retag {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {value oldTypeProfile newTypeProfile : Profile n}
    (htyped : value.HasType newTypeProfile)
    (hnew : TypeRelated env U registry Γ type type newTypeProfile)
    (hold : Related env U registry Γ left right type value oldTypeProfile) :
    Related env U registry Γ left right type value newTypeProfile := by
  induction n generalizing Γ left right type with
  | zero =>
    intro requested hr
    have htyped := htyped.singleton_of_mem hr
    have hold := hold requested hr
    intro Δ ρ W
    rcases hold Δ ρ W with hempty | ⟨Ω, τ, I, _, _, hvalue⟩
    · exact .inl hempty
    · refine .inr ⟨Ω, τ, I, ?_, ?_, hvalue⟩
      · exact Profile.rename_hasType_iff.mpr (Profile.rename_hasType_iff.mpr htyped)
      · exact TypeRelated.future henv I.toFuture (TypeRelated.future henv W hnew)
  | succ n ih =>
    intro requested hr
    have htyped := htyped.singleton_of_mem hr
    have hold := hold requested hr
    intro Δ ρ W
    rcases hold Δ ρ W with hempty | ⟨Ω, τ, I, _, _, hvalue⟩
    · exact .inl hempty
    · have htyped' := (Profile.rename_hasType_iff (ρ := τ)).mpr
        ((Profile.rename_hasType_iff (ρ := ρ)).mpr htyped)
      have hnew' := TypeRelated.future henv I.toFuture (TypeRelated.future henv W hnew)
      refine .inr ⟨Ω, τ, I, htyped', hnew', ?_⟩
      intro atom ha
      have hv := hvalue atom ha
      cases atom with
      | sort | pi | family | ctor | record => exact hv
      | fn key output =>
        apply FunctionBehavior.retag henv (fun Γ a b A p d d0 _ hp0 _ hc0 hr =>
          ih hp0 hc0 hr) hnew' (htyped'.singleton_of_mem ha) hv
      | pad lowerAtom =>
        have hp : (Profile.singleton lowerAtom).HasType
            (((newTypeProfile.rename ρ).rename τ).down) :=
          Profile.HasType.pad_inv (by
            simpa only [Profile.pad_singleton] using htyped'.singleton_of_mem ha)
        exact ih hp (TypeRelated.down henv hnew') hv

end Lean4Lean.AnchoredSemantics
