import Lean4Lean.Theory.Typing.AnchoredSortComposition
import Lean4Lean.Theory.Typing.AnchoredMinimalPiFocus
import Lean4Lean.Theory.Typing.AnchoredPadding

/-! The finite-rank induction interface for hereditary support transport.
These fields are proof obligations for the rank construction, not additional
premises for the source equality foundation. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

structure SupportLaws (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (n : Nat) : Prop where
  symm : ∀ Γ left right (support : Profile n), support.WF →
    TypeRelated env U registry Γ left right support →
    TypeRelated env U registry Γ right left support
  focus : ∀ Γ left right (value support bound : Profile n),
    Minimal value support → value.HasType support → support ≤ bound →
    TypeRelated env U registry Γ left right bound →
    TypeRelated env U registry Γ left right support
  compose : ∀ Γ left middle right (value support other : Profile n),
    Minimal value support → value.HasType other →
    TypeRelated env U registry Γ left middle support →
    TypeRelated env U registry Γ middle right other →
    TypeRelated env U registry Γ left right support
  transport : ∀ Γ left right left' right' (value support other : Profile n),
    Minimal value support → value.HasType other →
    TypeRelated env U registry Γ left right support →
    TypeRelated env U registry Γ left left' other →
    TypeRelated env U registry Γ right right' other →
    TypeRelated env U registry Γ left' right' support

theorem SupportLaws.zero
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) : SupportLaws env U registry 0 := by
  have symm : ∀ Γ left right (support : Profile 0), support.WF →
      TypeRelated env U registry Γ left right support →
      TypeRelated env U registry Γ right left support := by
    intro Γ left right support _ h Δ ρ future relevant hr
    exact (h Δ ρ future relevant hr).symm
  have compose : ∀ Γ left middle right (value support other : Profile 0),
      Minimal value support → value.HasType other →
      TypeRelated env U registry Γ left middle support →
      TypeRelated env U registry Γ middle right other →
      TypeRelated env U registry Γ left right support := by
    intro Γ left middle right value support other minimal typed first second Δ ρ future atom ha
    obtain ⟨requested, hrequested, _, _, _⟩ := (minimal.rename ρ).support_origin ha
    have ht := (Profile.rename_hasType_iff (ρ := ρ)).mpr typed
    obtain ⟨otherAtom, hother, _⟩ := ht requested hrequested
    exact (first Δ ρ future atom ha).compose henv (second Δ ρ future otherAtom hother)
  refine ⟨symm, ?_, compose, ?_⟩
  · intro Γ left right value support bound _ _ hle h Δ ρ future atom ha
    have hl := (Profile.rename_le_iff (ρ := ρ)).mpr hle
    obtain ⟨other, ho, he⟩ := hl atom ha
    cases he
    exact h Δ ρ future atom ho
  · intro Γ left right left' right' value support other minimal typed first hl hr
    have hs : support.WF := by trivial
    exact compose _ _ _ _ _ _ _ minimal typed
      (symm _ _ _ _ hs (compose _ _ _ _ _ _ _ minimal typed (symm _ _ _ _ hs first) hl)) hr

end Lean4Lean.AnchoredSemantics
