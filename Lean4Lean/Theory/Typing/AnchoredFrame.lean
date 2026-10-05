import Lean4Lean.Theory.Typing.AnchoredSemantics

/-! Forward transport and proof-frame absorption for the concrete anchored
relation. Absorption applies only when every operand and profile is lifted
from the smaller context; it does not retract private display components. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ Δ Ω : List VExpr} {ρ : Lift}

theorem FutureCode.future
    {core : List VExpr → VExpr → VExpr → Profile n → Prop}
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (h : FutureCode env U core Γ left right profile) :
    FutureCode env U core Δ (left.lift' ρ) (right.lift' ρ) (profile.rename ρ) := by
  intro Ω τ J
  simpa only [lift'_comp, ← Profile.rename_comp] using h Ω (ρ.comp τ) (W.comp J henv)

theorem FutureTerm.future
    {core : List VExpr → VExpr → VExpr → VExpr → Profile n → Profile n → Prop}
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (h : FutureTerm env U core Γ left right type value typeProfile) :
    FutureTerm env U core Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (typeProfile.rename ρ) := by
  intro Ω τ J
  simpa only [lift'_comp, ← Profile.rename_comp] using h Ω (ρ.comp τ) (W.comp J henv)

theorem SaturatedTerm.absorb
    {core : List VExpr → VExpr → VExpr → VExpr → Profile n → Profile n → Prop}
    (henv : env.Ordered) (I : ProofInsertion env U Γ Δ ρ)
    (h : SaturatedTerm env U core Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (typeProfile.rename ρ)) :
    SaturatedTerm env U core Γ left right type value typeProfile := by
  rcases h with he | ⟨Ω, τ, J, h⟩
  · left
    exact Profile.rename_inj.mp (he.trans Profile.rename_empty.symm)
  · right
    exact ⟨Ω, ρ.comp τ, I.comp J henv, by
      simpa only [lift'_comp, ← Profile.rename_comp] using h⟩

theorem FutureTerm.absorb
    {core : List VExpr → VExpr → VExpr → VExpr → Profile n → Profile n → Prop}
    (henv : env.Ordered) (I : ProofInsertion env U Γ Δ ρ)
    (h : FutureTerm env U (SaturatedTerm env U core) Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (typeProfile.rename ρ)) :
    FutureTerm env U (SaturatedTerm env U core) Γ left right type value typeProfile := by
  intro V τ W
  obtain ⟨Ω, i, j, hi, hj, he⟩ := I.pushout W henv
  apply SaturatedTerm.absorb henv hi
  have hout := h Ω j hj
  simpa only [← lift'_comp, ← Profile.rename_comp, he] using hout

theorem TypeRelated.future {profile : Profile n}
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Δ (left.lift' ρ) (right.lift' ρ) (profile.rename ρ) := by
  cases n <;> intro Ω τ J <;>
    simpa only [lift'_comp, ← Profile.rename_comp] using h Ω (ρ.comp τ) (W.comp J henv)

theorem Related.future {value typeProfile : Profile n}
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (h : Related env U registry Γ left right type value typeProfile) :
    Related env U registry Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (typeProfile.rename ρ) := by
  cases n <;> intro atom ha
  all_goals
    obtain ⟨oldAtom, hm, rfl⟩ := List.mem_map.mp ha
    simpa only [Profile.rename_singleton] using FutureTerm.future henv W (h oldAtom hm)

theorem Related.absorb {value typeProfile : Profile n}
    (henv : env.Ordered) (I : ProofInsertion env U Γ Δ ρ)
    (h : Related env U registry Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (value.rename ρ) (typeProfile.rename ρ)) :
    Related env U registry Γ left right type value typeProfile := by
  cases n <;> intro atom ha
  all_goals
    have hm : atom.rename ρ ∈ (value.rename ρ).atoms := List.mem_map_of_mem ha
    have h' := h _ hm
    apply FutureTerm.absorb henv I
    simpa only [Profile.rename_singleton] using h'

theorem Related.singleton_of_mem {value typeProfile : Profile n}
    (h : Related env U registry Γ left right type value typeProfile)
    (ha : atom ∈ value.atoms) :
    Related env U registry Γ left right type (.singleton atom) typeProfile := by
  cases n <;> intro other ho
  all_goals
    have he : other = atom := List.mem_singleton.mp ho
    subst other
    exact h atom ha

theorem Related.of_singletons {value typeProfile : Profile n}
    (h : ∀ atom ∈ value.atoms,
      Related env U registry Γ left right type (.singleton atom) typeProfile) :
    Related env U registry Γ left right type value typeProfile := by
  cases n <;> intro atom ha
  all_goals exact h atom ha atom (List.mem_singleton_self _)

theorem Related.union {first second typeProfile : Profile n}
    (h₁ : Related env U registry Γ left right type first typeProfile)
    (h₂ : Related env U registry Γ left right type second typeProfile) :
    Related env U registry Γ left right type (first.union second) typeProfile := by
  cases n <;> intro atom ha
  all_goals
    rcases List.mem_append.mp ha with h | h
    · exact h₁ atom h
    · exact h₂ atom h

theorem Admitted.future (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (h : Admitted env U registry Γ key left right) :
    Admitted env U registry Δ (key.rename ρ) (left.lift' ρ) (right.lift' ρ) := by
  obtain ⟨hanchor, heq, support, hp, hs, hc, ha, hr⟩ := h
  refine ⟨hanchor.weak' henv W.weakening, heq.weak' henv W.weakening,
    support.rename ρ, Profile.rename_hasType_iff.mpr hp, ?_,
    TypeRelated.future henv W hc, Related.future henv W ha, Related.future henv W hr⟩
  simpa only [Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := ρ)).mpr hs

end Lean4Lean.AnchoredSemantics
