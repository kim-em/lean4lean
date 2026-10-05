import Lean4Lean.Theory.Typing.AnchoredPadding
import Lean4Lean.Theory.Typing.AnchoredExposureAbsorption

/-! Extract code evidence from a sortable term demand. Each term atom may
choose its own inhabited proof extension; the conclusion retains and combines
those extensions. No reflection of private display components is assumed. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

/-- Code evidence in an actual generated inhabited proof extension. -/
def FramedCode (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right : VExpr) (profile : Profile n) : Prop :=
  ∃ Δ ρ, ProofInsertion env U Γ Δ ρ ∧
    TypeRelated env U registry Δ (left.lift' ρ) (right.lift' ρ) (profile.rename ρ)

/-- Absorption reflects only the initial trace renaming and keeps its private
display context. It does not substitute into arbitrary private components. -/
theorem FramedCode.absorb (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {left right : VExpr} {profile : Profile n}
    (h : FramedCode env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right profile := by
  obtain ⟨Δ, ρ, I, h⟩ := h
  exact TypeRelated.absorb henv hscoped I h

theorem FramedCode.union (henv : env.Ordered)
    {Γ : List VExpr} {left right : VExpr} {p q : Profile n}
    (hp : FramedCode env U registry Γ left right p)
    (hq : FramedCode env U registry Γ left right q) :
    FramedCode env U registry Γ left right (p.union q) := by
  obtain ⟨Δ₁, ρ₁, I₁, hp⟩ := hp
  obtain ⟨Δ₂, ρ₂, I₂, hq⟩ := hq
  obtain ⟨Ω, j, i, J, I, hmaps⟩ := I₁.pushoutProof I₂ henv
  have hp' := hp.future henv I.toFuture
  have hq' := hq.future henv J.toFuture
  simp only [← lift'_comp, ← Profile.rename_comp, hmaps] at hp' hq'
  refine ⟨Ω, ρ₂.comp j, I₂.comp J henv, ?_⟩
  apply TypeRelated.of_singletons
  intro atom hm
  rw [Profile.rename_union] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hp'.singleton hm
  · exact hq'.singleton hm

theorem FramedCode.of_singletons (henv : env.Ordered)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {left right : VExpr} {profile : Profile n}
    (h : ∀ atom ∈ profile.atoms,
      FramedCode env U registry Γ left right (.singleton atom)) :
    FramedCode env U registry Γ left right profile := by
  induction profile with
  | nil =>
    refine ⟨Γ, .refl, .refl hΓ, ?_⟩
    apply TypeRelated.of_singletons
    intro atom hm
    cases hm
  | cons atom rest ih =>
    exact (h atom (List.mem_cons_self)).union henv
      (ih fun a ha => h a (List.mem_cons_of_mem atom ha))

/-- This is the leaf operation for source code certificates. The demanded
profile must itself be intrinsically sortable; arbitrary function demands
cannot be read as code. The assigned raw type and its support may be arbitrary. -/
theorem Related.codeInFrame (henv : env.Ordered)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {left right type : VExpr} {value typeProfile : Profile n} {relevant : Bool}
    (hsort : value.HasType (.sort relevant))
    (h : Related env U registry Γ left right type value typeProfile) :
    FramedCode env U registry Γ left right value := by
  induction n generalizing Γ left right type with
  | zero =>
    apply FramedCode.of_singletons henv hΓ
    intro atom ha
    have hs := h atom ha Γ .refl (.refl hΓ)
    simp only [lift'_refl, Profile.rename_refl] at hs
    rcases hs with hempty | ⟨Δ, ρ, I, _, _, hc⟩
    · cases hempty
    · exact ⟨Δ, ρ, I, hc⟩
  | succ n ih =>
    apply FramedCode.of_singletons henv hΓ
    intro atom ha
    have hat := hsort.singleton_of_mem ha
    have hs := h atom ha Γ .refl (.refl hΓ)
    simp only [lift'_refl, Profile.rename_refl] at hs
    rcases hs with hempty | ⟨Δ, ρ, I, _, _, hv⟩
    · cases hempty
    have hv := hv (atom.rename ρ) (List.mem_singleton_self _)
    cases atom with
    | fn | ctor | record =>
      obtain ⟨cover, hm, ht⟩ := hat.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp hm
      contradiction
    | sort | pi | family => exact ⟨Δ, ρ, I, hv⟩
    | pad lower =>
      have hlow : (Profile.singleton lower).HasType (.sort relevant) := by
        have hp : (Profile.singleton lower).pad.HasType (.sort relevant) := hat
        simpa only [Profile.down_sort] using hp.pad_inv
      have hlow' : (Profile.singleton (lower.rename ρ)).HasType (.sort relevant) := by
        simpa only [Profile.rename_singleton, Profile.rename_sort] using
          (Profile.rename_hasType_iff (ρ := ρ)).mpr hlow
      obtain ⟨Ω, τ, J, hc⟩ := ih (I.targetWF henv) hlow' hv
      refine ⟨Ω, ρ.comp τ, I.comp J henv, ?_⟩
      have hc' := hc.pad henv
      simpa only [← lift'_comp, ← Profile.rename_singleton, ← Profile.rename_comp,
        Profile.pad_rename, Profile.pad_singleton] using hc'

/-- Sortable computational leaves provide code evidence in the caller's
world, including when their term interpretation chose private proof frames. -/
theorem Related.code_of_sortable (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {left right type : VExpr} {value typeProfile : Profile n} {relevant : Bool}
    (hsort : value.HasType (.sort relevant))
    (h : Related env U registry Γ left right type value typeProfile) :
    TypeRelated env U registry Γ left right value :=
  (h.codeInFrame henv hΓ hsort).absorb henv hscoped

/-- A nonempty term demand retains its entire chosen type capability. Empty
demands deliberately do not imply any capability about their assigned type. -/
theorem Related.typeCode (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {left right type : VExpr} {value typeProfile : Profile n}
    (hne : value.Nonempty)
    (h : Related env U registry Γ left right type value typeProfile) :
    TypeRelated env U registry Γ type type typeProfile := by
  obtain ⟨atom, ha⟩ := List.exists_mem_of_ne_nil value.atoms hne
  cases n <;> have hs := h atom ha Γ .refl (.refl hΓ)
  all_goals
    simp only [lift'_refl, Profile.rename_refl] at hs
    rcases hs with hempty | ⟨Δ, ρ, I, _, ht, _⟩
    · cases hempty
    · exact TypeRelated.absorb henv hscoped I ht

end Lean4Lean.AnchoredSemantics
