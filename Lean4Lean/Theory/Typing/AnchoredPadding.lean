import Lean4Lean.Theory.Typing.AnchoredFrame

/-! Semantic introduction and reflection of explicit rank padding. Finite
value conjunction is interpreted atom by atom, so reflection does not need
to combine independently chosen unsaturated proof frames.
-/

namespace Lean4Lean.AnchoredSemantics

set_option backward.isDefEq.respectTransparency false
open VExpr VEnv AnchoredProfiles

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ : List VExpr} {left right type : VExpr}

theorem TypeRelated.singleton {profile : Profile n} {atom : Atom n}
    (h : TypeRelated env U registry Γ left right profile) (ha : atom ∈ profile.atoms) :
    TypeRelated env U registry Γ left right (.singleton atom) := by
  cases n <;> intro Δ ρ future other hother
  all_goals
    have he : other = atom.rename ρ := List.mem_singleton.mp hother
    subst other
    exact h Δ ρ future _ (List.mem_map.mpr ⟨atom, ha, rfl⟩)

theorem TypeRelated.of_singletons {profile : Profile n}
    (h : ∀ atom ∈ profile.atoms,
      TypeRelated env U registry Γ left right (.singleton atom)) :
    TypeRelated env U registry Γ left right profile := by
  cases n <;> intro Δ ρ future other hother
  all_goals
    obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hother
    exact h atom ha Δ ρ future _ (List.mem_singleton_self _)

/-- Padding keeps precisely the existing lower code demands. -/
theorem TypeRelated.pad {profile : Profile n} (henv : env.Ordered)
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right profile.pad := by
  intro Δ ρ future atom ha
  have hm : atom ∈ (profile.rename ρ).pad.atoms := by
    simpa only [Profile.pad_rename] using ha
  obtain ⟨lowerAtom, hl, rfl⟩ := List.mem_map.mp hm
  exact (TypeRelated.future henv future h).singleton hl

/-- Project only demands represented by padding or an exposed universe.
No Pi or function capability is synthesized at the smaller rank. -/
theorem TypeRelated.down {profile : Profile (n + 1)} (henv : env.Ordered)
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right profile.down := by
  cases n <;> intro Δ ρ future atom ha
  all_goals
    have hm : atom ∈ (profile.rename ρ).down.atoms := by
      simpa only [Profile.down_rename] using ha
    obtain ⟨upper, hu, hl⟩ := List.mem_flatMap.mp hm
    have hc := h Δ ρ future upper hu
    cases upper with
    | sort relevant =>
      have he := List.mem_singleton.mp hl
      subst atom
      exact hc
    | fn | pi | family | ctor | record => cases hl
    | pad lowerAtom =>
      have he := List.mem_singleton.mp hl
      subst atom
      have hbase := hc Δ .refl (.refl (future.targetWF henv))
      simp only [lift'_refl, Profile.rename_refl] at hbase
      exact hbase _ (List.mem_singleton_self _)

theorem TypeRelated.pad_iff {profile : Profile n} (henv : env.Ordered) :
    TypeRelated env U registry Γ left right profile.pad ↔
      TypeRelated env U registry Γ left right profile := by
  constructor
  · intro h
    simpa only [Profile.down_pad] using h.down henv
  · exact TypeRelated.pad henv

/-- A padded value observation reveals its original lower demand even when
the high type support is not itself a padded profile. -/
theorem Related.unpad {value : Profile n} {typeProfile : Profile (n + 1)}
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (h : Related env U registry Γ left right type value.pad typeProfile) :
    Related env U registry Γ left right type value typeProfile.down := by
  apply Related.of_singletons
  intro atom ha
  have hm : AtomData.pad atom ∈ value.pad.atoms := List.mem_map_of_mem ha
  have hs := h _ hm Γ .refl (.refl hΓ)
  simp only [Profile.rename_refl, lift'_refl] at hs
  rcases hs with hempty | ⟨Δ, ρ, insertion, _, _, values⟩
  · cases hempty
  · have hv := values (.pad (atom.rename ρ)) (List.mem_singleton_self _)
    change Related env U registry Δ (left.lift' ρ) (right.lift' ρ) (type.lift' ρ)
      (.singleton (atom.rename ρ)) (typeProfile.rename ρ).down at hv
    apply Related.absorb henv insertion
    simpa only [Profile.rename_singleton, Profile.down_rename] using hv

/-- Introduction reuses the full lower singleton relation in the selected
proof frame. The extracted core supplies only typing and type-capability
evidence; it is never asserted to be stable in future worlds. -/
theorem Related.pad {value typeProfile : Profile n} (henv : env.Ordered)
    (h : Related env U registry Γ left right type value typeProfile) :
    Related env U registry Γ left right type value.pad typeProfile.pad := by
  cases n <;> intro upper hu Δ ρ future
  all_goals
    obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hu
    have single := Related.singleton_of_mem h ha
    have hs := h atom ha Δ ρ future
    rcases hs with hempty | ⟨Ω, τ, insertion, typed, typeCode, _⟩
    · cases hempty
    · right
      refine ⟨Ω, τ, insertion, ?_, ?_, ?_⟩
      · simpa only [Profile.rename_singleton, Profile.pad_singleton,
          Atom.rename_pad, Profile.rename_pad] using typed.pad
      · change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
          ((type.lift' ρ).lift' τ) ((typeProfile.rename ρ).rename τ) at typeCode
        change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
          ((type.lift' ρ).lift' τ) ((typeProfile.pad.rename ρ).rename τ)
        simpa only [Profile.rename_pad] using TypeRelated.pad henv typeCode
      · intro observed hobserved
        have he : observed = .pad ((atom.rename ρ).rename τ) :=
          List.mem_singleton.mp hobserved
        subst observed
        have lower := Related.future henv insertion.toFuture
          (Related.future henv future single)
        change Related env U registry Ω ((left.lift' ρ).lift' τ)
          ((right.lift' ρ).lift' τ) ((type.lift' ρ).lift' τ)
          (.singleton ((atom.rename ρ).rename τ))
          (((typeProfile.pad.rename ρ).rename τ).down)
        simpa only [← Profile.pad_rename, Profile.down_pad,
          Profile.rename_singleton] using lower

theorem Related.pad_iff {value typeProfile : Profile n}
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) :
    Related env U registry Γ left right type value.pad typeProfile.pad ↔
      Related env U registry Γ left right type value typeProfile := by
  constructor
  · intro h
    simpa only [Profile.down_pad] using h.unpad henv hΓ
  · exact Related.pad henv

/-- The existential type support is padded along with the fixed input. -/
theorem Admitted.pad {key : Key n} (henv : env.Ordered)
    (h : Admitted env U registry Γ key left right) :
    Admitted env U registry Γ key.pad left right := by
  obtain ⟨hanchor, hpair, support, hinput, hsupport, hcode, hfirst, hsecond⟩ := h
  exact ⟨hanchor, hpair, support.pad, hinput.pad, hsupport.pad_sort,
    TypeRelated.pad henv hcode, Related.pad henv hfirst, Related.pad henv hsecond⟩

/-- A padded input cannot admit extra arguments: project its actual support
and both semantic input witnesses to the original rank. -/
theorem Admitted.unpad {key : Key n} (henv : env.Ordered)
    (hΓ : OnCtx Γ (env.IsType U))
    (h : Admitted env U registry Γ key.pad left right) :
    Admitted env U registry Γ key left right := by
  obtain ⟨hanchor, hpair, support, hinput, hsupport, hcode, hfirst, hsecond⟩ := h
  refine ⟨hanchor, hpair, support.down, hinput.pad_inv, ?_,
    TypeRelated.down henv hcode, Related.unpad henv hΓ hfirst,
    Related.unpad henv hΓ hsecond⟩
  simpa only [Profile.down_sort] using hsupport.down

theorem Admitted.pad_iff {key : Key n} (henv : env.Ordered)
    (hΓ : OnCtx Γ (env.IsType U)) :
    Admitted env U registry Γ key.pad left right ↔
      Admitted env U registry Γ key left right :=
  ⟨Admitted.unpad henv hΓ, Admitted.pad henv⟩

end Lean4Lean.AnchoredSemantics
