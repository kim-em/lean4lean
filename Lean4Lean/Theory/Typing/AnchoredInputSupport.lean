import Lean4Lean.Theory.Typing.AnchoredMinimalSupport
import Lean4Lean.Theory.Typing.AnchoredSupportBasisRename
import Lean4Lean.Theory.Typing.AnchoredViewMaps

/-! Finite domain supports for contravariant input adaptation. A backward
type-support map is applied to every hereditary minimal support of the old
input. This retains the support before any caller or private display is chosen.
The map laws below are strict lower-rank obligations of the view interpreter,
not fields stored in a source observation or a final correctness hypothesis. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

noncomputable def inputDomain (oldInput : Profile n) (back : Profile n → Profile n)
    (domain : Profile n) : Profile n :=
  domain.union (Profile.unions ((Basis oldInput domain).map back))

private theorem rename_unions (profiles : List (Profile n)) (ρ : Lift) :
    (Profile.unions profiles).rename ρ =
      Profile.unions (profiles.map (Profile.rename ρ)) := by
  induction profiles with
  | nil => rfl
  | cons first rest ih => exact (Profile.rename_union ..).trans (congrArg _ ih)

theorem inputDomain.rename (oldInput domain : Profile n) (ρ : Lift)
    (back back' : Profile n → Profile n)
    (natural : ∀ d, (back d).rename ρ = back' (d.rename ρ)) :
    (inputDomain oldInput back domain).rename ρ =
      inputDomain (oldInput.rename ρ) back' (domain.rename ρ) := by
  simp only [inputDomain, Profile.rename_union, rename_unions, ← Basis.rename,
    List.map_map, Function.comp_def, natural]

private theorem le_unions_of_mem {profile : Profile n} {profiles : List (Profile n)}
    (h : profile ∈ profiles) : profile ≤ Profile.unions profiles := by
  induction profiles with
  | nil => cases h
  | cons first rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Profile.le_union_left _ _
    · exact Profile.le_trans (ih h) (Profile.le_union_right _ _)

theorem inputDomain.original {oldInput domain : Profile n} {back : Profile n → Profile n} :
    domain ≤ inputDomain oldInput back domain := Profile.le_union_left _ _

theorem inputDomain.selected {oldInput domain support : Profile n}
    {back : Profile n → Profile n} (h : support ∈ Basis oldInput domain) :
    back support ≤ inputDomain oldInput back domain :=
  Profile.le_trans (le_unions_of_mem (List.mem_map.mpr ⟨support, h, rfl⟩))
    (Profile.le_union_right _ _)

theorem inputDomain.formed {oldInput domain : Profile n} {back : Profile n → Profile n}
    (mapsSort : ∀ d : Profile n, d.HasType (.sort true) → (back d).HasType (.sort true))
    (h : domain.HasType (.sort true)) :
    (inputDomain oldInput back domain).HasType (.sort true) := by
  apply h.union
  apply Profile.HasType.unions (Profile.WF.sort true)
  intro d hd
  obtain ⟨support, hs, rfl⟩ := List.mem_map.mp hd
  exact mapsSort support (Basis.minimal hs).formation

theorem inputDomain.typed {oldInput newInput domain : Profile n}
    {back : Profile n → Profile n}
    (mapsSort : ∀ d : Profile n, d.HasType (.sort true) → (back d).HasType (.sort true))
    (mapsType : ∀ d : Profile n, oldInput.HasType d → newInput.HasType (back d))
    (formed : domain.HasType (.sort true)) (typed : oldInput.HasType domain) :
    newInput.HasType (inputDomain oldInput back domain) := by
  obtain ⟨support, hs⟩ := Basis.exists typed
  exact (mapsType support (Basis.valid hs).1).enlarge (inputDomain.selected hs)
    (inputDomain.formed mapsSort formed).wf_value

private theorem code_unions {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {left right : VExpr} {profiles : List (Profile n)}
    (h : ∀ p ∈ profiles, TypeRelated env U registry Γ left right p) :
    TypeRelated env U registry Γ left right (Profile.unions profiles) := by
  apply TypeRelated.of_singletons
  intro atom hm
  induction profiles with
  | nil => cases hm
  | cons first rest ih =>
    rcases List.mem_append.mp hm with hf | hr
    · exact (h first (List.mem_cons_self)).singleton hf
    · exact ih (fun p hp => h p (List.mem_cons_of_mem first hp)) hr

theorem inputDomain.code {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {Γ : List VExpr} {left right : VExpr}
    {oldInput domain : Profile n} {back : Profile n → Profile n}
    (mapsCode : ∀ d : Profile n, TypeRelated env U registry Γ left right d →
      TypeRelated env U registry Γ left right (back d))
    (h : TypeRelated env U registry Γ left right domain) :
    TypeRelated env U registry Γ left right (inputDomain oldInput back domain) := by
  have extra : TypeRelated env U registry Γ left right
      (Profile.unions ((Basis oldInput domain).map back)) := by
    apply code_unions
    intro d hd
    obtain ⟨support, hs, rfl⟩ := List.mem_map.mp hd
    exact mapsCode support (h.focusMinimal henv (Basis.minimal hs) (Basis.valid hs).2)
  apply TypeRelated.of_singletons
  intro atom hm
  rcases List.mem_append.mp hm with hbase | hextra
  · exact h.singleton hbase
  · exact extra.singleton hextra

/-- Rebuild the caller-domain bridge at a fixed member of the finite mapped
basis. Merely retaining the new anchor's self-capability would not supply this
binary bridge. No arbitrary semantic restriction along intrinsic ≤ is used. -/
theorem inputDomain.bridge {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {Γ : List VExpr} {keyDomain actualDomain otherDomain : VExpr}
    {oldInput newInput domain oldSupport : Profile n} {back : Profile n → Profile n}
    (mapsSort : ∀ d : Profile n, d.HasType (.sort true) → (back d).HasType (.sort true))
    (mapsType : ∀ d : Profile n, oldInput.HasType d → newInput.HasType (back d))
    (mapsCode : ∀ d : Profile n, TypeRelated env U registry Γ keyDomain actualDomain d →
      TypeRelated env U registry Γ keyDomain actualDomain (back d))
    (typed : oldInput.HasType domain) (oldTyped : oldInput.HasType oldSupport)
    (hdom : TypeRelated env U registry Γ actualDomain otherDomain domain)
    (hold : TypeRelated env U registry Γ keyDomain actualDomain oldSupport) :
    ∃ support, newInput.HasType support ∧ support.HasType (.sort true) ∧
      support ≤ inputDomain oldInput back domain ∧
      TypeRelated env U registry Γ keyDomain actualDomain support := by
  obtain ⟨selected, hs⟩ := Basis.exists typed
  have minimal := Basis.minimal hs
  have focused := hdom.focusMinimal henv minimal (Basis.valid hs).2
  have old := focused.left_diagonal.composeMinimal henv minimal oldTyped
    (hold.symm henv oldTyped.wf_type)
  exact ⟨back selected, mapsType selected minimal.typed,
    mapsSort selected minimal.formation, inputDomain.selected hs,
    mapsCode selected (old.symm henv minimal.typed.wf_type)⟩

def inputKey (key : Key n) (input : Profile n) : Key n := { key with input }

noncomputable def inputTypes (key : Key n) (newInput : Profile n)
    (back : Profile n → Profile n) (profile : Profile (n + 1)) : Profile (n + 1) := by
  classical
  exact profile.map fun
    | .pi A B domain rows => if key.input.HasType domain then
        .pi A B (inputDomain key.input back domain)
          (reanchorRows key (inputKey key newInput) rows) else .pi A B domain rows
    | atom => atom

theorem inputTypes.rename (key : Key n) (newInput : Profile n) (profile : Profile (n + 1))
    (ρ : Lift) (back back' : Profile n → Profile n)
    (natural : ∀ d, (back d).rename ρ = back' (d.rename ρ)) :
    (inputTypes key newInput back profile).rename ρ =
      inputTypes (key.rename ρ) (newInput.rename ρ) back' (profile.rename ρ) := by
  classical
  simp only [inputTypes, Profile.rename, List.map_map]
  apply List.map_congr_left
  intro atom _
  cases atom with
  | sort | fn | family | ctor | record | pad => rfl
  | pi A B domain rows =>
    change (Atom.rename ρ (if key.input.HasType domain then _ else _)) = _
    by_cases ht : key.input.HasType domain
    · have ht' := (Profile.rename_hasType_iff (ρ := ρ)).mpr ht
      simp only [ht, if_pos, Function.comp_def, Atom.rename_pi, Key.rename,
        ht', inputDomain.rename _ _ _ _ _ natural, reanchorRows_rename, inputKey]
      rfl
    · have ht' : ¬(key.input.rename ρ).HasType (Profile.rename ρ domain) :=
        fun h => ht (Profile.rename_hasType_iff.mp h)
      simp only [ht, if_false, Function.comp_def, Atom.rename_pi, Key.rename, ht']

theorem inputTypes.wf {key : Key n} {newInput : Profile n}
    {back : Profile n → Profile n} {profile : Profile (n + 1)}
    (mapsSort : ∀ d : Profile n, d.HasType (.sort true) → (back d).HasType (.sort true))
    (mapsType : ∀ d : Profile n, key.input.HasType d → newInput.HasType (back d))
    (h : profile.WF) : (inputTypes key newInput back profile).WF := by
  classical
  intro atom hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
  have hw := h old ho
  cases old with
  | sort | fn | family | ctor | record | pad => exact hw
  | pi A B domain rows =>
    dsimp only
    split
    · have hf := inputDomain.formed (oldInput := key.input) mapsSort hw.1
      refine ⟨hf, ?_⟩
      intro k result hr
      rcases mem_reanchorRows.mp hr with old | ⟨rfl, old⟩
      · have typed := hw.2 k result old
        have hk : Profile.HasType k.input domain := typed.1
        exact ⟨hk.enlarge inputDomain.original hf.wf_value, typed.2⟩
      · have typed := hw.2 key result old
        exact ⟨inputDomain.typed mapsSort mapsType hw.1 typed.1, typed.2⟩
    · exact hw

theorem inputTypes.sort {key : Key n} {newInput : Profile n}
    {back : Profile n → Profile n} {profile : Profile (n + 1)}
    (mapsSort : ∀ d : Profile n, d.HasType (.sort true) → (back d).HasType (.sort true))
    (mapsType : ∀ d : Profile n, key.input.HasType d → newInput.HasType (back d))
    (h : profile.HasType (.sort relevant)) :
    (inputTypes key newInput back profile).HasType (.sort relevant) := by
  classical
  refine ⟨inputTypes.wf mapsSort mapsType h.wf_value, h.wf_type, ?_⟩
  intro atom hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
  obtain ⟨cover, hc, ht⟩ := h.2.2 old ho
  cases List.mem_singleton.mp hc
  refine ⟨.sort relevant, List.mem_singleton_self _, ?_⟩
  cases old with
  | sort | fn | family | ctor | record | pad => exact ht
  | pi A B domain rows =>
    dsimp only
    split
    · intro k result hr
      rcases mem_reanchorRows.mp hr with old | ⟨rfl, old⟩
      · exact ht k result old
      · exact ht key result old
    · exact ht

theorem inputTypes.typed {key : Key n} {newInput : Profile n}
    {back : Profile n → Profile n} {output : Atom n} {profile : Profile (n + 1)}
    (mapsSort : ∀ d : Profile n, d.HasType (.sort true) → (back d).HasType (.sort true))
    (mapsType : ∀ d : Profile n, key.input.HasType d → newInput.HasType (back d))
    (h : (Profile.fn key output).HasType profile) :
    (Profile.fn (inputKey key newInput) output).HasType
      (inputTypes key newInput back profile) := by
  classical
  obtain ⟨A, B, domain, rows, result, hm, hw, _, inputTyped, hr, ht⟩ :=
    h.fn_inv (List.mem_singleton_self _)
  have newWF := inputTypes.wf mapsSort mapsType hw
  simp only [inputTypes, Profile.pi, Profile.singleton, Profile.mk, List.map_cons,
    List.map_nil, inputTyped, if_pos] at newWF
  change (Profile.pi A B (inputDomain key.input back domain)
    (reanchorRows key (inputKey key newInput) rows)).WF at newWF
  have typed := Profile.HasType.fn newWF (reanchorRows.changed hr) ht
  apply typed.enlarge ?_ (inputTypes.wf mapsSort mapsType h.wf_type)
  intro atom ha
  cases List.mem_singleton.mp ha
  apply Profile.le_refl (inputTypes key newInput back profile)
  exact List.mem_map.mpr ⟨_, hm, by simp only [inputTyped, if_pos]⟩

end Lean4Lean.AnchoredSemantics
