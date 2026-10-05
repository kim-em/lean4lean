import Lean4Lean.Theory.Typing.AnchoredDataLaws
import Lean4Lean.Theory.Typing.AnchoredSupportLaws
import Lean4Lean.Theory.Typing.AnchoredMinimalPiSymmetry

/-! The symmetry and focusing successor steps use only the completed
strictly lower-rank support laws and the actual Pi witness constructors. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}

theorem SupportLaws.succ_symm (henv : env.Ordered)
    (lower : SupportLaws env U registry n)
    (dataLaws : RankedData.LowerEquality env U registry (relations env U registry n)) :
    ∀ Γ left right (support : Profile (n + 1)), support.WF →
      TypeRelated env U registry Γ left right support →
      TypeRelated env U registry Γ right left support := by
  intro Γ left right support hw h Δ ρ future atom ha
  have wf := (Profile.rename_wf_iff (ρ := ρ)).mpr hw
  have haWF := wf atom ha
  have hc := h Δ ρ future atom ha
  cases atom with
  | sort relevant => exact hc.symm
  | fn key output => exact False.elim hc
  | ctor | record => exact False.elim hc
  | family data =>
    obtain ⟨witness⟩ := hc
    exact ⟨witness.symm dataLaws⟩
  | pad atom => exact lower.symm _ _ _ _ haWF hc
  | pi A B domain rows =>
    obtain ⟨display⟩ := hc
    have hd : Profile.HasType domain (.sort true) := haWF.1
    exact ⟨display.symm henv lower.focus lower.compose lower.symm hd.wf_value
      (fun key output hm => (haWF.2 key output hm).2)⟩

private theorem le_of_subset {left right : Profile n}
    (h : ∀ atom ∈ left.atoms, atom ∈ right.atoms) : left ≤ right := by
  cases n <;> intro atom ha
  all_goals exact right.le_refl atom (h atom ha)

private theorem focus_atom (henv : env.Ordered)
    (lower : SupportLaws env U registry n)
    {Γ : List VExpr} {left right : VExpr}
    {atom : Atom (n + 1)} {support bound : Profile (n + 1)}
    (minimal : AtomMinimal atom support) (hle : support ≤ bound)
    (h : TypeRelated env U registry Γ left right bound) :
    TypeRelated env U registry Γ left right support := by
  cases minimal with
  | sort typed =>
    have hm := Profile.sort_le_mem hle
    intro Δ ρ future a ha
    simp only [Profile.sort, Profile.atoms] at ha
    cases List.mem_singleton.mp ha
    exact h Δ ρ future _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
  | family typed =>
    have hm := Profile.family_le_mem hle
    intro Δ ρ future a ha
    cases List.mem_singleton.mp ha
    exact h Δ ρ future _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
  | @fn _ domain result A B key output inputMinimal outputMinimal domainFormation =>
    obtain ⟨oldDomain, oldRows, hm, domainBound, rowBound⟩ :=
      Profile.pi_le_inv hle (List.mem_singleton_self _)
    obtain ⟨oldResult, oldRow, resultBound⟩ := rowBound key result (List.mem_singleton_self _)
    intro Δ ρ future a ha
    simp only [Profile.pi, Profile.rename_singleton, Atom.rename_pi, Rows.rename,
      List.map_cons, List.map_nil, Profile.atoms] at ha
    cases List.mem_singleton.mp ha
    have selected := h Δ ρ future _ (List.mem_map.mpr ⟨_, hm, rfl⟩)
    obtain ⟨display⟩ := selected
    have renamedRow : (key.rename ρ, oldResult.rename ρ) ∈ Rows.rename ρ oldRows :=
      List.mem_map.mpr ⟨(key, oldResult), oldRow, rfl⟩
    have renamedFormation := (Profile.rename_hasType_iff (ρ := ρ)).mpr domainFormation
    simp only [Profile.rename_sort] at renamedFormation
    refine ⟨display.focusMinimal (output := output.rename ρ)
      lower.focus lower.compose lower.symm renamedRow
      (inputMinimal.rename ρ) ?_
      (Profile.rename_hasType_iff.mpr inputMinimal.typed) ?_
      renamedFormation (Profile.rename_le_iff.mpr domainBound)
      (Profile.rename_le_iff.mpr resultBound)⟩
    · simpa only [Profile.rename_singleton] using outputMinimal.rename ρ
    · simpa only [Profile.rename_singleton] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr outputMinimal.typed
  | @pad _ atom support minimal =>
    have smallerBound : support ≤ bound.down := by
      simpa only [Profile.down_pad] using Profile.LE.down hle
    exact TypeRelated.pad henv (lower.focus _ _ _ _ _ _ minimal minimal.typed
      smallerBound (TypeRelated.down henv h))

theorem SupportLaws.succ_focus (henv : env.Ordered)
    (lower : SupportLaws env U registry n) :
    ∀ Γ left right (value support bound : Profile (n + 1)),
      Minimal value support → value.HasType support → support ≤ bound →
      TypeRelated env U registry Γ left right bound →
      TypeRelated env U registry Γ left right support := by
  intro Γ left right value support bound minimal _ hle h
  apply TypeRelated.of_singletons
  intro atom ha
  obtain ⟨requested, _, part, hm, hatom, subset⟩ := minimal.support_origin_subset ha
  have partBound := Profile.le_trans (le_of_subset subset) hle
  exact (focus_atom henv lower hm partBound h).singleton hatom

end Lean4Lean.AnchoredSemantics
