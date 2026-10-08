import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ProjCtor

/-! # Constructing field observations of constructor spines (stage C)

`ctor_field_obs`: a constructor spine `mk ps fs` of a never-zero projection-registered family
has, for each observation `k` of the field `fs[j]` and finite demands on the earlier fields, a
field observation `fieldOb S j L k` whose context `L` contains the demands. The observation is
built in the constructor's telescope: typed finite keys at the anchors `args.subst σ`
(`tele_compact` over the valuation of `spine_tele`), field-type and field-domain observations
of the codomain from the spine lemma on the codomain (whose key classes are identified with the
constructor's parameter domains through the family's telescope), and `tele_wind`. -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

theorem extS_apply : ∀ (K : List Key) (S : ObSets) (m : Nat),
    extS S K m = if h : m < K.length then listSet (K[K.length - 1 - m]).2.2 else S (m - K.length)
  | [], S, m => by simp [extS]
  | k :: K, S, m => by
    simp only [extS, List.foldl_cons] at *
    rw [show K.foldl (fun S k => S.cons (listSet k.2.2)) (S.cons (listSet k.2.2)) m =
      extS (S.cons (listSet k.2.2)) K m from rfl, extS_apply K]
    simp only [List.length_cons]
    by_cases hm : m < K.length
    · rw [dif_pos hm, dif_pos (by omega)]
      have e : K.length + 1 - 1 - m = (K.length - 1 - m) + 1 := by omega
      simp only [e, List.getElem_cons_succ]
    · rw [dif_neg hm]
      by_cases hm' : m = K.length
      · subst hm'; rw [dif_pos (by omega)]; simp [ObSets.cons]
      · rw [dif_neg (by omega)]
        obtain ⟨d, hd⟩ : ∃ d, m - K.length = d + 1 := ⟨m - K.length - 1, by omega⟩
        rw [hd, show m - (K.length + 1) = d by omega]; rfl

theorem keySets_eq_extS (K : List Key) : keySets K = extS .empty K := by
  funext m; rw [extS_apply]; simp only [keySets]; split <;> rfl

theorem keySets_congr {K K' : List Key}
    (H : List.Forall₂ (fun (k k' : Key) => ∀ y, y ∈ k.2.2 ↔ y ∈ k'.2.2) K K') :
    keySets K = keySets K' := by
  have hl := List.Forall₂.length_eq H
  funext m o
  simp only [keySets, hl]
  split
  · rename_i hm
    obtain ⟨_, h⟩ := forall₂_getElem H (K'.length - 1 - m) (by omega)
    exact propext (h o)
  · rfl

/-- The data of a chain of typed keys from the identity: the anchors, the observation sets, and
for each key its domain class, its typed class containing the anchor, and its typed list. -/
theorem TeleKeys.data (h : TeleKeys env U Δ σ S ds keys σ' S') :
    ∃ ys : List VExpr, σ' = ys.foldl VExpr.Subst.cons σ ∧ S' = extS S keys ∧
      ys.length = ds.length ∧ keys.length = ds.length ∧
      ∀ i k y A, keys[i]? = some k → ys[i]? = some y → ds[i]? = some A →
        k.1 = TyCls env U Δ (A.subst ((ys.take i).foldl VExpr.Subst.cons σ)) ∧
        TypedElCls env U Δ (TyCls env U Δ (A.subst ((ys.take i).foldl VExpr.Subst.cons σ))) k.2.1 ∧
        k.2.1 y ∧
        (∀ x ∈ k.2.2, TypedAt env U Δ k.2.1 ((ys.take i).foldl VExpr.Subst.cons σ)
          (extS S (keys.take i)) A x) ∧
        Backed (listSet k.2.2) := by
  induction h with
  | nil => exact ⟨[], rfl, by simp [extS], rfl, rfl, fun i k y A h => by simp at h⟩
  | @cons c y K σ S A ds keys σ' S' hc hy hK hb _ ih =>
    obtain ⟨ys, e1, e2, hl1, hl2, hd⟩ := ih
    refine ⟨y :: ys, e1, by rw [e2]; rfl, by simp [hl1], by simp [hl2], fun i k y' A' hk hy' hA => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk hy' hA
      subst hk hy' hA
      exact ⟨rfl, hc, hy, fun x hx => by simpa [extS] using hK x hx, hb⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hk hy' hA
      have := hd i k y' A' hk hy' hA
      simpa [List.take_succ_cons, List.foldl_cons, extS] using this

theorem forall₂_take' {R : α → β → Prop} : ∀ (i : Nat) {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → List.Forall₂ R (l₁.take i) (l₂.take i)
  | 0, _, _, _ => by simp
  | _ + 1, _, _, .nil => by simp
  | i + 1, _, _, .cons h H => by simpa using List.Forall₂.cons h (forall₂_take' i H)

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

end

end Model
end VEnv
end Lean4Lean
