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

theorem TeleKeys.head {k : Key} (h : TeleKeys env U Δ σ S (A :: ds) (k :: keys) σ' S') :
    TypedElCls env U Δ (TyCls env U Δ (A.subst σ)) k.2.1 := by
  cases h with | cons hc => exact hc

theorem forall₂_take' {R : α → β → Prop} : ∀ (i : Nat) {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → List.Forall₂ R (l₁.take i) (l₂.take i)
  | 0, _, _, _ => by simp
  | _ + 1, _, _, .nil => by simp
  | i + 1, _, _, .cons h H => by simpa using List.Forall₂.cons h (forall₂_take' i H)

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- The classes of a chain of typed keys from the identity are typed at the domains instantiated
at any other members `bs` of the classes. -/
theorem TeleKeys.cls_at (h : TeleKeys env U Δ .id .empty ds keys σ' S')
    (hds : DomsSD env U Δ [] ds) {bs : List VExpr}
    (hbs : List.Forall₂ (fun (k : Key) b => k.2.1 b) keys bs) :
    ∀ i k A, keys[i]? = some k → ds[i]? = some A →
      TypedElCls env U Δ (TyCls env U Δ (A.subst (VExpr.argSubst (bs.take i)))) k.2.1 ∧
      Ctx.SubstEq env U Δ (VExpr.argSubst (bs.take i)) (VExpr.argSubst (bs.take i))
        (ds.take i).reverse := by
  intro i k A hk hA
  have hil : i < ds.length := (List.getElem?_eq_some_iff.1 hA).1
  have hkl : i < keys.length := (List.getElem?_eq_some_iff.1 hk).1
  have hl := h.length
  have e1 : ds = ds.take i ++ ds.drop i := (List.take_append_drop i ds).symm
  have e2 : keys = keys.take i ++ keys.drop i := (List.take_append_drop i keys).symm
  rw [e1, e2] at h
  obtain ⟨σ₁, S₁, h1, h2⟩ := TeleKeys.split (by simp; omega) h
  obtain ⟨ys, rfl, -, -, -, -⟩ := TeleKeys.data h1
  have hbs' := forall₂_take' i hbs
  obtain ⟨hds1, u, hsd⟩ := DomsSD.take_getElem hds i hil
  have W := TeleKeys.substEq henv hΔ h1 (v := .id) hds1 (Ctx.SubstEq.nil) hbs'
  simp only [List.append_nil] at W
  refine ⟨?_, SubstEq.right henv hΔ W⟩
  rw [List.drop_eq_getElem_cons hil, List.drop_eq_getElem_cons hkl] at h2
  have hc := h2.head
  have eA : ds[i] = A := Option.some.inj ((List.getElem?_eq_getElem hil).symm.trans hA)
  have ek : keys[i] = k := Option.some.inj ((List.getElem?_eq_getElem hkl).symm.trans hk)
  rw [ek] at hc
  subst eA
  simp only [List.append_nil] at hsd
  have := TyCls.eq_of_defeq (IsDefEq.substDF henv W.wf hΔ W hsd.1.defeq.hasType.1)
  unfold VExpr.argSubst; rw [← this]; exact hc

end

end Model
end VEnv
end Lean4Lean
