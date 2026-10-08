import Lean4Lean.Std.Basic

/-! List lemmas shared by the verification, in `namespace Lean4Lean` like `Std/Basic.lean`. -/

namespace Lean4Lean

theorem List.forall₂_drop {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.drop k) (r.drop k)
  | _, _, .nil, _ => by simp
  | _, _, .cons h t, 0 => by simpa using List.Forall₂.cons h t
  | _, _, .cons _ t, k + 1 => by
    simp only [List.drop_succ_cons]
    exact forall₂_drop t k

theorem List.nodup_map_inj {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, hnd, x, y, hx, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with hx' | hx' <;> rcases List.mem_cons.mp hy with hy' | hy'
    · exact hx'.trans hy'.symm
    · subst hx'; exact absurd ⟨y, hy', hxy.symm⟩ hnd.1
    · subst hy'; exact absurd ⟨x, hx', hxy⟩ hnd.1
    · exact nodup_map_inj hnd.2 hx' hy' hxy

end Lean4Lean
