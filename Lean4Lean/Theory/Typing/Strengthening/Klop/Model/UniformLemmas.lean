import Lean4Lean.Theory.Typing.Strengthening.Klop.Model.Uniform

/-! # Properties of uniform sections

Monotonicity of `LvLe`, `Small` and `DpLe`; the unfolding of `Lf` at each kind of record;
reindexing of worlds (`Lf.comp`) and covers (`Lf.cover`); independence of the recursion
bound (`Lf.fuel`); every section of a family of bounded depth in `𝒰ₘ` is uniform at level
`m` (`Lf_full`); and uniformity depends on the family of types only up to similarity
(`Lf.sim`).
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
universe u
variable {𝕊 : SetModel.{u}}

local infix:50 " ∈ₛ " => 𝕊.mem

theorem kind_unique {X : 𝕊.S} {a b : Nat} (h1 : 𝕊.kind X = 𝕊.tagN a) (h2 : 𝕊.kind X = 𝕊.tagN b) :
    a = b := 𝕊.tagN_inj (h1.symm.trans h2)

theorem not_isBase_of_kind {X : 𝕊.S} {a : Nat} (h : 𝕊.kind X = 𝕊.tagN a) (ha : 3 ≤ a) :
    ¬ 𝕊.IsBase X := by
  rintro (h' | h' | h') <;> have := kind_unique h h' <;> omega

theorem LvLe.mono {N N' : Nat} (h : N ≤ N') {X : 𝕊.S} (H : 𝕊.LvLe N X) : 𝕊.LvLe N' X := by
  induction H with
  | base hb => exact .base hb
  | univ hk ha hj => exact .univ hk ha (Nat.lt_of_lt_of_le hj h)
  | pi hk _ _ ihD ihF => exact .pi hk ihD ihF
  | piP hk _ ih => exact .piP hk ih

theorem Small.mono {m m' : Nat} (h : m ≤ m') {X : 𝕊.S} (H : 𝕊.Small m X) : 𝕊.Small m' X := by
  rcases H with hb | ⟨n, rfl, hl⟩
  · exact .inl hb
  · obtain ⟨n', rfl⟩ : ∃ n', m' = n' + 1 := ⟨m' - 1, by omega⟩
    exact .inr ⟨n', rfl, hl.mono (by omega)⟩

theorem LvLe.small {N : Nat} {X : 𝕊.S} (H : 𝕊.LvLe N X) : 𝕊.Small (N + 1) X := .inr ⟨N, rfl, H⟩

theorem DpLe.mono {m k k' : Nat} (h : k ≤ k') {X : 𝕊.S} (H : 𝕊.DpLe m X k) : 𝕊.DpLe m X k' := by
  induction H generalizing k' with
  | small hs => exact .small hs
  | univ hk => exact .univ hk
  | pi hk _ _ ihD ihF =>
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    exact .pi hk (ihD (by omega)) fun d hd => ihF d hd (by omega)
  | piP hk _ ih =>
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    exact .piP hk (ih (by omega))

/-- `Y` is the domain, a fibre or the codomain of the function type record `X`. -/
def Child (𝕊 : SetModel.{u}) (X Y : 𝕊.S) : Prop :=
  (𝕊.kind X = 𝕊.tagN 4 ∧ (Y = 𝕊.dom X ∨ ∃ d, 𝕊.mem d (𝕊.El (𝕊.dom X)) ∧ Y = 𝕊.fib X d)) ∨
  (𝕊.kind X = 𝕊.tagN 5 ∧ Y = 𝕊.cod X)

theorem Child.not_isBase {X Y : 𝕊.S} (h : 𝕊.Child X Y) : ¬ 𝕊.IsBase X := by
  rcases h with ⟨hk, -⟩ | ⟨hk, -⟩
  · exact not_isBase_of_kind hk (by omega)
  · exact not_isBase_of_kind hk (by omega)

theorem LvLe.child {N : Nat} {X Y : 𝕊.S} (H : 𝕊.LvLe N X) (hc : 𝕊.Child X Y) : 𝕊.LvLe N Y := by
  cases H with
  | base hb => exact (hc.not_isBase hb).elim
  | univ hk _ _ =>
    rcases hc with ⟨hk', -⟩ | ⟨hk', -⟩ <;> have := kind_unique hk hk' <;> omega
  | pi hk hD hF =>
    rcases hc with ⟨-, rfl | ⟨d, hd, rfl⟩⟩ | ⟨hk', -⟩
    · exact hD
    · exact hF d hd
    · have := kind_unique hk hk'; omega
  | piP hk hB =>
    rcases hc with ⟨hk', -⟩ | ⟨-, rfl⟩
    · have := kind_unique hk hk'; omega
    · exact hB

theorem Small.child {m : Nat} {X Y : 𝕊.S} (H : 𝕊.Small m X) (hc : 𝕊.Child X Y) : 𝕊.Small m Y := by
  rcases H with hb | ⟨n, rfl, hl⟩
  · exact (hc.not_isBase hb).elim
  · exact .inr ⟨n, rfl, hl.child hc⟩

theorem DpLe.child_succ {m k : Nat} {X Y : 𝕊.S} (H : 𝕊.DpLe m X (k + 1)) (hc : 𝕊.Child X Y) :
    𝕊.DpLe m Y k := by
  cases H with
  | small hs => exact .small (hs.child hc)
  | univ hk =>
    rcases hc with ⟨hk', -⟩ | ⟨hk', -⟩ <;> have := kind_unique hk hk' <;> omega
  | pi hk hD hF =>
    rcases hc with ⟨-, rfl | ⟨d, hd, rfl⟩⟩ | ⟨hk', -⟩
    · exact hD
    · exact hF d hd
    · have := kind_unique hk hk'; omega
  | piP hk hB =>
    rcases hc with ⟨hk', -⟩ | ⟨-, rfl⟩
    · have := kind_unique hk hk'; omega
    · exact hB

theorem DpLe.small_of_child_zero {m : Nat} {X Y : 𝕊.S} (H : 𝕊.DpLe m X 0) (hc : 𝕊.Child X Y) :
    𝕊.Small m X := by
  cases H with
  | small hs => exact hs
  | univ hk =>
    rcases hc with ⟨hk', -⟩ | ⟨hk', -⟩ <;> have := kind_unique hk hk' <;> omega

/-! ### The unfolding of `Lf` -/

theorem Lf_iff {b : Nat × Nat} {m : Nat} {I : World.{u}} {H s : I → 𝕊.S} :
    𝕊.Lf b m I H s ↔
    𝕊.Tame m H ∧ 𝕊.FamLe m H b ∧
    (∃ k, ∀ i, 𝕊.kind (H i) = 𝕊.tagN 3 → ¬ 𝕊.Small m (H i) → 𝕊.LvLe m (s i) → 𝕊.DpLe m (s i) k) ∧
    (∀ b', Prod.Lex (· < ·) (· < ·) b' b → ∀ (I' : World.{u}) (φ : I' → I) (a : I' → 𝕊.S),
      (∀ i', 𝕊.kind (H (φ i')) = 𝕊.tagN 4 ∧ ¬ 𝕊.Small m (H (φ i'))) →
      (∀ i', 𝕊.mem (a i') (𝕊.El (𝕊.dom (H (φ i'))))) →
      (∀ m', m ≤ m' → 𝕊.Lf b' m' I' (fun i' => 𝕊.dom (H (φ i'))) a) →
      𝕊.Tame m (fun i' => 𝕊.fib (H (φ i')) (a i')) →
      𝕊.FamLe m (fun i' => 𝕊.fib (H (φ i')) (a i')) b' →
      𝕊.Lf b' m I' (fun i' => 𝕊.fib (H (φ i')) (a i')) (fun i' => 𝕊.ap (s (φ i')) (a i'))) ∧
    (∀ b', Prod.Lex (· < ·) (· < ·) b' b → ∀ (I' : World.{u}) (φ : I' → I),
      (∀ i', 𝕊.kind (H (φ i')) = 𝕊.tagN 5 ∧ ¬ 𝕊.Small m (H (φ i'))) →
      𝕊.Tame m (fun i' => 𝕊.cod (H (φ i'))) →
      𝕊.FamLe m (fun i' => 𝕊.cod (H (φ i'))) b' →
      𝕊.Lf b' m I' (fun i' => 𝕊.cod (H (φ i'))) (fun i' => 𝕊.ap (s (φ i')) 𝕊.star)) := by
  rw [Lf]

theorem Lf.tame {b : Nat × Nat} {m : Nat} {I : World.{u}} {H s : I → 𝕊.S}
    (h : 𝕊.Lf b m I H s) : 𝕊.Tame m H := (Lf_iff.1 h).1

theorem Lf.famLe {b : Nat × Nat} {m : Nat} {I : World.{u}} {H s : I → 𝕊.S}
    (h : 𝕊.Lf b m I H s) : 𝕊.FamLe m H b := (Lf_iff.1 h).2.1

theorem Tame.comp {m : Nat} {I I' : World.{u}} {H : I → 𝕊.S} (h : 𝕊.Tame m H) (φ : I' → I) :
    𝕊.Tame m (fun i' => H (φ i')) :=
  ⟨h.1.imp fun _ hN _ => hN _, fun m' hm => (h.2 m' hm).imp fun _ hk _ => hk _⟩

theorem Tame.mono {m m' : Nat} (hm : m ≤ m') {I : World.{u}} {H : I → 𝕊.S} (h : 𝕊.Tame m H) :
    𝕊.Tame m' H := ⟨h.1, fun m'' h' => h.2 m'' (Nat.le_trans hm h')⟩

theorem FamLe.comp {m : Nat} {b : Nat × Nat} {I I' : World.{u}} {H : I → 𝕊.S}
    (h : 𝕊.FamLe m H b) (φ : I' → I) : 𝕊.FamLe m (fun i' => H (φ i')) b := fun _ => h _

theorem FamLe.mono {m m' : Nat} (hm : m ≤ m') {b : Nat × Nat} {I : World.{u}} {H : I → 𝕊.S}
    (h : 𝕊.FamLe m H b) : 𝕊.FamLe m' H b := fun i hs => h i fun hs' => hs (hs'.mono hm)

/-- **Reindexing.** -/
theorem Lf.comp {b : Nat × Nat} {m : Nat} {I J : World.{u}} {H s : I → 𝕊.S}
    (h : 𝕊.Lf b m I H s) (ψ : J → I) : 𝕊.Lf b m J (fun j => H (ψ j)) (fun j => s (ψ j)) := by
  obtain ⟨ht, hf, ⟨k, hu⟩, hpi, hpiP⟩ := Lf_iff.1 h
  exact Lf_iff.2 ⟨ht.comp ψ, hf.comp ψ, ⟨k, fun j => hu _⟩,
    fun b' hb I' φ a => hpi b' hb I' (fun i' => ψ (φ i')) a,
    fun b' hb I' φ => hpiP b' hb I' (fun i' => ψ (φ i'))⟩

/-- Over an empty world every section is uniform. -/
theorem Lf_of_isEmpty (b : Nat × Nat) (m : Nat) {I : World.{u}} (hI : I → False) (H s : I → 𝕊.S) :
    𝕊.Lf b m I H s := by
  induction b using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction generalizing m I with
  | _ b ih =>
    exact Lf_iff.2 ⟨⟨⟨0, fun i => (hI i).elim⟩, fun _ _ => ⟨0, fun i => (hI i).elim⟩⟩,
      fun i => (hI i).elim, ⟨0, fun i => (hI i).elim⟩,
      fun b' hb I' φ a _ _ _ _ _ => ih b' hb _ (fun i' => hI (φ i')) _ _,
      fun b' hb I' φ _ _ _ => ih b' hb _ (fun i' => hI (φ i')) _ _⟩

/-- A tame family of children of a family bounded by `b` is bounded by some `b' < b`. -/
theorem exists_famLe_child {m : Nat} {b : Nat × Nat} {I : World.{u}} {P K : I → 𝕊.S}
    (hP : ∀ i, ¬ 𝕊.Small m (P i) ∧ 𝕊.LvLe b.1 (P i) ∧ 𝕊.DpLe b.1 (P i) b.2)
    (hc : ∀ i, 𝕊.Child (P i) (K i)) (hK : 𝕊.Tame m K) (i₀ : I) :
    ∃ b', Prod.Lex (· < ·) (· < ·) b' b ∧ 𝕊.FamLe m K b' := by
  obtain ⟨N, k⟩ := b
  cases k with
  | succ k =>
    exact ⟨(N, k), .right _ (Nat.lt_succ_self k), fun i _ =>
      ⟨(hP i).2.1.child (hc i), (hP i).2.2.child_succ (hc i)⟩⟩
  | zero =>
    have hs : ∀ i, 𝕊.Small N (P i) := fun i => (hP i).2.2.small_of_child_zero (hc i)
    have hN : ∀ i, ∃ N', N = N' + 1 ∧ 𝕊.LvLe N' (P i) := fun i => by
      rcases hs i with hb | h
      · exact ((hc i).not_isBase hb).elim
      · exact h
    obtain ⟨N', rfl, -⟩ := hN i₀
    have hl : ∀ i, 𝕊.LvLe N' (P i) := fun i => by
      obtain ⟨N'', e, h⟩ := hN i
      cases e; exact h
    have hm : m ≤ N' := by
      refine Nat.le_of_not_lt fun hlt => (hP i₀).1 ?_
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact .inr ⟨m', rfl, (hl i₀).mono (by omega)⟩
    obtain ⟨k', hk'⟩ := hK.2 N' hm
    exact ⟨(N', k'), .left _ _ (Nat.lt_succ_self N'), fun i _ =>
      ⟨(hl i).child (hc i), hk' i ((hl i).child (hc i))⟩⟩

theorem FamLe.of_lex {m : Nat} {b b' : Nat × Nat} {I : World.{u}} {K : I → 𝕊.S}
    (h : 𝕊.FamLe m K b) (hb : b = b' ∨ Prod.Lex (· < ·) (· < ·) b b') : 𝕊.FamLe m K b' := by
  rcases hb with rfl | hb
  · exact h
  · intro i hs
    obtain ⟨hl, hd⟩ := h i hs
    cases hb with
    | left _ _ hlt => exact ⟨hl.mono (Nat.le_of_lt hlt), .small (hl.small.mono hlt)⟩
    | right _ hlt => exact ⟨hl, hd.mono (Nat.le_of_lt hlt)⟩

theorem lex_total (a b : Nat × Nat) :
    a = b ∨ Prod.Lex (· < ·) (· < ·) a b ∨ Prod.Lex (· < ·) (· < ·) b a := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  rcases Nat.lt_trichotomy a1 b1 with h | rfl | h
  · exact .inr (.inl (.left _ _ h))
  · rcases Nat.lt_trichotomy a2 b2 with h | rfl | h
    · exact .inr (.inl (.right _ h))
    · exact .inl rfl
    · exact .inr (.inr (.right _ h))
  · exact .inr (.inr (.left _ _ h))

/-- Two bounds below `c` have a common bound below `c`. -/
theorem exists_common {m : Nat} {c c₁ c₂ : Nat × Nat} {I : World.{u}} {K₁ K₂ : I → 𝕊.S}
    (h₁ : Prod.Lex (· < ·) (· < ·) c₁ c) (h₂ : Prod.Lex (· < ·) (· < ·) c₂ c)
    (f₁ : 𝕊.FamLe m K₁ c₁) (f₂ : 𝕊.FamLe m K₂ c₂) :
    ∃ c₀, Prod.Lex (· < ·) (· < ·) c₀ c ∧ 𝕊.FamLe m K₁ c₀ ∧ 𝕊.FamLe m K₂ c₀ := by
  rcases lex_total c₁ c₂ with rfl | h | h
  · exact ⟨c₁, h₁, f₁, f₂⟩
  · exact ⟨c₂, h₂, f₁.of_lex (.inr h), f₂⟩
  · exact ⟨c₁, h₁, f₁, f₂.of_lex (.inr h)⟩

/-- **Independence of the bound**, in both directions. -/
theorem Lf.fuel_aux (b₁ : Nat × Nat) : ∀ (b₂ : Nat × Nat) (m : Nat) (I : World.{u})
    (H s : I → 𝕊.S),
    (𝕊.Lf b₁ m I H s → 𝕊.FamLe m H b₂ → 𝕊.Lf b₂ m I H s) ∧
    (𝕊.Lf b₂ m I H s → 𝕊.FamLe m H b₁ → 𝕊.Lf b₁ m I H s) := by
  induction b₁ using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
  | _ b₁ ih =>
    have step : ∀ (c c' : Nat × Nat) (m : Nat) (I : World.{u}) (H s : I → 𝕊.S),
        (∀ c₀, Prod.Lex (· < ·) (· < ·) c₀ c → ∀ d₀, Prod.Lex (· < ·) (· < ·) d₀ c' →
          ∀ (m : Nat) (I : World.{u}) (H s : I → 𝕊.S),
          (𝕊.Lf c₀ m I H s → 𝕊.FamLe m H d₀ → 𝕊.Lf d₀ m I H s) ∧
          (𝕊.Lf d₀ m I H s → 𝕊.FamLe m H c₀ → 𝕊.Lf c₀ m I H s)) →
        𝕊.Lf c m I H s → 𝕊.FamLe m H c' → 𝕊.Lf c' m I H s := by
      intro c c' m I H s conv h hf'
      obtain ⟨ht, hf, hu, hpi, hpiP⟩ := Lf_iff.1 h
      refine Lf_iff.2 ⟨ht, hf', hu, ?_, ?_⟩
      · intro d hd I' φ a hk ha hG hT hF
        by_cases hI' : Nonempty I'
        · obtain ⟨i₀⟩ := hI'
          have hP : ∀ i', ¬ 𝕊.Small m (H (φ i')) ∧ 𝕊.LvLe c.1 (H (φ i')) ∧
              𝕊.DpLe c.1 (H (φ i')) c.2 := fun i' => ⟨(hk i').2, hf _ (hk i').2⟩
          obtain ⟨c₁, hc₁, hfD⟩ := exists_famLe_child (K := fun i' => 𝕊.dom (H (φ i'))) hP
            (fun i' => .inl ⟨(hk i').1, .inl rfl⟩) (hG m (Nat.le_refl m)).tame i₀
          obtain ⟨c₂, hc₂, hfR⟩ := exists_famLe_child
            (K := fun i' => 𝕊.fib (H (φ i')) (a i')) hP
            (fun i' => .inl ⟨(hk i').1, .inr ⟨_, ha i', rfl⟩⟩) hT i₀
          obtain ⟨c₀, hc₀, hfD₀, hfR₀⟩ := exists_common hc₁ hc₂ hfD hfR
          have hG₀ : ∀ m', m ≤ m' → 𝕊.Lf c₀ m' I' (fun i' => 𝕊.dom (H (φ i'))) a :=
            fun m' hm => (conv c₀ hc₀ d hd m' I' _ a).2 (hG m' hm) (hfD₀.mono hm)
          exact (conv c₀ hc₀ d hd m I' _ _).1 (hpi c₀ hc₀ I' φ a hk ha hG₀ hT hfR₀) hF
        · exact Lf_of_isEmpty _ _ (fun i' => hI' ⟨i'⟩) _ _
      · intro d hd I' φ hk hT hF
        by_cases hI' : Nonempty I'
        · obtain ⟨i₀⟩ := hI'
          have hP : ∀ i', ¬ 𝕊.Small m (H (φ i')) ∧ 𝕊.LvLe c.1 (H (φ i')) ∧
              𝕊.DpLe c.1 (H (φ i')) c.2 := fun i' => ⟨(hk i').2, hf _ (hk i').2⟩
          obtain ⟨c₀, hc₀, hfR⟩ := exists_famLe_child (K := fun i' => 𝕊.cod (H (φ i'))) hP
            (fun i' => .inr ⟨(hk i').1, rfl⟩) hT i₀
          exact (conv c₀ hc₀ d hd m I' _ _).1 (hpiP c₀ hc₀ I' φ hk hT hfR) hF
        · exact Lf_of_isEmpty _ _ (fun i' => hI' ⟨i'⟩) _ _
    intro b₂ m I H s
    refine ⟨step b₁ b₂ m I H s fun c₀ hc₀ d₀ _ => ih c₀ hc₀ d₀, ?_⟩
    exact step b₂ b₁ m I H s fun c₀ _ d₀ hd₀ m I H s =>
      ⟨(ih d₀ hd₀ c₀ m I H s).2, (ih d₀ hd₀ c₀ m I H s).1⟩

/-- **Independence of the bound.** -/
theorem Lf.fuel {b₁ b₂ : Nat × Nat} {m : Nat} {I : World.{u}} {H s : I → 𝕊.S}
    (h : 𝕊.Lf b₁ m I H s) (hf : 𝕊.FamLe m H b₂) : 𝕊.Lf b₂ m I H s :=
  (Lf.fuel_aux b₁ b₂ m I H s).1 h hf

/-! ### Small families, full families, covers -/

theorem tame_of_small {m : Nat} {I : World.{u}} {H : I → 𝕊.S} (h : ∀ i, 𝕊.Small m (H i)) :
    𝕊.Tame m H := by
  refine ⟨⟨m, fun i => ?_⟩, fun m' hm => ⟨0, fun i _ => .small ((h i).mono hm)⟩⟩
  rcases h i with hb | ⟨n, rfl, hl⟩
  · exact .base hb
  · exact hl.mono (Nat.le_succ n)

/-- A section of a family of `m`-small types is uniform at level `m`. -/
theorem Lf_of_small (b : Nat × Nat) {m : Nat} {I : World.{u}} {H : I → 𝕊.S}
    (h : ∀ i, 𝕊.Small m (H i)) (s : I → 𝕊.S) : 𝕊.Lf b m I H s :=
  Lf_iff.2 ⟨tame_of_small h, fun i hs => (hs (h i)).elim, ⟨0, fun i _ hs => (hs (h i)).elim⟩,
    fun _ _ _ _ _ hk _ _ _ _ =>
      Lf_of_isEmpty _ _ (fun i' => (hk i').2 (h _)) _ _,
    fun _ _ _ _ hk _ _ => Lf_of_isEmpty _ _ (fun i' => (hk i').2 (h _)) _ _⟩

/-- **Every section of a family of bounded depth in `𝒰ₘ` is uniform at level `m`**.
`Q` is a class of types closed under children whose universes have elements of lower level. -/
theorem Lf_full (Q : 𝕊.S → Prop) (hQc : ∀ X Y, Q X → 𝕊.Child X Y → Q Y)
    (hQu : ∀ X (j : Nat) x, Q X → 𝕊.kind X = 𝕊.tagN 3 → 𝕊.argsOf X = 𝕊.enc j →
      𝕊.mem x (𝕊.El X) → 𝕊.LvLe j x)
    (hQap : ∀ X f d, Q X → 𝕊.kind X = 𝕊.tagN 4 → 𝕊.mem f (𝕊.El X) →
      𝕊.mem d (𝕊.El (𝕊.dom X)) → 𝕊.mem (𝕊.ap f d) (𝕊.El (𝕊.fib X d)))
    (hQapP : ∀ X f, Q X → 𝕊.kind X = 𝕊.tagN 5 → 𝕊.mem f (𝕊.El X) →
      𝕊.mem (𝕊.ap f 𝕊.star) (𝕊.El (𝕊.cod X)))
    (m : Nat) : ∀ (k : Nat) (I : World.{u}) (H s : I → 𝕊.S),
    (∀ i, Q (H i) ∧ 𝕊.LvLe m (H i) ∧ 𝕊.DpLe m (H i) k ∧ 𝕊.mem (s i) (𝕊.El (H i))) →
    𝕊.Lf (m, k) m I H s := by
  intro k
  induction k with
  | zero =>
    intro I H s h
    refine Lf_iff.2 ⟨?_, fun i _ => ⟨(h i).2.1, (h i).2.2.1⟩, ⟨0, ?_⟩, ?_, ?_⟩
    · refine ⟨⟨m, fun i => (h i).2.1⟩, fun m' hm => ?_⟩
      rcases Nat.lt_or_ge m m' with hlt | hge
      · exact ⟨0, fun i _ => .small ((h i).2.1.small.mono hlt)⟩
      · obtain rfl : m = m' := Nat.le_antisymm hm hge
        exact ⟨0, fun i _ => (h i).2.2.1⟩
    · intro i hk _ _
      obtain ⟨hq, hl, -, hs⟩ := h i
      cases hl with
      | base hb => exact (not_isBase_of_kind hk (by omega) hb).elim
      | univ _ ha hj =>
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact .small (.inr ⟨m', rfl, (hQu _ _ _ hq hk ha hs).mono (by omega)⟩)
      | pi hk' => have := kind_unique hk hk'; omega
      | piP hk' => have := kind_unique hk hk'; omega
    · intro _ _ I' φ a hk _ _ _ _
      exact Lf_of_isEmpty _ _ (fun i' => (hk i').2
        ((h _).2.2.1.small_of_child_zero (.inl ⟨(hk i').1, .inl rfl⟩))) _ _
    · intro _ _ I' φ hk _ _
      exact Lf_of_isEmpty _ _ (fun i' => (hk i').2
        ((h _).2.2.1.small_of_child_zero (.inr ⟨(hk i').1, rfl⟩))) _ _
  | succ k ih =>
    intro I H s h
    refine Lf_iff.2 ⟨?_, fun i _ => ⟨(h i).2.1, (h i).2.2.1⟩, ⟨0, ?_⟩, ?_, ?_⟩
    · refine ⟨⟨m, fun i => (h i).2.1⟩, fun m' hm => ?_⟩
      rcases Nat.lt_or_ge m m' with hlt | hge
      · exact ⟨0, fun i _ => .small ((h i).2.1.small.mono hlt)⟩
      · obtain rfl : m = m' := Nat.le_antisymm hm hge
        exact ⟨k + 1, fun i _ => (h i).2.2.1⟩
    · intro i hk _ _
      obtain ⟨hq, hl, -, hs⟩ := h i
      cases hl with
      | base hb => exact (not_isBase_of_kind hk (by omega) hb).elim
      | univ _ ha hj =>
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        exact .small (.inr ⟨m', rfl, (hQu _ _ _ hq hk ha hs).mono (by omega)⟩)
      | pi hk' => have := kind_unique hk hk'; omega
      | piP hk' => have := kind_unique hk hk'; omega
    · intro b' _ I' φ a hk ha _ _ hF
      have hc : ∀ i', 𝕊.Child (H (φ i')) (𝕊.fib (H (φ i')) (a i')) :=
        fun i' => .inl ⟨(hk i').1, .inr ⟨_, ha i', rfl⟩⟩
      refine (ih I' _ _ fun i' => ?_).fuel hF
      obtain ⟨hq, hl, hd, hs⟩ := h (φ i')
      exact ⟨hQc _ _ hq (hc i'), hl.child (hc i'), hd.child_succ (hc i'),
        hQap _ _ _ hq (hk i').1 hs (ha i')⟩
    · intro b' _ I' φ hk _ hF
      have hc : ∀ i', 𝕊.Child (H (φ i')) (𝕊.cod (H (φ i'))) :=
        fun i' => .inr ⟨(hk i').1, rfl⟩
      refine (ih I' _ _ fun i' => ?_).fuel hF
      obtain ⟨hq, hl, hd, hs⟩ := h (φ i')
      exact ⟨hQc _ _ hq (hc i'), hl.child (hc i'), hd.child_succ (hc i'),
        hQapP _ _ hq (hk i').1 hs⟩

/-! ### Covers and congruence -/

/-- **A section uniform on both parts of a world is uniform.** -/
theorem Lf.cover (b : Nat × Nat) : ∀ (m : Nat) (I : World.{u}) (H s : I → 𝕊.S) (P : I → Prop),
    𝕊.Lf b m {i // P i} (fun i => H i.1) (fun i => s i.1) →
    𝕊.Lf b m {i // ¬ P i} (fun i => H i.1) (fun i => s i.1) → 𝕊.Lf b m I H s := by
  induction b using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
  | _ b ih =>
    intro m I H s P h₁ h₂
    obtain ⟨⟨⟨N₁, hN₁⟩, ht₁⟩, hf₁, ⟨k₁, hu₁⟩, hpi₁, hpiP₁⟩ := Lf_iff.1 h₁
    obtain ⟨⟨⟨N₂, hN₂⟩, ht₂⟩, hf₂, ⟨k₂, hu₂⟩, hpi₂, hpiP₂⟩ := Lf_iff.1 h₂
    refine Lf_iff.2 ⟨⟨⟨max N₁ N₂, fun i => ?_⟩, fun m' hm => ?_⟩, fun i => ?_,
      ⟨max k₁ k₂, fun i => ?_⟩, ?_, ?_⟩
    · by_cases hi : P i
      · exact (hN₁ ⟨i, hi⟩).mono (Nat.le_max_left ..)
      · exact (hN₂ ⟨i, hi⟩).mono (Nat.le_max_right ..)
    · obtain ⟨k₁', h₁'⟩ := ht₁ m' hm
      obtain ⟨k₂', h₂'⟩ := ht₂ m' hm
      refine ⟨max k₁' k₂', fun i hl => ?_⟩
      by_cases hi : P i
      · exact (h₁' ⟨i, hi⟩ hl).mono (Nat.le_max_left ..)
      · exact (h₂' ⟨i, hi⟩ hl).mono (Nat.le_max_right ..)
    · by_cases hi : P i
      · exact hf₁ ⟨i, hi⟩
      · exact hf₂ ⟨i, hi⟩
    · intro hk hs hl
      by_cases hi : P i
      · exact (hu₁ ⟨i, hi⟩ hk hs hl).mono (Nat.le_max_left ..)
      · exact (hu₂ ⟨i, hi⟩ hk hs hl).mono (Nat.le_max_right ..)
    · intro b' hb I' φ a hk ha hG hT hF
      refine ih b' hb m I' _ _ (fun i' => P (φ i')) ?_ ?_
      · exact hpi₁ b' hb {i' // P (φ i')} (fun j => ⟨φ j.1, j.2⟩) (fun j => a j.1)
          (fun j => hk j.1) (fun j => ha j.1) (fun m' hm => (hG m' hm).comp _)
          (hT.comp _) (hF.comp _)
      · exact hpi₂ b' hb {i' // ¬ P (φ i')} (fun j => ⟨φ j.1, j.2⟩) (fun j => a j.1)
          (fun j => hk j.1) (fun j => ha j.1) (fun m' hm => (hG m' hm).comp _)
          (hT.comp _) (hF.comp _)
    · intro b' hb I' φ hk hT hF
      refine ih b' hb m I' _ _ (fun i' => P (φ i')) ?_ ?_
      · exact hpiP₁ b' hb {i' // P (φ i')} (fun j => ⟨φ j.1, j.2⟩)
          (fun j => hk j.1) (hT.comp _) (hF.comp _)
      · exact hpiP₂ b' hb {i' // ¬ P (φ i')} (fun j => ⟨φ j.1, j.2⟩)
          (fun j => hk j.1) (hT.comp _) (hF.comp _)

/-- Two records with the same kind and constructor arguments. -/
def SameArgs (𝕊 : SetModel.{u}) (X X' : 𝕊.S) : Prop :=
  𝕊.kind X = 𝕊.kind X' ∧ 𝕊.argsOf X = 𝕊.argsOf X'

theorem SameArgs.symm {X X' : 𝕊.S} (h : 𝕊.SameArgs X X') : 𝕊.SameArgs X' X := ⟨h.1.symm, h.2.symm⟩
theorem SameArgs.dom {X X' : 𝕊.S} (h : 𝕊.SameArgs X X') : 𝕊.dom X = 𝕊.dom X' := by
  simp [SetModel.dom, h.2]
theorem SameArgs.fib {X X' : 𝕊.S} (h : 𝕊.SameArgs X X') (d : 𝕊.S) : 𝕊.fib X d = 𝕊.fib X' d := by
  simp [SetModel.fib, h.2]
theorem SameArgs.cod {X X' : 𝕊.S} (h : 𝕊.SameArgs X X') : 𝕊.cod X = 𝕊.cod X' := by
  simp [SetModel.cod, h.2]

theorem LvLe.congr {N : Nat} {X X' : 𝕊.S} (h : 𝕊.SameArgs X X') (H : 𝕊.LvLe N X) :
    𝕊.LvLe N X' := by
  cases H with
  | base hb => exact .base (by simpa [IsBase, h.1] using hb)
  | univ hk ha hj => exact .univ (h.1 ▸ hk) (h.2 ▸ ha) hj
  | pi hk hD hF => exact .pi (h.1 ▸ hk) (h.dom ▸ hD) fun d hd => h.fib d ▸ hF d (h.dom ▸ hd)
  | piP hk hB => exact .piP (h.1 ▸ hk) (h.cod ▸ hB)

theorem Small.congr {m : Nat} {X X' : 𝕊.S} (h : 𝕊.SameArgs X X') (H : 𝕊.Small m X) :
    𝕊.Small m X' := by
  rcases H with hb | ⟨n, rfl, hl⟩
  · exact .inl (by simpa [IsBase, h.1] using hb)
  · exact .inr ⟨n, rfl, hl.congr h⟩

theorem DpLe.congr {m k : Nat} {X X' : 𝕊.S} (h : 𝕊.SameArgs X X') (H : 𝕊.DpLe m X k) :
    𝕊.DpLe m X' k := by
  cases H with
  | small hs => exact .small (hs.congr h)
  | univ hk => exact .univ (h.1 ▸ hk)
  | pi hk hD hF => exact .pi (h.1 ▸ hk) (h.dom ▸ hD) fun d hd => h.fib d ▸ hF d (h.dom ▸ hd)
  | piP hk hB => exact .piP (h.1 ▸ hk) (h.cod ▸ hB)

/-- Uniformity depends on the family of types only through kinds and constructor arguments. -/
theorem Lf.congr (b : Nat × Nat) : ∀ (m : Nat) (I : World.{u}) (H H' s : I → 𝕊.S),
    (∀ i, 𝕊.SameArgs (H i) (H' i)) → 𝕊.Lf b m I H s → 𝕊.Lf b m I H' s := by
  induction b using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
  | _ b ih =>
    intro m I H H' s hh h
    obtain ⟨⟨⟨N, hN⟩, ht⟩, hf, ⟨k, hu⟩, hpi, hpiP⟩ := Lf_iff.1 h
    have e1 : ∀ (I' : World.{u}) (φ : I' → I),
        (fun i' => 𝕊.dom (H' (φ i'))) = fun i' => 𝕊.dom (H (φ i')) := fun I' φ =>
      funext fun i' => (hh _).dom.symm
    have e2 : ∀ (I' : World.{u}) (φ : I' → I) (a : I' → 𝕊.S),
        (fun i' => 𝕊.fib (H' (φ i')) (a i')) = fun i' => 𝕊.fib (H (φ i')) (a i') := fun I' φ a =>
      funext fun i' => ((hh _).fib _).symm
    have e3 : ∀ (I' : World.{u}) (φ : I' → I),
        (fun i' => 𝕊.cod (H' (φ i'))) = fun i' => 𝕊.cod (H (φ i')) := fun I' φ =>
      funext fun i' => (hh _).cod.symm
    refine Lf_iff.2 ⟨⟨⟨N, fun i => (hN i).congr (hh i)⟩, fun m' hm => (ht m' hm).imp
      fun k hk i hl => (hk i (hl.congr (hh i).symm)).congr (hh i)⟩,
      fun i hs => ?_, ⟨k, fun i hk hs => hu i ((hh i).1 ▸ hk) fun hs' => hs (hs'.congr (hh i))⟩,
      ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hf i fun hs' => hs (hs'.congr (hh i))
      exact ⟨h1.congr (hh i), h2.congr (hh i)⟩
    · intro b' hb I' φ a hk ha hG hT hF
      rw [e2] at hT hF ⊢
      rw [e1] at hG
      refine hpi b' hb I' φ a (fun i' => ⟨(hh _).1 ▸ (hk i').1, fun hs => (hk i').2
        (hs.congr (hh _))⟩) (fun i' => ?_) hG hT hF
      have := ha i'; rwa [← (hh _).dom] at this
    · intro b' hb I' φ hk hT hF
      rw [e3] at hT hF ⊢
      exact hpiP b' hb I' φ (fun i' => ⟨(hh _).1 ▸ (hk i').1, fun hs => (hk i').2
        (hs.congr (hh _))⟩) hT hF

/-! ### Similar records -/

/-- Two records with the same structure of kinds, universes and domains: what uniformity
reads of a type. Coarsely related valid types are similar. -/
inductive Sim (𝕊 : SetModel.{u}) : 𝕊.S → 𝕊.S → Prop where
  | base {X X'} : 𝕊.IsBase X → 𝕊.IsBase X' → Sim 𝕊 X X'
  | univ {X X'} : 𝕊.kind X = 𝕊.tagN 3 → 𝕊.kind X' = 𝕊.tagN 3 → 𝕊.argsOf X = 𝕊.argsOf X' →
      Sim 𝕊 X X'
  | pi {X X'} : 𝕊.kind X = 𝕊.tagN 4 → 𝕊.kind X' = 𝕊.tagN 4 → Sim 𝕊 (𝕊.dom X) (𝕊.dom X') →
      𝕊.El (𝕊.dom X) = 𝕊.El (𝕊.dom X') →
      (∀ d, 𝕊.mem d (𝕊.El (𝕊.dom X)) → Sim 𝕊 (𝕊.fib X d) (𝕊.fib X' d)) → Sim 𝕊 X X'
  | piP {X X'} : 𝕊.kind X = 𝕊.tagN 5 → 𝕊.kind X' = 𝕊.tagN 5 → Sim 𝕊 (𝕊.cod X) (𝕊.cod X') →
      Sim 𝕊 X X'

theorem Sim.symm {X X' : 𝕊.S} (h : 𝕊.Sim X X') : 𝕊.Sim X' X := by
  induction h with
  | base hb hb' => exact .base hb' hb
  | univ hk hk' ha => exact .univ hk' hk ha.symm
  | pi hk hk' _ hE _ ihD ihF => exact .pi hk' hk ihD hE.symm fun d hd => ihF d (hE ▸ hd)
  | piP hk hk' _ ih => exact .piP hk' hk ih

theorem Sim.isBase {X X' : 𝕊.S} (h : 𝕊.Sim X X') (hb : 𝕊.IsBase X) : 𝕊.IsBase X' := by
  cases h with
  | base _ hb' => exact hb'
  | univ hk => exact (not_isBase_of_kind hk (by omega) hb).elim
  | pi hk => exact (not_isBase_of_kind hk (by omega) hb).elim
  | piP hk => exact (not_isBase_of_kind hk (by omega) hb).elim

theorem Sim.kind_eq {X X' : 𝕊.S} {a : Nat} (h : 𝕊.Sim X X') (ha : 3 ≤ a)
    (hk : 𝕊.kind X = 𝕊.tagN a) : 𝕊.kind X' = 𝕊.tagN a := by
  cases h with
  | base hb => exact (not_isBase_of_kind hk ha hb).elim
  | univ hk₁ hk' => rw [← kind_unique hk₁ hk]; exact hk'
  | pi hk₁ hk' => rw [← kind_unique hk₁ hk]; exact hk'
  | piP hk₁ hk' => rw [← kind_unique hk₁ hk]; exact hk'

theorem LvLe.sim {X X' : 𝕊.S} (h : 𝕊.Sim X X') : ∀ {N : Nat}, 𝕊.LvLe N X → 𝕊.LvLe N X' := by
  induction h with
  | base _ hb' => exact fun _ => .base hb'
  | univ hk hk' ha =>
    intro N H
    cases H with
    | base hb => exact (not_isBase_of_kind hk (by omega) hb).elim
    | univ _ ha' hj => exact .univ hk' (ha ▸ ha') hj
    | pi hk₁ => have := kind_unique hk hk₁; omega
    | piP hk₁ => have := kind_unique hk hk₁; omega
  | pi hk hk' _ hE _ ihD ihF =>
    intro N H
    cases H with
    | base hb => exact (not_isBase_of_kind hk (by omega) hb).elim
    | univ hk₁ => have := kind_unique hk hk₁; omega
    | pi _ hD hF => exact .pi hk' (ihD hD) fun d hd => ihF d (hE ▸ hd) (hF d (hE ▸ hd))
    | piP hk₁ => have := kind_unique hk hk₁; omega
  | piP hk hk' _ ih =>
    intro N H
    cases H with
    | base hb => exact (not_isBase_of_kind hk (by omega) hb).elim
    | univ hk₁ => have := kind_unique hk hk₁; omega
    | pi hk₁ => have := kind_unique hk hk₁; omega
    | piP _ hB => exact .piP hk' (ih hB)

theorem Small.sim {m : Nat} {X X' : 𝕊.S} (h : 𝕊.Sim X X') (H : 𝕊.Small m X) : 𝕊.Small m X' := by
  rcases H with hb | ⟨n, rfl, hl⟩
  · exact .inl (h.isBase hb)
  · exact .inr ⟨n, rfl, hl.sim h⟩

theorem DpLe.sim {m : Nat} {X X' : 𝕊.S} (h : 𝕊.Sim X X') :
    ∀ {k : Nat}, 𝕊.DpLe m X k → 𝕊.DpLe m X' k := by
  induction h with
  | base _ hb' => exact fun _ => .small (.inl hb')
  | univ _ hk' => exact fun _ => .univ hk'
  | @pi X X' hk hk' hD hE hF ihD ihF =>
    intro k H
    cases H with
    | small hs => exact .small (hs.sim (.pi hk hk' hD hE hF))
    | univ hk₁ => have := kind_unique hk hk₁; omega
    | pi _ hD' hF' => exact .pi hk' (ihD hD') fun d hd => ihF d (hE ▸ hd) (hF' d (hE ▸ hd))
    | piP hk₁ => have := kind_unique hk hk₁; omega
  | @piP X X' hk hk' hB ih =>
    intro k H
    cases H with
    | small hs => exact .small (hs.sim (.piP hk hk' hB))
    | univ hk₁ => have := kind_unique hk hk₁; omega
    | pi hk₁ => have := kind_unique hk hk₁; omega
    | piP _ hB' => exact .piP hk' (ih hB')

theorem Tame.sim {m : Nat} {I : World.{u}} {H H' : I → 𝕊.S} (hh : ∀ i, 𝕊.Sim (H i) (H' i))
    (h : 𝕊.Tame m H) : 𝕊.Tame m H' :=
  ⟨h.1.imp fun _ hN i => (hN i).sim (hh i), fun m' hm => (h.2 m' hm).imp fun _ hk i hl =>
    (hk i (hl.sim (hh i).symm)).sim (hh i)⟩

theorem FamLe.sim {m : Nat} {b : Nat × Nat} {I : World.{u}} {H H' : I → 𝕊.S}
    (hh : ∀ i, 𝕊.Sim (H i) (H' i)) (h : 𝕊.FamLe m H b) : 𝕊.FamLe m H' b := fun i hs =>
  let ⟨h1, h2⟩ := h i fun hs' => hs (hs'.sim (hh i))
  ⟨h1.sim (hh i), h2.sim (hh i)⟩

theorem Sim.pi_inv {X X' : 𝕊.S} (h : 𝕊.Sim X X') (hk : 𝕊.kind X = 𝕊.tagN 4) :
    𝕊.Sim (𝕊.dom X) (𝕊.dom X') ∧ 𝕊.El (𝕊.dom X) = 𝕊.El (𝕊.dom X') ∧
    ∀ d, 𝕊.mem d (𝕊.El (𝕊.dom X)) → 𝕊.Sim (𝕊.fib X d) (𝕊.fib X' d) := by
  cases h with
  | base hb => exact (not_isBase_of_kind hk (by omega) hb).elim
  | univ hk₁ => have := kind_unique hk hk₁; omega
  | pi _ _ hD hE hF => exact ⟨hD, hE, hF⟩
  | piP hk₁ => have := kind_unique hk hk₁; omega

theorem Sim.piP_inv {X X' : 𝕊.S} (h : 𝕊.Sim X X') (hk : 𝕊.kind X = 𝕊.tagN 5) :
    𝕊.Sim (𝕊.cod X) (𝕊.cod X') := by
  cases h with
  | base hb => exact (not_isBase_of_kind hk (by omega) hb).elim
  | univ hk₁ => have := kind_unique hk hk₁; omega
  | pi hk₁ => have := kind_unique hk hk₁; omega
  | piP _ _ hB => exact hB

/-- **Uniformity depends on the family of types only up to similarity**. -/
theorem Lf.sim (b : Nat × Nat) : ∀ (m : Nat) (I : World.{u}) (H H' s : I → 𝕊.S),
    (∀ i, 𝕊.Sim (H i) (H' i)) → 𝕊.Lf b m I H s → 𝕊.Lf b m I H' s := by
  induction b using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
  | _ b ih =>
    intro m I H H' s hh h
    obtain ⟨ht, hf, ⟨k, hu⟩, hpi, hpiP⟩ := Lf_iff.1 h
    refine Lf_iff.2 ⟨ht.sim hh, hf.sim hh, ⟨k, fun i hk hs =>
      hu i ((hh i).symm.kind_eq (by omega) hk) fun hs' => hs (hs'.sim (hh i))⟩, ?_, ?_⟩
    · intro b' hb I' φ a hk ha hG hT hF
      have hk₀ : ∀ i', 𝕊.kind (H (φ i')) = 𝕊.tagN 4 ∧ ¬ 𝕊.Small m (H (φ i')) := fun i' =>
        ⟨(hh _).symm.kind_eq (by omega) (hk i').1, fun hs => (hk i').2 (hs.sim (hh _))⟩
      have inv := fun i' => (hh (φ i')).pi_inv (hk₀ i').1
      have ha₀ : ∀ i', 𝕊.mem (a i') (𝕊.El (𝕊.dom (H (φ i')))) := fun i' => by
        rw [(inv i').2.1]; exact ha i'
      have sD : ∀ i', 𝕊.Sim (𝕊.dom (H' (φ i'))) (𝕊.dom (H (φ i'))) := fun i' => (inv i').1.symm
      have sF : ∀ i', 𝕊.Sim (𝕊.fib (H (φ i')) (a i')) (𝕊.fib (H' (φ i')) (a i')) := fun i' =>
        (inv i').2.2 _ (ha₀ i')
      refine ih b' hb m I' _ _ _ sF ?_
      exact hpi b' hb I' φ a hk₀ ha₀ (fun m' hm => ih b' hb m' I' _ _ _ sD (hG m' hm))
        (hT.sim fun i' => (sF i').symm) (hF.sim fun i' => (sF i').symm)
    · intro b' hb I' φ hk hT hF
      have hk₀ : ∀ i', 𝕊.kind (H (φ i')) = 𝕊.tagN 5 ∧ ¬ 𝕊.Small m (H (φ i')) := fun i' =>
        ⟨(hh _).symm.kind_eq (by omega) (hk i').1, fun hs => (hk i').2 (hs.sim (hh _))⟩
      have sB : ∀ i', 𝕊.Sim (𝕊.cod (H (φ i'))) (𝕊.cod (H' (φ i'))) := fun i' =>
        (hh (φ i')).piP_inv (hk₀ i').1
      refine ih b' hb m I' _ _ _ sB ?_
      exact hpiP b' hb I' φ hk₀ (hT.sim fun i' => (sB i').symm) (hF.sim fun i' => (sB i').symm)

theorem Unif.sim {m : Nat} {I : World.{u}} {H H' s : I → 𝕊.S} (hh : ∀ i, 𝕊.Sim (H i) (H' i))
    (h : 𝕊.Unif m I H s) : 𝕊.Unif m I H' s := fun m' hm =>
  (h m' hm).imp fun b hb => Lf.sim b m' I H H' s hh hb

/-! ### Elimination, leaves, and `Unif` -/

theorem exists_famLe_of_tame {m : Nat} {I : World.{u}} {H : I → 𝕊.S} (h : 𝕊.Tame m H) :
    ∃ b, 𝕊.FamLe m H b := by
  obtain ⟨⟨N, hN⟩, ht⟩ := h
  by_cases hm : m ≤ N
  · obtain ⟨k, hk⟩ := ht N hm
    exact ⟨(N, k), fun i _ => ⟨hN i, hk i (hN i)⟩⟩
  · exact ⟨(0, 0), fun i hs => (hs ((hN i).small.mono (by omega))).elim⟩

/-- **Application of a uniform section of Π-types to a uniform section of the domains.** -/
theorem Lf.ap_pi {b : Nat × Nat} {m : Nat} {I : World.{u}} {H s a : I → 𝕊.S}
    (h : 𝕊.Lf b m I H s) (hk : ∀ i, 𝕊.kind (H i) = 𝕊.tagN 4 ∧ ¬ 𝕊.Small m (H i))
    (ha : ∀ i, 𝕊.mem (a i) (𝕊.El (𝕊.dom (H i))))
    (hG : 𝕊.Unif m I (fun i => 𝕊.dom (H i)) a)
    (hT : 𝕊.Tame m (fun i => 𝕊.fib (H i) (a i))) :
    ∃ b', 𝕊.Lf b' m I (fun i => 𝕊.fib (H i) (a i)) (fun i => 𝕊.ap (s i) (a i)) := by
  by_cases hI : Nonempty I
  · obtain ⟨i₀⟩ := hI
    have hf := h.famLe
    have hP : ∀ i, ¬ 𝕊.Small m (H i) ∧ 𝕊.LvLe b.1 (H i) ∧ 𝕊.DpLe b.1 (H i) b.2 :=
      fun i => ⟨(hk i).2, hf _ (hk i).2⟩
    obtain ⟨bD, hD⟩ := hG m (Nat.le_refl m)
    obtain ⟨c₁, hc₁, hfD⟩ := exists_famLe_child (K := fun i => 𝕊.dom (H i)) hP
      (fun i => .inl ⟨(hk i).1, .inl rfl⟩) hD.tame i₀
    obtain ⟨c₂, hc₂, hfR⟩ := exists_famLe_child (K := fun i => 𝕊.fib (H i) (a i)) hP
      (fun i => .inl ⟨(hk i).1, .inr ⟨_, ha i, rfl⟩⟩) hT i₀
    obtain ⟨c₀, hc₀, hfD₀, hfR₀⟩ := exists_common hc₁ hc₂ hfD hfR
    have hG₀ : ∀ m', m ≤ m' → 𝕊.Lf c₀ m' I (fun i => 𝕊.dom (H i)) a := fun m' hm => by
      obtain ⟨b'', h''⟩ := hG m' hm
      exact h''.fuel (hfD₀.mono hm)
    exact ⟨c₀, (Lf_iff.1 h).2.2.2.1 c₀ hc₀ I (fun i => i) a hk ha hG₀ hT hfR₀⟩
  · exact ⟨(0, 0), Lf_of_isEmpty _ _ (fun i => hI ⟨i⟩) _ _⟩

/-- Application of a uniform section of function types out of propositions. -/
theorem Lf.ap_piP {b : Nat × Nat} {m : Nat} {I : World.{u}} {H s : I → 𝕊.S}
    (h : 𝕊.Lf b m I H s) (hk : ∀ i, 𝕊.kind (H i) = 𝕊.tagN 5 ∧ ¬ 𝕊.Small m (H i))
    (hT : 𝕊.Tame m (fun i => 𝕊.cod (H i))) :
    ∃ b', 𝕊.Lf b' m I (fun i => 𝕊.cod (H i)) (fun i => 𝕊.ap (s i) 𝕊.star) := by
  by_cases hI : Nonempty I
  · obtain ⟨i₀⟩ := hI
    have hf := h.famLe
    have hP : ∀ i, ¬ 𝕊.Small m (H i) ∧ 𝕊.LvLe b.1 (H i) ∧ 𝕊.DpLe b.1 (H i) b.2 :=
      fun i => ⟨(hk i).2, hf _ (hk i).2⟩
    obtain ⟨c₀, hc₀, hfR⟩ := exists_famLe_child (K := fun i => 𝕊.cod (H i)) hP
      (fun i => .inr ⟨(hk i).1, rfl⟩) hT i₀
    exact ⟨c₀, (Lf_iff.1 h).2.2.2.2 c₀ hc₀ I (fun i => i) hk hT hfR⟩
  · exact ⟨(0, 0), Lf_of_isEmpty _ _ (fun i => hI ⟨i⟩) _ _⟩

/-- A section of a family of base types and universes is uniform when its values have bounded
depth. -/
theorem Lf_leaf {m N : Nat} {I : World.{u}} {H s : I → 𝕊.S}
    (hk : ∀ i, 𝕊.IsBase (H i) ∨ 𝕊.kind (H i) = 𝕊.tagN 3) (hN : ∀ i, 𝕊.LvLe N (H i))
    (hs : ∃ k, ∀ i, 𝕊.kind (H i) = 𝕊.tagN 3 → ¬ 𝕊.Small m (H i) → 𝕊.LvLe m (s i) →
      𝕊.DpLe m (s i) k) : 𝕊.Lf (N, 0) m I H s := by
  have hd : ∀ m' i, 𝕊.DpLe m' (H i) 0 := fun m' i => by
    rcases hk i with hb | h3
    · exact .small (.inl hb)
    · exact .univ h3
  refine Lf_iff.2 ⟨⟨⟨N, hN⟩, fun m' _ => ⟨0, fun i _ => hd m' i⟩⟩, fun i _ => ⟨hN i, hd N i⟩, hs,
    fun _ _ I' φ a hk' _ _ _ _ => Lf_of_isEmpty _ _ (fun i' => ?_) _ _,
    fun _ _ I' φ hk' _ _ => Lf_of_isEmpty _ _ (fun i' => ?_) _ _⟩
  · rcases hk (φ i') with hb | h3
    · exact not_isBase_of_kind (hk' i').1 (by omega) hb
    · have := kind_unique (hk' i').1 h3; omega
  · rcases hk (φ i') with hb | h3
    · exact not_isBase_of_kind (hk' i').1 (by omega) hb
    · have := kind_unique (hk' i').1 h3; omega

theorem Unif.comp {m : Nat} {I J : World.{u}} {H s : I → 𝕊.S} (h : 𝕊.Unif m I H s) (ψ : J → I) :
    𝕊.Unif m J (fun j => H (ψ j)) (fun j => s (ψ j)) := fun m' hm =>
  (h m' hm).imp fun _ hb => hb.comp ψ

theorem Unif.mono {m m' : Nat} (hm : m ≤ m') {I : World.{u}} {H s : I → 𝕊.S}
    (h : 𝕊.Unif m I H s) : 𝕊.Unif m' I H s := fun m'' h' => h m'' (Nat.le_trans hm h')

/-- A section of a family of types that are small from level `m` on is uniform. -/
theorem unif_of_small {m : Nat} {I : World.{u}} {H : I → 𝕊.S} (h : ∀ i, 𝕊.Small m (H i))
    (s : I → 𝕊.S) : 𝕊.Unif m I H s := fun _ hm =>
  ⟨(0, 0), Lf_of_small _ (fun i => (h i).mono hm) s⟩

/-- **A section uniform on both parts of a world is uniform.** -/
theorem Unif.cover {m : Nat} {I : World.{u}} {H s : I → 𝕊.S} (P : I → Prop)
    (h₁ : 𝕊.Unif m {i // P i} (fun i => H i.1) (fun i => s i.1))
    (h₂ : 𝕊.Unif m {i // ¬ P i} (fun i => H i.1) (fun i => s i.1)) : 𝕊.Unif m I H s := by
  intro m' hm
  obtain ⟨b₁, hb₁⟩ := h₁ m' hm
  obtain ⟨b₂, hb₂⟩ := h₂ m' hm
  obtain ⟨⟨N₁, hN₁⟩, ht₁⟩ := hb₁.tame
  obtain ⟨⟨N₂, hN₂⟩, ht₂⟩ := hb₂.tame
  have hT : 𝕊.Tame m' H := by
    refine ⟨⟨max N₁ N₂, fun i => ?_⟩, fun m'' hm'' => ?_⟩
    · by_cases hi : P i
      · exact (hN₁ ⟨i, hi⟩).mono (Nat.le_max_left ..)
      · exact (hN₂ ⟨i, hi⟩).mono (Nat.le_max_right ..)
    · obtain ⟨k₁, h₁'⟩ := ht₁ m'' hm''
      obtain ⟨k₂, h₂'⟩ := ht₂ m'' hm''
      refine ⟨max k₁ k₂, fun i hl => ?_⟩
      by_cases hi : P i
      · exact (h₁' ⟨i, hi⟩ hl).mono (Nat.le_max_left ..)
      · exact (h₂' ⟨i, hi⟩ hl).mono (Nat.le_max_right ..)
  obtain ⟨b, hb⟩ := exists_famLe_of_tame hT
  exact ⟨b, Lf.cover b m' I H s P (hb₁.fuel (hb.comp _)) (hb₂.fuel (hb.comp _))⟩

end SetModel

end VEnv.Strengthening
end Lean4Lean
