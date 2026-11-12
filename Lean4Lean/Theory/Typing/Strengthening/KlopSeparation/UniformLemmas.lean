import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Uniform

/-! # Basic properties of uniform sections

Monotonicity of `LvLe`, `Small`, `DpLe`; the unfolding of `Lf`; reindexing of worlds;
independence of the recursion bound (`Lf.fuel`).
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower
universe u
variable {𝕋 : UniverseTower.{u}}

local infix:50 " ∈ₛ " => 𝕋.mem

theorem kind_unique {X : 𝕋.S} {a b : Nat} (h1 : 𝕋.kind X = 𝕋.tagN a) (h2 : 𝕋.kind X = 𝕋.tagN b) :
    a = b := 𝕋.tagN_inj (h1.symm.trans h2)

theorem not_isBase_of_kind {X : 𝕋.S} {a : Nat} (h : 𝕋.kind X = 𝕋.tagN a) (ha : 3 ≤ a) :
    ¬ 𝕋.IsBase X := by
  rintro (h' | h' | h') <;> have := kind_unique h h' <;> omega

theorem LvLe.mono {N N' : Nat} (h : N ≤ N') {X : 𝕋.S} (H : 𝕋.LvLe N X) : 𝕋.LvLe N' X := by
  induction H with
  | base hb => exact .base hb
  | univ hk ha hj => exact .univ hk ha (Nat.lt_of_lt_of_le hj h)
  | pi hk _ _ ihD ihF => exact .pi hk ihD ihF
  | piP hk _ ih => exact .piP hk ih

theorem Small.mono {m m' : Nat} (h : m ≤ m') {X : 𝕋.S} (H : 𝕋.Small m X) : 𝕋.Small m' X := by
  rcases H with hb | ⟨n, rfl, hl⟩
  · exact .inl hb
  · obtain ⟨n', rfl⟩ : ∃ n', m' = n' + 1 := ⟨m' - 1, by omega⟩
    exact .inr ⟨n', rfl, hl.mono (by omega)⟩

theorem LvLe.small {N : Nat} {X : 𝕋.S} (H : 𝕋.LvLe N X) : 𝕋.Small (N + 1) X := .inr ⟨N, rfl, H⟩

theorem DpLe.mono {m k k' : Nat} (h : k ≤ k') {X : 𝕋.S} (H : 𝕋.DpLe m X k) : 𝕋.DpLe m X k' := by
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
def Child (𝕋 : UniverseTower.{u}) (X Y : 𝕋.S) : Prop :=
  (𝕋.kind X = 𝕋.tagN 4 ∧ (Y = 𝕋.dom X ∨ ∃ d, 𝕋.mem d (𝕋.El (𝕋.dom X)) ∧ Y = 𝕋.fib X d)) ∨
  (𝕋.kind X = 𝕋.tagN 5 ∧ Y = 𝕋.cod X)

theorem Child.not_isBase {X Y : 𝕋.S} (h : 𝕋.Child X Y) : ¬ 𝕋.IsBase X := by
  rcases h with ⟨hk, -⟩ | ⟨hk, -⟩
  · exact not_isBase_of_kind hk (by omega)
  · exact not_isBase_of_kind hk (by omega)

theorem LvLe.child {N : Nat} {X Y : 𝕋.S} (H : 𝕋.LvLe N X) (hc : 𝕋.Child X Y) : 𝕋.LvLe N Y := by
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

theorem Small.child {m : Nat} {X Y : 𝕋.S} (H : 𝕋.Small m X) (hc : 𝕋.Child X Y) : 𝕋.Small m Y := by
  rcases H with hb | ⟨n, rfl, hl⟩
  · exact (hc.not_isBase hb).elim
  · exact .inr ⟨n, rfl, hl.child hc⟩

theorem DpLe.child_succ {m k : Nat} {X Y : 𝕋.S} (H : 𝕋.DpLe m X (k + 1)) (hc : 𝕋.Child X Y) :
    𝕋.DpLe m Y k := by
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

theorem DpLe.small_of_child_zero {m : Nat} {X Y : 𝕋.S} (H : 𝕋.DpLe m X 0) (hc : 𝕋.Child X Y) :
    𝕋.Small m X := by
  cases H with
  | small hs => exact hs
  | univ hk =>
    rcases hc with ⟨hk', -⟩ | ⟨hk', -⟩ <;> have := kind_unique hk hk' <;> omega

/-! ### The unfolding of `Lf` -/

theorem Lf_iff {b : Nat × Nat} {m : Nat} {I : World.{u}} {H s : I → 𝕋.S} :
    𝕋.Lf b m I H s ↔
    𝕋.Tame m H ∧ 𝕋.FamLe m H b ∧
    (∃ k, ∀ i, 𝕋.kind (H i) = 𝕋.tagN 3 → ¬ 𝕋.Small m (H i) → 𝕋.LvLe m (s i) → 𝕋.DpLe m (s i) k) ∧
    (∀ b', Prod.Lex (· < ·) (· < ·) b' b → ∀ (I' : World.{u}) (φ : I' → I) (a : I' → 𝕋.S),
      (∀ i', 𝕋.kind (H (φ i')) = 𝕋.tagN 4 ∧ ¬ 𝕋.Small m (H (φ i'))) →
      (∀ i', 𝕋.mem (a i') (𝕋.El (𝕋.dom (H (φ i'))))) →
      (∀ m', m ≤ m' → 𝕋.Lf b' m' I' (fun i' => 𝕋.dom (H (φ i'))) a) →
      𝕋.Tame m (fun i' => 𝕋.fib (H (φ i')) (a i')) →
      𝕋.FamLe m (fun i' => 𝕋.fib (H (φ i')) (a i')) b' →
      𝕋.Lf b' m I' (fun i' => 𝕋.fib (H (φ i')) (a i')) (fun i' => 𝕋.ap (s (φ i')) (a i'))) ∧
    (∀ b', Prod.Lex (· < ·) (· < ·) b' b → ∀ (I' : World.{u}) (φ : I' → I),
      (∀ i', 𝕋.kind (H (φ i')) = 𝕋.tagN 5 ∧ ¬ 𝕋.Small m (H (φ i'))) →
      𝕋.Tame m (fun i' => 𝕋.cod (H (φ i'))) →
      𝕋.FamLe m (fun i' => 𝕋.cod (H (φ i'))) b' →
      𝕋.Lf b' m I' (fun i' => 𝕋.cod (H (φ i'))) (fun i' => 𝕋.ap (s (φ i')) 𝕋.star)) := by
  rw [Lf]

theorem Lf.tame {b : Nat × Nat} {m : Nat} {I : World.{u}} {H s : I → 𝕋.S}
    (h : 𝕋.Lf b m I H s) : 𝕋.Tame m H := (Lf_iff.1 h).1

theorem Lf.famLe {b : Nat × Nat} {m : Nat} {I : World.{u}} {H s : I → 𝕋.S}
    (h : 𝕋.Lf b m I H s) : 𝕋.FamLe m H b := (Lf_iff.1 h).2.1

theorem Tame.comp {m : Nat} {I I' : World.{u}} {H : I → 𝕋.S} (h : 𝕋.Tame m H) (φ : I' → I) :
    𝕋.Tame m (fun i' => H (φ i')) :=
  ⟨h.1.imp fun _ hN i' => hN _, fun m' hm => (h.2 m' hm).imp fun _ hk i' => hk _⟩

theorem Tame.mono {m m' : Nat} (hm : m ≤ m') {I : World.{u}} {H : I → 𝕋.S} (h : 𝕋.Tame m H) :
    𝕋.Tame m' H := ⟨h.1, fun m'' h' => h.2 m'' (Nat.le_trans hm h')⟩

theorem FamLe.comp {m : Nat} {b : Nat × Nat} {I I' : World.{u}} {H : I → 𝕋.S}
    (h : 𝕋.FamLe m H b) (φ : I' → I) : 𝕋.FamLe m (fun i' => H (φ i')) b := fun i' => h _

theorem FamLe.mono {m m' : Nat} (hm : m ≤ m') {b : Nat × Nat} {I : World.{u}} {H : I → 𝕋.S}
    (h : 𝕋.FamLe m H b) : 𝕋.FamLe m' H b := fun i hs => h i fun hs' => hs (hs'.mono hm)

/-- **Reindexing.** -/
theorem Lf.comp {b : Nat × Nat} {m : Nat} {I J : World.{u}} {H s : I → 𝕋.S}
    (h : 𝕋.Lf b m I H s) (ψ : J → I) : 𝕋.Lf b m J (fun j => H (ψ j)) (fun j => s (ψ j)) := by
  obtain ⟨ht, hf, ⟨k, hu⟩, hpi, hpiP⟩ := Lf_iff.1 h
  exact Lf_iff.2 ⟨ht.comp ψ, hf.comp ψ, ⟨k, fun j => hu _⟩,
    fun b' hb I' φ a => hpi b' hb I' (fun i' => ψ (φ i')) a,
    fun b' hb I' φ => hpiP b' hb I' (fun i' => ψ (φ i'))⟩

/-- Over an empty world every section is uniform. -/
theorem Lf_of_isEmpty (b : Nat × Nat) (m : Nat) {I : World.{u}} (hI : I → False) (H s : I → 𝕋.S) :
    𝕋.Lf b m I H s := by
  induction b using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction generalizing m I with
  | _ b ih =>
    exact Lf_iff.2 ⟨⟨⟨0, fun i => (hI i).elim⟩, fun _ _ => ⟨0, fun i => (hI i).elim⟩⟩,
      fun i => (hI i).elim, ⟨0, fun i => (hI i).elim⟩,
      fun b' hb I' φ a _ _ _ _ _ => ih b' hb _ (fun i' => hI (φ i')) _ _,
      fun b' hb I' φ _ _ _ => ih b' hb _ (fun i' => hI (φ i')) _ _⟩

/-- A tame family of children of a family bounded by `b` is bounded by some `b' < b`. -/
theorem exists_famLe_child {m : Nat} {b : Nat × Nat} {I : World.{u}} {P K : I → 𝕋.S}
    (hP : ∀ i, ¬ 𝕋.Small m (P i) ∧ 𝕋.LvLe b.1 (P i) ∧ 𝕋.DpLe b.1 (P i) b.2)
    (hc : ∀ i, 𝕋.Child (P i) (K i)) (hK : 𝕋.Tame m K) (i₀ : I) :
    ∃ b', Prod.Lex (· < ·) (· < ·) b' b ∧ 𝕋.FamLe m K b' := by
  obtain ⟨N, k⟩ := b
  cases k with
  | succ k =>
    exact ⟨(N, k), .right _ (Nat.lt_succ_self k), fun i _ =>
      ⟨(hP i).2.1.child (hc i), (hP i).2.2.child_succ (hc i)⟩⟩
  | zero =>
    have hs : ∀ i, 𝕋.Small N (P i) := fun i => (hP i).2.2.small_of_child_zero (hc i)
    have hN : ∀ i, ∃ N', N = N' + 1 ∧ 𝕋.LvLe N' (P i) := fun i => by
      rcases hs i with hb | h
      · exact ((hc i).not_isBase hb).elim
      · exact h
    obtain ⟨N', rfl, -⟩ := hN i₀
    have hl : ∀ i, 𝕋.LvLe N' (P i) := fun i => by
      obtain ⟨N'', e, h⟩ := hN i
      cases e; exact h
    have hm : m ≤ N' := by
      refine Nat.le_of_not_lt fun hlt => (hP i₀).1 ?_
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact .inr ⟨m', rfl, (hl i₀).mono (by omega)⟩
    obtain ⟨k', hk'⟩ := hK.2 N' hm
    exact ⟨(N', k'), .left _ _ (Nat.lt_succ_self N'), fun i _ =>
      ⟨(hl i).child (hc i), hk' i ((hl i).child (hc i))⟩⟩

theorem FamLe.of_lex {m : Nat} {b b' : Nat × Nat} {I : World.{u}} {K : I → 𝕋.S}
    (h : 𝕋.FamLe m K b) (hb : b = b' ∨ Prod.Lex (· < ·) (· < ·) b b') : 𝕋.FamLe m K b' := by
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
theorem exists_common {m : Nat} {c c₁ c₂ : Nat × Nat} {I : World.{u}} {K₁ K₂ : I → 𝕋.S}
    (h₁ : Prod.Lex (· < ·) (· < ·) c₁ c) (h₂ : Prod.Lex (· < ·) (· < ·) c₂ c)
    (f₁ : 𝕋.FamLe m K₁ c₁) (f₂ : 𝕋.FamLe m K₂ c₂) :
    ∃ c₀, Prod.Lex (· < ·) (· < ·) c₀ c ∧ 𝕋.FamLe m K₁ c₀ ∧ 𝕋.FamLe m K₂ c₀ := by
  rcases lex_total c₁ c₂ with rfl | h | h
  · exact ⟨c₁, h₁, f₁, f₂⟩
  · exact ⟨c₂, h₂, f₁.of_lex (.inr h), f₂⟩
  · exact ⟨c₁, h₁, f₁, f₂.of_lex (.inr h)⟩

/-- **Independence of the bound**, in both directions. -/
theorem Lf.fuel_aux (b₁ : Nat × Nat) : ∀ (b₂ : Nat × Nat) (m : Nat) (I : World.{u})
    (H s : I → 𝕋.S),
    (𝕋.Lf b₁ m I H s → 𝕋.FamLe m H b₂ → 𝕋.Lf b₂ m I H s) ∧
    (𝕋.Lf b₂ m I H s → 𝕋.FamLe m H b₁ → 𝕋.Lf b₁ m I H s) := by
  induction b₁ using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
  | _ b₁ ih =>
    have step : ∀ (c c' : Nat × Nat) (m : Nat) (I : World.{u}) (H s : I → 𝕋.S),
        (∀ c₀, Prod.Lex (· < ·) (· < ·) c₀ c → ∀ d₀, Prod.Lex (· < ·) (· < ·) d₀ c' →
          ∀ (m : Nat) (I : World.{u}) (H s : I → 𝕋.S),
          (𝕋.Lf c₀ m I H s → 𝕋.FamLe m H d₀ → 𝕋.Lf d₀ m I H s) ∧
          (𝕋.Lf d₀ m I H s → 𝕋.FamLe m H c₀ → 𝕋.Lf c₀ m I H s)) →
        𝕋.Lf c m I H s → 𝕋.FamLe m H c' → 𝕋.Lf c' m I H s := by
      intro c c' m I H s conv h hf'
      obtain ⟨ht, hf, hu, hpi, hpiP⟩ := Lf_iff.1 h
      refine Lf_iff.2 ⟨ht, hf', hu, ?_, ?_⟩
      · intro d hd I' φ a hk ha hG hT hF
        by_cases hI' : Nonempty I'
        · obtain ⟨i₀⟩ := hI'
          have hP : ∀ i', ¬ 𝕋.Small m (H (φ i')) ∧ 𝕋.LvLe c.1 (H (φ i')) ∧
              𝕋.DpLe c.1 (H (φ i')) c.2 := fun i' => ⟨(hk i').2, hf _ (hk i').2⟩
          obtain ⟨c₁, hc₁, hfD⟩ := exists_famLe_child (K := fun i' => 𝕋.dom (H (φ i'))) hP
            (fun i' => .inl ⟨(hk i').1, .inl rfl⟩) (hG m (Nat.le_refl m)).tame i₀
          obtain ⟨c₂, hc₂, hfR⟩ := exists_famLe_child
            (K := fun i' => 𝕋.fib (H (φ i')) (a i')) hP
            (fun i' => .inl ⟨(hk i').1, .inr ⟨_, ha i', rfl⟩⟩) hT i₀
          obtain ⟨c₀, hc₀, hfD₀, hfR₀⟩ := exists_common hc₁ hc₂ hfD hfR
          have hG₀ : ∀ m', m ≤ m' → 𝕋.Lf c₀ m' I' (fun i' => 𝕋.dom (H (φ i'))) a :=
            fun m' hm => (conv c₀ hc₀ d hd m' I' _ a).2 (hG m' hm) (hfD₀.mono hm)
          exact (conv c₀ hc₀ d hd m I' _ _).1 (hpi c₀ hc₀ I' φ a hk ha hG₀ hT hfR₀) hF
        · exact Lf_of_isEmpty _ _ (fun i' => hI' ⟨i'⟩) _ _
      · intro d hd I' φ hk hT hF
        by_cases hI' : Nonempty I'
        · obtain ⟨i₀⟩ := hI'
          have hP : ∀ i', ¬ 𝕋.Small m (H (φ i')) ∧ 𝕋.LvLe c.1 (H (φ i')) ∧
              𝕋.DpLe c.1 (H (φ i')) c.2 := fun i' => ⟨(hk i').2, hf _ (hk i').2⟩
          obtain ⟨c₀, hc₀, hfR⟩ := exists_famLe_child (K := fun i' => 𝕋.cod (H (φ i'))) hP
            (fun i' => .inr ⟨(hk i').1, rfl⟩) hT i₀
          exact (conv c₀ hc₀ d hd m I' _ _).1 (hpiP c₀ hc₀ I' φ hk hT hfR) hF
        · exact Lf_of_isEmpty _ _ (fun i' => hI' ⟨i'⟩) _ _
    intro b₂ m I H s
    refine ⟨step b₁ b₂ m I H s fun c₀ hc₀ d₀ _ => ih c₀ hc₀ d₀, ?_⟩
    exact step b₂ b₁ m I H s fun c₀ _ d₀ hd₀ m I H s =>
      ⟨(ih d₀ hd₀ c₀ m I H s).2, (ih d₀ hd₀ c₀ m I H s).1⟩

/-- **Independence of the bound.** -/
theorem Lf.fuel {b₁ b₂ : Nat × Nat} {m : Nat} {I : World.{u}} {H s : I → 𝕋.S}
    (h : 𝕋.Lf b₁ m I H s) (hf : 𝕋.FamLe m H b₂) : 𝕋.Lf b₂ m I H s :=
  (Lf.fuel_aux b₁ b₂ m I H s).1 h hf

/-! ### Small families, full families, covers -/

theorem tame_of_small {m : Nat} {I : World.{u}} {H : I → 𝕋.S} (h : ∀ i, 𝕋.Small m (H i)) :
    𝕋.Tame m H := by
  refine ⟨⟨m, fun i => ?_⟩, fun m' hm => ⟨0, fun i _ => .small ((h i).mono hm)⟩⟩
  rcases h i with hb | ⟨n, rfl, hl⟩
  · exact .base hb
  · exact hl.mono (Nat.le_succ n)

/-- A section of a family of `m`-small types is uniform at level `m`. -/
theorem Lf_of_small (b : Nat × Nat) {m : Nat} {I : World.{u}} {H : I → 𝕋.S}
    (h : ∀ i, 𝕋.Small m (H i)) (s : I → 𝕋.S) : 𝕋.Lf b m I H s :=
  Lf_iff.2 ⟨tame_of_small h, fun i hs => (hs (h i)).elim, ⟨0, fun i _ hs => (hs (h i)).elim⟩,
    fun _ _ I' φ a hk _ _ _ _ =>
      Lf_of_isEmpty _ _ (fun i' => (hk i').2 (h _)) _ _,
    fun _ _ I' φ hk _ _ => Lf_of_isEmpty _ _ (fun i' => (hk i').2 (h _)) _ _⟩

/-- **Every section of a family of bounded depth in `𝒰ₘ` is uniform at level `m`** (U3).
`Q` is a class of types closed under children whose universes have elements of lower level. -/
theorem Lf_full (Q : 𝕋.S → Prop) (hQc : ∀ X Y, Q X → 𝕋.Child X Y → Q Y)
    (hQu : ∀ X (j : Nat) x, Q X → 𝕋.kind X = 𝕋.tagN 3 → 𝕋.argsOf X = 𝕋.enc j →
      𝕋.mem x (𝕋.El X) → 𝕋.LvLe j x)
    (hQap : ∀ X f d, Q X → 𝕋.kind X = 𝕋.tagN 4 → 𝕋.mem f (𝕋.El X) →
      𝕋.mem d (𝕋.El (𝕋.dom X)) → 𝕋.mem (𝕋.ap f d) (𝕋.El (𝕋.fib X d)))
    (hQapP : ∀ X f, Q X → 𝕋.kind X = 𝕋.tagN 5 → 𝕋.mem f (𝕋.El X) →
      𝕋.mem (𝕋.ap f 𝕋.star) (𝕋.El (𝕋.cod X)))
    (m : Nat) : ∀ (k : Nat) (I : World.{u}) (H s : I → 𝕋.S),
    (∀ i, Q (H i) ∧ 𝕋.LvLe m (H i) ∧ 𝕋.DpLe m (H i) k ∧ 𝕋.mem (s i) (𝕋.El (H i))) →
    𝕋.Lf (m, k) m I H s := by
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
      have hc : ∀ i', 𝕋.Child (H (φ i')) (𝕋.fib (H (φ i')) (a i')) :=
        fun i' => .inl ⟨(hk i').1, .inr ⟨_, ha i', rfl⟩⟩
      refine (ih I' _ _ fun i' => ?_).fuel hF
      obtain ⟨hq, hl, hd, hs⟩ := h (φ i')
      exact ⟨hQc _ _ hq (hc i'), hl.child (hc i'), hd.child_succ (hc i'),
        hQap _ _ _ hq (hk i').1 hs (ha i')⟩
    · intro b' _ I' φ hk _ hF
      have hc : ∀ i', 𝕋.Child (H (φ i')) (𝕋.cod (H (φ i'))) :=
        fun i' => .inr ⟨(hk i').1, rfl⟩
      refine (ih I' _ _ fun i' => ?_).fuel hF
      obtain ⟨hq, hl, hd, hs⟩ := h (φ i')
      exact ⟨hQc _ _ hq (hc i'), hl.child (hc i'), hd.child_succ (hc i'),
        hQapP _ _ hq (hk i').1 hs⟩

end UniverseTower

end VEnv.Strengthening
end Lean4Lean
