import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.SemD

/-! # The body of `Eq.rec` in the model

Semantic facts about `recBody α a M m b`, for a type `α` of `⟦Sort u⟧`, elements `a`, `b` of
`α` that are coarsely related, a motive `M` in `motiveTy v α a` and a minor premise `m` in the
fibre of `M` over `a`:

* the fibres `Fib M x` of the motive over the endpoints coarsely related to `a` are elements
  of `⟦Sort v⟧`, coarsely related for coarsely related endpoints (`fib_rel`);
* `recBody α a M m b` is an element of `Fib M b` (`recBody_mem`): the minor premise lies in
  it because coarsely related fibres have the same elements, and the successor is used only
  when the fibre is `T`;
* `recBody` respects the coarse relations in all its arguments (`recBody_rel`).
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

/-- `(a = x) → Sort v`. -/
noncomputable def fibTy (𝕊 : SetModel) (v : VLevel) (α a x : 𝕊.S) : 𝕊.S :=
  𝕊.mkPi (𝕊.cand (𝕊.eqCand α a x)) fun _ => 𝕊.sortDen v

/-- The fibre of a motive over an endpoint. -/
noncomputable def Fib (𝕊 : SetModel) (M x : 𝕊.S) : 𝕊.S := 𝕊.mkApp (𝕊.mkApp M x) 𝕊.star

theorem sortDen_valid (l : VLevel) : 𝕊.ValidAny (𝕊.univList (l.eval [])) (𝕊.sortDen l) := by
  unfold sortDen
  cases l.eval [] with
  | zero => exact .tProp
  | succ m => exact .univ (univ_mem_univList m)

theorem fibTy_valid {n : Nat} {v : VLevel} (hn : v.eval [] ≤ n) (α a x : 𝕊.S) :
    𝕊.ValidAny (𝕊.univList n) (𝕊.fibTy v α a x) :=
  mkPi_valid (.prop (good_eqCand ..)) (fun _ _ => (sortDen_valid v).mono hn)
    (fun _ _ _ _ => rfl) (.inl fun _ _ hc => (not_isCand_sortDen _ hc).elim)
    (fun h => (h ⟨_, rfl⟩).elim)

/-- `(a = x) → Sort v` has depth at most `1` at every level. -/
theorem dpLe_fibTy (v : VLevel) (α a x : 𝕊.S) (m : Nat) : 𝕊.DpLe m (𝕊.fibTy v α a x) 1 := by
  unfold fibTy
  rcases mkPi_cases (𝕊.cand (𝕊.eqCand α a x)) (fun _ => 𝕊.sortDen v) with
    ⟨hc, -⟩ | ⟨e, -, -, -⟩ | ⟨-, hn, -⟩
  · exact .small (.inl (isBase_of_isCand hc))
  · rw [e]
    refine .piP (kind_tPiP ..) ?_
    rw [cod_tPiP]
    rcases sortDen_leaf (𝕊 := 𝕊) v with hb | hk
    · exact .small (.inl hb)
    · exact .univ hk
  · exact (hn ⟨_, rfl⟩).elim

theorem fibTy_tyRel {n : Nat} {v : VLevel} (hn : v.eval [] ≤ n) {α a x x' : 𝕊.S}
    (hα : 𝕊.IsPER α) (hx : x ∈ₛ 𝕊.El α) (hxx' : 𝕊.Rel α x x') :
    𝕊.TyRel (𝕊.fibTy v α a x) (𝕊.fibTy v α a x') := by
  refine mkPi_tyRel (n := n) (.prop (good_eqCand ..)) (.prop (good_eqCand ..)) ?_
    (fun _ _ => (sortDen_valid v).mono hn) (fun _ _ => (sortDen_valid v).mono hn) fun _ _ => rfl
  refine tyRel_cand.2 ?_
  rw [eqCand_nonempty_iff hα, eqCand_nonempty_iff hα]
  exact and_congr_right fun ha =>
    ⟨fun h => hα.trans _ _ _ ha h hxx', fun h => hα.trans _ _ _ ha h (hα.symm _ _ hx hxx')⟩

theorem motiveTy_valid {n : Nat} {v : VLevel} (hn : v.eval [] ≤ n) {α : 𝕊.S}
    (hα : 𝕊.ValidAny (𝕊.univList n) α) (a : 𝕊.S) :
    𝕊.ValidAny (𝕊.univList n) (𝕊.motiveTy v α a) :=
  mkPi_valid hα (fun x _ => fibTy_valid hn α a x)
    (fun _ _ hx h => fibTy_tyRel hn hα.isPER hx h)
    (.inl fun _ _ hc => mkPi_full hc fun _ _ hc' => (not_isCand_sortDen _ hc').elim)
    (fun _ => famUnif_of_bound (k := 1) fun x _ m => dpLe_fibTy v α a x m)

/-- The fibres of coarsely related motives over coarsely related endpoints are coarsely
related elements of `⟦Sort v⟧`. -/
theorem fib_rel {n : Nat} {v : VLevel} (hn : v.eval [] ≤ n) {α a M M' x x' : 𝕊.S}
    (hα : 𝕊.ValidAny (𝕊.univList n) α) (ha : a ∈ₛ 𝕊.El α)
    (hM : M ∈ₛ 𝕊.El (𝕊.motiveTy v α a)) (hMM' : 𝕊.Rel (𝕊.motiveTy v α a) M M')
    (hx : x ∈ₛ 𝕊.El α) (hax : 𝕊.Rel α a x) (hxx' : 𝕊.Rel α x x') :
    𝕊.Fib M x ∈ₛ 𝕊.El (𝕊.sortDen v) ∧ 𝕊.Rel (𝕊.sortDen v) (𝕊.Fib M x) (𝕊.Fib M' x') := by
  have hs : 𝕊.star ∈ₛ 𝕊.El (𝕊.cand (𝕊.eqCand α a x)) :=
    star_mem_cand ((eqCand_nonempty_iff hα.isPER).2 ⟨ha, hax⟩)
  have h1 : 𝕊.mkApp M x ∈ₛ 𝕊.El (𝕊.fibTy v α a x) := mkApp_mem hM hx
  have h2 : 𝕊.Rel (𝕊.fibTy v α a x) (𝕊.mkApp M x) (𝕊.mkApp M' x') :=
    mkApp_rel (n := n) (fun d _ => fibTy_valid hn α a d) hM hMM' hx hxx'
  refine ⟨mkApp_mem h1 hs, ?_⟩
  exact mkApp_rel (n := n) (fun _ _ => (sortDen_valid v).mono hn) h1 h2 hs ((rel_cand hs).2 hs)

/-- A valid type coarsely related to `T` is `T`. -/
theorem eq_tT_of_tyRel {n : Nat} {A : 𝕊.S} (hA : 𝕊.ValidAny (𝕊.univList n) A)
    (h : 𝕊.TyRel A 𝕊.tT) : A = 𝕊.tT := by
  have hk := hA.kind_eq_of_tyRel (ValidAny.tT) h
  rw [kind_tT] at hk
  cases hA with
  | prop => rw [kind_cand] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
  | tT => rfl
  | tProp => rw [kind_tProp] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
  | univ hu =>
    obtain ⟨m, -, rfl⟩ := mem_univList hu
    rw [SetModel.univ, kind_tU] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
  | pi => rw [kind_tPi] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)
  | piP => rw [kind_tPiP] at hk; exact absurd (𝕊.tagN_inj hk) (by decide)

/-- The hypotheses on the arguments of `Eq.rec`. -/
structure RecArgs (𝕊 : SetModel) (u v : VLevel) (α a M m b : 𝕊.S) : Prop where
  hα : 𝕊.mem α (𝕊.El (𝕊.sortDen u))
  ha : 𝕊.mem a (𝕊.El α)
  hM : 𝕊.mem M (𝕊.El (𝕊.motiveTy v α a))
  hm : 𝕊.mem m (𝕊.El (𝕊.Fib M a))
  hb : 𝕊.mem b (𝕊.El α)
  hab : 𝕊.Rel α a b

/-- The common level of validity. -/
def recLv (u v : VLevel) : Nat := max (sortLv u) (v.eval [])

namespace RecArgs
variable {u v : VLevel} {α a M m b : 𝕊.S} (H : 𝕊.RecArgs u v α a M m b)
include H

theorem αv : 𝕊.ValidAny (𝕊.univList (recLv u v)) α := (mem_sortDen H.hα).1.mono (Nat.le_max_left ..)

theorem motive_refl : 𝕊.Rel (𝕊.motiveTy v α a) M M :=
  (motiveTy_valid (Nat.le_max_right ..) H.αv a).isPER.refl _ H.hM

/-- The fibre over an endpoint coarsely related to `a` is a valid type. -/
theorem fib_valid {x : 𝕊.S} (hx : 𝕊.mem x (𝕊.El α)) (hax : 𝕊.Rel α a x) :
    𝕊.ValidAny (𝕊.univList (recLv u v)) (𝕊.Fib M x) :=
  (mem_sortDen (fib_rel (Nat.le_max_right ..) H.αv H.ha H.hM H.motive_refl hx hax
    (H.αv.isPER.refl _ hx)).1).1.mono (by unfold recLv sortLv; omega)

/-- The fibres over `a` and over `b` are coarsely related. -/
theorem fib_ab : 𝕊.TyRel (𝕊.Fib M a) (𝕊.Fib M b) := by
  have ha := H.ha
  have h := fib_rel (Nat.le_max_right ..) H.αv ha H.hM H.motive_refl ha
    (H.αv.isPER.refl _ ha) H.hab
  exact (tyRel_of_rel_sortDen h.1 h.2).2

theorem fib_a_valid : 𝕊.ValidAny (𝕊.univList (recLv u v)) (𝕊.Fib M a) :=
  H.fib_valid H.ha (H.αv.isPER.refl _ H.ha)

theorem fib_b_valid : 𝕊.ValidAny (𝕊.univList (recLv u v)) (𝕊.Fib M b) := H.fib_valid H.hb H.hab

/-- The minor premise is an element of the fibre over `b`. -/
theorem minor_mem : 𝕊.mem m (𝕊.El (𝕊.Fib M b)) := by
  rw [← (H.fib_a_valid.tyRel_same H.fib_b_valid H.fib_ab).1]; exact H.hm

/-- **`recBody` is an element of the fibre over `b`.** -/
theorem recBody_mem : 𝕊.mem (𝕊.recBody α a M m b) (𝕊.El (𝕊.Fib M b)) := by
  unfold recBody
  by_cases hc : 𝕊.IsCand (𝕊.mkApp (𝕊.mkApp M b) 𝕊.star)
  · rw [if_pos hc]
    have hm := H.minor_mem
    have hc' : 𝕊.IsCand (𝕊.Fib M b) := hc
    rw [isCand_eq hc'] at hm ⊢
    exact star_mem_cand (𝕊.mem_El_cand.1 hm).2
  · rw [if_neg hc]
    by_cases ht : α = 𝕊.tT ∧ 𝕊.mkApp (𝕊.mkApp M b) 𝕊.star = 𝕊.tT ∧ a ≠ b
    · rw [if_pos ht]
      have ha := H.ha
      rw [ht.1] at ha
      show 𝕊.mem _ (𝕊.El (𝕊.mkApp (𝕊.mkApp M b) 𝕊.star))
      rw [ht.2.1]
      exact tsucc_mem ha
    · rw [if_neg ht]; exact H.minor_mem

end RecArgs

/-- **`recBody` respects the coarse relations.** -/
theorem recBody_rel {u v : VLevel} {α a M m b α' a' M' m' b' : 𝕊.S}
    (H : 𝕊.RecArgs u v α a M m b) (H' : 𝕊.RecArgs u v α' a' M' m' b')
    (hMM' : 𝕊.Rel (𝕊.motiveTy v α a) M M') (hmm' : 𝕊.Rel (𝕊.Fib M a) m m')
    (hbb' : 𝕊.Rel α b b') :
    𝕊.Rel (𝕊.Fib M b) (𝕊.recBody α a M m b) (𝕊.recBody α' a' M' m' b') := by
  have hfb := fib_rel (Nat.le_max_right ..) H.αv H.ha H.hM hMM' H.hb H.hab hbb'
  have hT : 𝕊.TyRel (𝕊.Fib M b) (𝕊.Fib M' b') := (tyRel_of_rel_sortDen hfb.1 hfb.2).2
  have hv := H.fib_b_valid
  have hv' := H'.fib_b_valid
  have same := hv.tyRel_same hv' hT
  have per := hv.isPER
  have hmem := H.recBody_mem
  have hmem' : 𝕊.mem (𝕊.recBody α' a' M' m' b') (𝕊.El (𝕊.Fib M b)) := by
    rw [same.1]; exact H'.recBody_mem
  by_cases hc : 𝕊.IsCand (𝕊.Fib M b)
  · rw [isCand_eq hc] at hmem hmem' ⊢
    exact (rel_cand hmem).2 hmem'
  · by_cases htT : 𝕊.Fib M b = 𝕊.tT
    · rw [htT] at hmem hmem' ⊢
      exact 𝕊.rel_tT hmem hmem'
    · -- both sides are the minor premises
      have hc' : ¬ 𝕊.IsCand (𝕊.Fib M' b') := fun h => hc ((hv.isCand_congr hv' hT).2 h)
      have htT' : 𝕊.Fib M' b' ≠ 𝕊.tT := fun h =>
        htT (eq_tT_of_tyRel hv (by rw [← h]; exact hT))
      have e1 : 𝕊.recBody α a M m b = m := by
        unfold recBody
        rw [if_neg (show ¬ 𝕊.IsCand (𝕊.mkApp (𝕊.mkApp M b) 𝕊.star) from hc),
          if_neg fun h => htT h.2.1]
      have e2 : 𝕊.recBody α' a' M' m' b' = m' := by
        unfold recBody
        rw [if_neg (show ¬ 𝕊.IsCand (𝕊.mkApp (𝕊.mkApp M' b') 𝕊.star) from hc'),
          if_neg fun h => htT' h.2.1]
      rw [e1, e2]
      exact ((H.fib_a_valid.tyRel_same hv H.fib_ab).2 _ _ H.hm).1 hmm'

/-- **The fibres of a uniform family of motives over a uniform family of endpoints are a
uniform family of types.** -/
theorem unif_fib {n : Nat} {I : World} {u v : VLevel} {α a M x : I → 𝕊.S}
    (hα : ∀ i, 𝕊.ValidAny (𝕊.univList (recLv u v)) (α i)) (ha : ∀ i, a i ∈ₛ 𝕊.El (α i))
    (hM : ∀ i, M i ∈ₛ 𝕊.El (𝕊.motiveTy v (α i) (a i))) (hx : ∀ i, x i ∈ₛ 𝕊.El (α i))
    (hax : ∀ i, 𝕊.Rel (α i) (a i) (x i))
    (hMu : 𝕊.Unif n I (fun i => 𝕊.motiveTy v (α i) (a i)) M) (hxu : 𝕊.Unif n I α x) :
    𝕊.Unif n I (fun _ => 𝕊.sortDen v) (fun i => 𝕊.Fib (M i) (x i)) := by
  have hT1 : 𝕊.Tame n (fun i => 𝕊.fibTy v (α i) (a i) (x i)) :=
    ⟨⟨recLv u v, fun i => (fibTy_valid (Nat.le_max_right ..) (α i) (a i) (x i)).lvLe⟩,
      fun m' _ => ⟨1, fun i _ => dpLe_fibTy v (α i) (a i) (x i) m'⟩⟩
  have step1 : 𝕊.Unif n I (fun i => 𝕊.fibTy v (α i) (a i) (x i))
      (fun i => 𝕊.mkApp (M i) (x i)) :=
    unif_mkApp (D := α) (F := fun i b => 𝕊.fibTy v (α i) (a i) b) (g := M) (a := x)
      hMu hM hx hxu hT1
  exact unif_mkApp (D := fun i => 𝕊.cand (𝕊.eqCand (α i) (a i) (x i)))
    (F := fun _ _ => 𝕊.sortDen v) (g := fun i => 𝕊.mkApp (M i) (x i)) (a := fun _ => 𝕊.star)
    step1 (fun i => mkApp_mem (hM i) (hx i))
    (fun i => star_mem_cand ((eqCand_nonempty_iff (hα i).isPER).2 ⟨ha i, hax i⟩))
    (unif_of_small (fun i => .inl (.inl (kind_cand _))) _)
    ((sortDen_valid v).tame_const n I)

end SetModel
end VEnv.Strengthening
end Lean4Lean
