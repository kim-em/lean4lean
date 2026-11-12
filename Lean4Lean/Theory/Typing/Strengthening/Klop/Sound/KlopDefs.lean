import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.EqRec
import Lean4Lean.Theory.Typing.Strengthening.Klop.Derivation

/-! # Soundness: the definitional equations of `C` and `Fix`

`recDen_app`: `⟦Eq.rec⟧` applied to six arguments in the right sets is `recBody`.
`den_klopFixBody`: the body of `Fix` denotes `•` (an abstraction over the empty proposition).
`den_klopCBody`: the body of `C` denotes the successor function: the `Eq.rec` in it has
endpoints `x` and `x + 1` over `T` with fibre `T`, so `recBody` returns `x + 1`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

/-- `⟦Eq.rec⟧` applied to six arguments is `recBody`. -/
theorem recDen_app {v u : VLevel} {α a M m b t : 𝕊.S}
    (hα : α ∈ₛ 𝕊.El (𝕊.sortDen u)) (ha : a ∈ₛ 𝕊.El α) (hM : M ∈ₛ 𝕊.El (𝕊.motiveTy v α a))
    (hm : m ∈ₛ 𝕊.El (𝕊.mkApp (𝕊.mkApp M a) 𝕊.star)) (hb : b ∈ₛ 𝕊.El α)
    (ht : t ∈ₛ 𝕊.El (𝕊.cand (𝕊.eqCand α a b))) :
    𝕊.mkApp (𝕊.mkApp (𝕊.mkApp (𝕊.mkApp (𝕊.mkApp (𝕊.mkApp (𝕊.recDen v u) α) a) M) m) b) t =
      𝕊.recBody α a M m b := by
  rw [recDen, 𝕊.mkApp_mkLam hα, 𝕊.mkApp_mkLam ha, 𝕊.mkApp_mkLam hM, 𝕊.mkApp_mkLam hm,
    𝕊.mkApp_mkLam hb, 𝕊.mkApp_mkLam ht]

/-- The body of `Fix` denotes `•`. -/
theorem den_klopFixBody (ρ : Nat → 𝕊.S) : 𝕊.den ρ klopFixBody = 𝕊.star := by
  show 𝕊.mkLam (𝕊.den ρ (.const `Klop.P [])) _ = _
  rw [den_klopP, mkLam, if_pos]
  intro d hd
  obtain ⟨-, v, hv⟩ := 𝕊.mem_El_cand.1 hd
  exact hv.elim

theorem den_klopFix (ρ : Nat → 𝕊.S) : 𝕊.den ρ klopFix = 𝕊.star := by
  simp [den, constDen]

theorem den_klopC (ρ : Nat → 𝕊.S) : 𝕊.den ρ klopC = 𝕊.mkLam 𝕊.tT 𝕊.tsucc := by
  simp [den, constDen]

/-- The constant motive `fun y _ => T` at an element `x` of `T`. -/
noncomputable def constMotive (𝕊 : SetModel) (x : 𝕊.S) : 𝕊.S :=
  𝕊.mkLam 𝕊.tT fun y => 𝕊.mkLam (𝕊.cand (𝕊.eqCand 𝕊.tT x y)) fun _ => 𝕊.tT

theorem star_mem_eqCand_tT {x y : 𝕊.S} (hx : x ∈ₛ 𝕊.El 𝕊.tT) (hy : y ∈ₛ 𝕊.El 𝕊.tT) :
    𝕊.star ∈ₛ 𝕊.El (𝕊.cand (𝕊.eqCand 𝕊.tT x y)) :=
  star_mem_cand ⟨.bot, eqCand_mem_of_toBot hx (𝕊.rel_tT hx hy) .rfl⟩

/-- The fibres of the constant motive are `T`. -/
theorem fib_constMotive {x y : 𝕊.S} (hx : x ∈ₛ 𝕊.El 𝕊.tT) (hy : y ∈ₛ 𝕊.El 𝕊.tT) :
    𝕊.mkApp (𝕊.mkApp (𝕊.constMotive x) y) 𝕊.star = 𝕊.tT := by
  rw [constMotive, 𝕊.mkApp_mkLam hy, 𝕊.mkApp_mkLam (star_mem_eqCand_tT hx hy)]

/-- The constant motive is an element of the motive type. -/
theorem constMotive_mem {x : 𝕊.S} (hx : x ∈ₛ 𝕊.El 𝕊.tT) :
    𝕊.constMotive x ∈ₛ 𝕊.El (𝕊.motiveTy (.succ .zero) 𝕊.tT x) := by
  have hT : 𝕊.tT ∈ₛ 𝕊.El (𝕊.sortDen (.succ .zero)) := tT_mem_sort1
  have hTr : 𝕊.Rel (𝕊.sortDen (.succ .zero)) 𝕊.tT 𝕊.tT := rel_sortDen_of_tyRel hT hT rfl
  have hinner : ∀ z, (𝕊.mkLam (𝕊.cand (𝕊.eqCand 𝕊.tT x z)) fun _ => 𝕊.tT) ∈ₛ
      𝕊.El (𝕊.fibTy (.succ .zero) 𝕊.tT x z) := fun z =>
    mkLam_mem_mkPi (n := 1) (fun _ _ => (sortDen_valid (.succ .zero)))
      (fun _ _ => hT) (fun d d' hd h => (rel_cand hd).1 h) (fun _ _ _ _ => hTr)
      (fun h => (h ⟨_, rfl⟩).elim)
  have hfv : ∀ y, 𝕊.Valid (𝕊.fibTy (.succ .zero) 𝕊.tT x y) := fun y =>
    ⟨1, fibTy_valid (v := .succ .zero) (n := 1) (Nat.le_refl 1) 𝕊.tT x y⟩
  have hu : ¬ 𝕊.IsCand 𝕊.tT →
      (¬ ∀ d, d ∈ₛ 𝕊.El 𝕊.tT → 𝕊.IsCand (𝕊.fibTy (.succ .zero) 𝕊.tT x d)) →
      𝕊.PiUnif 𝕊.tT (𝕊.fibTy (.succ .zero) 𝕊.tT x)
        (𝕊.fn (𝕊.El 𝕊.tT) fun y => 𝕊.mkLam (𝕊.cand (𝕊.eqCand 𝕊.tT x y)) fun _ => 𝕊.tT) :=
    fun hDc hall => piUnif_of_unif_mk (fun y _ => hfv y) (fun y _ => hinner y)
      (unif_mkLam (I := PUnit) (D := fun _ => 𝕊.tT)
        (F := fun _ y => 𝕊.fibTy (.succ .zero) 𝕊.tT x y)
        (f := fun _ y => 𝕊.mkLam (𝕊.cand (𝕊.eqCand 𝕊.tT x y)) fun _ => 𝕊.tT)
        (fun _ y _ => hfv y) (fun _ y _ => hinner y)
        ((motiveTy_valid (v := .succ .zero) (n := 1) (Nat.le_refl 1) .tT x).tame_const 0 _)
        (fun m' _ I' φ a ha hu' hTr =>
          (unif_mkLam (D := fun i' => 𝕊.cand (𝕊.eqCand 𝕊.tT x (a i')))
            (F := fun _ _ => 𝕊.sortDen (.succ .zero)) (f := fun _ _ => 𝕊.tT)
            (fun _ _ _ => ⟨_, sortDen_valid (.succ .zero)⟩) (fun _ _ _ => hT) hTr
            (fun m'' _ I'' _ _ _ _ _ =>
              (sortDen_valid (.succ .zero)).unif_const I'' hT m'' (Nat.zero_le _)))
            m' (Nat.le_refl _))) hDc hall
  refine mkLam_mem_mkPi (n := 1)
    (fun y _ => fibTy_valid (v := .succ .zero) (n := 1) (Nat.le_refl 1) 𝕊.tT x y)
    (fun y hy => ?_) (fun y y' hy h => (rel_tT_iff hy).1 h) (fun y y' hy h => ?_) hu
  · exact mkLam_mem_mkPi (n := 1) (fun _ _ => (sortDen_valid (.succ .zero)))
      (fun _ _ => hT) (fun d d' hd h => (rel_cand hd).1 h) (fun _ _ _ _ => hTr)
      (fun h => (h ⟨_, rfl⟩).elim)
  · have hy' := (rel_tT_iff hy).1 h
    have hmem : ∀ z, z ∈ₛ 𝕊.El 𝕊.tT →
        (𝕊.mkLam (𝕊.cand (𝕊.eqCand 𝕊.tT x z)) fun _ => 𝕊.tT) ∈ₛ
          𝕊.El (𝕊.fibTy (.succ .zero) 𝕊.tT x z) := fun z _ =>
      mkLam_mem_mkPi (n := 1) (fun _ _ => (sortDen_valid (.succ .zero)))
        (fun _ _ => hT) (fun d d' hd h => (rel_cand hd).1 h) (fun _ _ _ _ => hTr)
      (fun h => (h ⟨_, rfl⟩).elim)
    have hT2 : 𝕊.TyRel (𝕊.fibTy (.succ .zero) 𝕊.tT x y) (𝕊.fibTy (.succ .zero) 𝕊.tT x y') :=
      fibTy_tyRel (n := 1) (v := .succ .zero) (Nat.le_refl 1)
        (ValidAny.tT (lower := 𝕊.univList 1)).isPER hy h
    have same :=
      (fibTy_valid (𝕊 := 𝕊) (n := 1) (v := .succ .zero) (Nat.le_refl 1) 𝕊.tT x y).tyRel_same
      (fibTy_valid (v := .succ .zero) (n := 1) (Nat.le_refl 1) 𝕊.tT x y') hT2
    have hmem2 : (𝕊.mkLam (𝕊.cand (𝕊.eqCand 𝕊.tT x y')) fun _ => 𝕊.tT) ∈ₛ
        𝕊.El (𝕊.fibTy (.succ .zero) 𝕊.tT x y) := by rw [same.1]; exact hmem y' hy'
    refine rel_mkPi_of_pointwise (hmem y hy) hmem2 fun d hd => ?_
    have hd' : d ∈ₛ 𝕊.El (𝕊.cand (𝕊.eqCand 𝕊.tT x y')) := by
      rw [(𝕊.mem_El_cand.1 hd).1]; exact star_mem_eqCand_tT hx hy'
    rw [𝕊.mkApp_mkLam hd, 𝕊.mkApp_mkLam hd']
    exact hTr

/-- `recBody` at the constant motive over `T` with endpoints `x` and `x + 1`. -/
theorem recBody_C {x : 𝕊.S} (hx : x ∈ₛ 𝕊.El 𝕊.tT) :
    𝕊.recBody 𝕊.tT x (𝕊.constMotive x) (𝕊.tval 0) (𝕊.tsucc x) = 𝕊.tsucc x := by
  have hfib := fib_constMotive hx (tsucc_mem hx)
  have hne : x ≠ 𝕊.tsucc x := by
    obtain ⟨i, rfl⟩ := 𝕊.mem_El_tT.1 hx
    exact fun h => 𝕊.tsucc_ne i h.symm
  unfold recBody
  rw [hfib, if_neg not_isCand_tT, if_pos ⟨rfl, rfl, hne⟩]

/-- **The body of `C` denotes the successor function.** -/
theorem den_klopCBody (ρ : Nat → 𝕊.S) : 𝕊.den ρ klopCBody = 𝕊.mkLam 𝕊.tT 𝕊.tsucc := by
  show 𝕊.mkLam (𝕊.den ρ (.const `Klop.T [])) _ = _
  rw [den_klopT]
  refine mkLam_congr fun x hx => ?_
  have hT : 𝕊.tT ∈ₛ 𝕊.El (𝕊.sortDen (.succ .zero)) := tT_mem_sort1
  -- the denotations of the six arguments
  have hrec : 𝕊.den (𝕊.cons x ρ) (.const ``Eq.rec [.succ .zero, .succ .zero]) =
      𝕊.recDen (.succ .zero) (.succ .zero) := by simp [den, constDen]
  have hMot : 𝕊.den (𝕊.cons x ρ) (klopMotive (.bvar 0)) = 𝕊.constMotive x := by
    show 𝕊.mkLam (𝕊.den (𝕊.cons x ρ) (.const `Klop.T [])) _ = _
    rw [den_klopT, constMotive]
    refine mkLam_congr fun y hy => ?_
    show 𝕊.mkLam _ _ = _
    have he : 𝕊.den (𝕊.cons y (𝕊.cons x ρ))
        (VExpr.eqApp (.succ .zero) klopT (VExpr.bvar 0).lift (.bvar 0)) =
        𝕊.cand (𝕊.eqCand 𝕊.tT x y) := by
      have := den_eqApp (𝕊 := 𝕊) (ρ := 𝕊.cons y (𝕊.cons x ρ)) (l := .succ .zero)
        (A := .const `Klop.T []) (x := .bvar 1) (y := .bvar 0)
        (by rw [den_klopT]; exact hT) (by rw [den_klopT]; exact hx)
        (by rw [den_klopT]; exact hy)
      rw [den_klopT] at this
      exact this
    rw [he]
    exact mkLam_congr fun _ _ => den_klopT _
  have hE : 𝕊.den (𝕊.cons x ρ) klopE = 𝕊.tval 0 := by simp [den, constDen]
  have hCx : 𝕊.den (𝕊.cons x ρ) (.app klopC (.bvar 0)) = 𝕊.tsucc x := by
    show 𝕊.mkApp (𝕊.den _ klopC) x = _
    rw [den_klopC, 𝕊.mkApp_mkLam hx]
  have hH : 𝕊.den (𝕊.cons x ρ) (.app (.app klopH (.bvar 0)) (.app klopC (.bvar 0))) =
      𝕊.star := by
    have : 𝕊.den (𝕊.cons x ρ) klopH = 𝕊.star := by simp [den, constDen]
    show 𝕊.mkApp (𝕊.mkApp (𝕊.den _ klopH) _) _ = _
    rw [this]; simp [mkApp]
  show 𝕊.mkApp (𝕊.mkApp (𝕊.mkApp (𝕊.mkApp (𝕊.mkApp (𝕊.mkApp
    (𝕊.den (𝕊.cons x ρ) (.const ``Eq.rec [.succ .zero, .succ .zero]))
    (𝕊.den (𝕊.cons x ρ) (.const `Klop.T []))) x)
    (𝕊.den (𝕊.cons x ρ) (klopMotive (.bvar 0)))) (𝕊.den (𝕊.cons x ρ) klopE))
    (𝕊.den (𝕊.cons x ρ) (.app klopC (.bvar 0))))
    (𝕊.den (𝕊.cons x ρ) (.app (.app klopH (.bvar 0)) (.app klopC (.bvar 0)))) = _
  rw [hrec, den_klopT, hMot, hE, hCx, hH]
  rw [recDen_app hT hx (constMotive_mem hx)
    (by rw [fib_constMotive hx hx]; exact 𝕊.mem_El_tT.2 ⟨0, rfl⟩) (tsucc_mem hx)
    (star_mem_eqCand_tT hx (tsucc_mem hx))]
  exact recBody_C hx

end SetModel
end VEnv.Strengthening
end Lean4Lean
