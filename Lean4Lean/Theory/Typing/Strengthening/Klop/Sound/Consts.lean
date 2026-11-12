import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.Spine

/-! # Soundness: constants

`ConstOK`: a constant denotes an element of the denotation of its declared type, and its
value realizes that type when it is a proposition. `sem_const_of` turns this into the
semantic judgment of the constant rule. The constants `T`, `E`, `P`, `C` and `Fix` are
treated here; `Eq.refl` and `H` in `EqReflH.lean`, `Eq` in `Eq.lean` and `Eq.rec` in
`EqRec.lean` and `EqRecVal.lean`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

theorem constVal_subst (c : Name) (σ : Nat → PVal) : (constVal c).subst σ = constVal c := by
  unfold constVal
  split
  · rfl
  · split
    · simp [recVal, PVal.subst, PVal.up_eq_upN, PVal.upN, PVal.liftN, liftVar]
    · rfl

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

/-- A constant is an element of its declared type, with a realizing value. -/
def ConstOK (𝕊 : SetModel) (c : Name) (ls : List VLevel) (ty : VExpr) : Prop :=
  ∀ ρ : Nat → 𝕊.S, 𝕊.mem (𝕊.constDen c ls) (𝕊.El (𝕊.den ρ ty)) ∧
    (𝕊.IsCand (𝕊.den ρ ty) → (𝕊.candOf (𝕊.den ρ ty)).mem (constVal c))

/-- The constant rule, from `ConstOK`. -/
theorem sem_const_of {Γ : List VExpr} {c : Name} {ls ls' : List VLevel} {ty ty' : VExpr}
    {u : VLevel} (hOK : 𝕊.ConstOK c ls ty) (hcongr : 𝕊.constDen c ls = 𝕊.constDen c ls')
    (HT : 𝕊.Sem Γ ty ty' (.sort u)) : 𝕊.Sem Γ (.const c ls) (.const c ls') ty := by
  intro ρ w hρ
  obtain ⟨-, -, hTm, -, hTr⟩ := HT ρ w hρ
  obtain ⟨hm, hv⟩ := hOK ρ
  have hval : (pval (.const c ls)).subst w = constVal c := constVal_subst c w
  have hval' : (pval (.const c ls')).subst w = constVal c := constVal_subst c w
  refine ⟨isSemTy_of_mem_sortDen hTm, hcongr, hm, fun hc => ?_, fun ρ' w' hρ' hr => ?_⟩
  · rw [hval, hval']; exact ⟨hv hc, hv hc⟩
  · refine ⟨(tyRel_of_rel_sortDen hTm (hTr ρ' w' hρ' hr).2).2, ?_⟩
    exact (mem_sortDen hTm).1.isPER.refl _ hm

/-! ### The Klop constants -/

theorem den_klopT (ρ : Nat → 𝕊.S) : 𝕊.den ρ (.const `Klop.T []) = 𝕊.tT := by
  simp [den, constDen]

theorem den_klopP (ρ : Nat → 𝕊.S) : 𝕊.den ρ (.const `Klop.P []) = 𝕊.cand Candidate.empty := by
  simp [den, constDen]

theorem tsucc_mem {d : 𝕊.S} (hd : d ∈ₛ 𝕊.El 𝕊.tT) : 𝕊.tsucc d ∈ₛ 𝕊.El 𝕊.tT := by
  obtain ⟨i, rfl⟩ := 𝕊.mem_El_tT.1 hd
  rw [tsucc_tval]; exact 𝕊.mem_El_tT.2 ⟨_, rfl⟩

/-- `T : Type`. -/
theorem constOK_T (ls : List VLevel) : 𝕊.ConstOK `Klop.T ls (.sort (.succ .zero)) := by
  intro ρ
  have h : 𝕊.constDen `Klop.T ls = 𝕊.tT := by simp [constDen]
  rw [h]
  exact ⟨(ValidAny.tT (lower := 𝕊.univList 0)).mem_univ fun hc => (not_isCand_tT hc).elim,
    fun hc => (not_isCand_univ 0 hc).elim⟩

/-- `E : T`. -/
theorem constOK_E (ls : List VLevel) : 𝕊.ConstOK `Klop.E ls (.const `Klop.T []) := by
  intro ρ
  have h : 𝕊.constDen `Klop.E ls = 𝕊.tval 0 := by simp [constDen]
  rw [h, den_klopT]
  exact ⟨𝕊.mem_El_tT.2 ⟨0, rfl⟩, fun hc => (not_isCand_tT hc).elim⟩

/-- `P : Prop`. -/
theorem constOK_P (ls : List VLevel) : 𝕊.ConstOK `Klop.P ls (.sort .zero) := by
  intro ρ
  have h : 𝕊.constDen `Klop.P ls = 𝕊.cand Candidate.empty := by simp [constDen]
  rw [h]
  exact ⟨mem_El_tProp.2 ⟨_, Candidate.good_empty, rfl⟩, fun hc => (not_isCand_tProp hc).elim⟩

theorem mkPi_tT_tT : 𝕊.mkPi 𝕊.tT (fun _ => 𝕊.tT) = 𝕊.tPi 𝕊.tT (fun _ => 𝕊.tT) := by
  have h0 : 𝕊.tval 0 ∈ₛ 𝕊.El 𝕊.tT := 𝕊.mem_El_tT.2 ⟨0, rfl⟩
  rw [mkPi, if_neg not_isCand_tT, if_neg fun h => not_isCand_tT (h _ h0)]

/-- `C : T → T`. -/
theorem constOK_C (ls : List VLevel) :
    𝕊.ConstOK `Klop.C ls (.forallE (.const `Klop.T []) (.const `Klop.T [])) := by
  intro ρ
  have h : 𝕊.constDen `Klop.C ls = 𝕊.mkLam 𝕊.tT 𝕊.tsucc := by simp [constDen]
  have hden : 𝕊.den ρ (.forallE (.const `Klop.T []) (.const `Klop.T [])) =
      𝕊.mkPi 𝕊.tT (fun _ => 𝕊.tT) := by
    show 𝕊.mkPi _ _ = _
    simp only [den_klopT]
  rw [h, hden]
  refine ⟨mkLam_mem_mkPi (n := 0) (fun _ _ => .tT) (fun d hd => tsucc_mem hd)
    (fun d d' hd h => (rel_tT_iff hd).1 h)
    (fun d d' hd h => 𝕊.rel_tT (tsucc_mem hd) (tsucc_mem ((rel_tT_iff hd).1 h)))
    (piUnif_of_flat (n := 0) _ (mkPi_valid .tT (fun _ _ => .tT) (fun _ _ _ _ => rfl)
      (.inl fun _ _ hc => (not_isCand_tT hc).elim) fun _ => famUnif_of_base fun _ _ =>
        .inr (.inl kind_tT)) fun _ _ => flat_tT), fun hc => ?_⟩
  rw [mkPi_tT_tT] at hc
  exact absurd hc (not_isCand_of_kind (kind_tPi ..) (by decide))

/-- `Fix : P → T`. -/
theorem constOK_Fix (ls : List VLevel) :
    𝕊.ConstOK `Klop.Fix ls (.forallE (.const `Klop.P []) (.const `Klop.T [])) := by
  intro ρ
  have h : 𝕊.constDen `Klop.Fix ls = 𝕊.star := by simp [constDen]
  have hden : 𝕊.den ρ (.forallE (.const `Klop.P []) (.const `Klop.T [])) =
      𝕊.cand Candidate.full := by
    show 𝕊.mkPi _ _ = _
    rw [den_klopP]
    refine mkPi_of_empty fun ⟨d, hd⟩ => ?_
    obtain ⟨-, v, hv⟩ := 𝕊.mem_El_cand.1 hd
    exact hv
  rw [h, hden]
  exact ⟨star_mem_cand ⟨.bot, trivial⟩, fun _ => by rw [𝕊.candOf_cand]; trivial⟩

/-! ### Level congruence -/

theorem getD_equiv {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls') (i : Nat) :
    ls.getD i .zero ≈ ls'.getD i .zero := by
  induction h generalizing i with
  | nil => exact rfl
  | cons hx _ ih =>
    cases i with
    | zero => exact hx
    | succ i => exact ih i

theorem eqDen_congr {u u' : VLevel} (h : u ≈ u') : 𝕊.eqDen u = 𝕊.eqDen u' := by
  simp only [eqDen, sortDen_congr h]

theorem recDen_congr {v v' u u' : VLevel} (hv : v ≈ v') (hu : u ≈ u') :
    𝕊.recDen v u = 𝕊.recDen v' u' := by
  simp only [recDen, motiveTy, sortDen_congr hv, sortDen_congr hu]

/-- Equivalent universe levels give the same denotation of a constant. -/
theorem constDen_congr {c : Name} {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls') :
    𝕊.constDen c ls = 𝕊.constDen c ls' := by
  unfold constDen
  split
  · exact eqDen_congr (getD_equiv h 0)
  · split
    · exact recDen_congr (getD_equiv h 0) (getD_equiv h 1)
    · rfl

end SetModel
end VEnv.Strengthening
end Lean4Lean
