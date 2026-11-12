import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.EqReflH

/-! # Soundness: the constant `Eq`

`⟦Eq.{l}⟧` is an element of `⟦∀ α : Sort l, α → α → Prop⟧`: the candidate `eqCand α a b` is
inhabited exactly when `a` and `b` are coarsely related, and this is stable under coarse
relatedness of `b`, of `a` and of `α`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

theorem good_eqCand (α a b : 𝕊.S) : (𝕊.eqCand α a b).Good := by
  unfold eqCand
  split
  · exact Candidate.good_rOrBot
  · split
    · exact Candidate.good_botOnly
    · exact Candidate.good_empty

/-- An equation is inhabited exactly when its endpoints are coarsely related. -/
theorem eqCand_nonempty_iff {α a b : 𝕊.S} (hα : 𝕊.IsPER α) :
    (∃ v, (𝕊.eqCand α a b).mem v) ↔ a ∈ₛ 𝕊.El α ∧ 𝕊.Rel α a b := by
  unfold eqCand
  by_cases h1 : a ∈ₛ 𝕊.El α ∧ a = b
  · rw [if_pos h1]
    obtain ⟨ha, rfl⟩ := h1
    exact ⟨fun _ => ⟨ha, hα.refl _ ha⟩, fun _ => ⟨.r, .inl .rfl⟩⟩
  · rw [if_neg h1]
    by_cases h2 : a ∈ₛ 𝕊.El α ∧ 𝕊.Rel α a b
    · rw [if_pos h2]; exact ⟨fun _ => h2, fun _ => ⟨.bot, .rfl⟩⟩
    · rw [if_neg h2]; exact ⟨fun ⟨_, h⟩ => h.elim, fun h => (h2 h).elim⟩

theorem cand_mem_tProp {c : Candidate} (hc : c.Good) : 𝕊.cand c ∈ₛ 𝕊.El 𝕊.tProp :=
  mem_El_tProp.2 ⟨c, hc, rfl⟩

/-- Two equations with equivalent inhabitation are coarsely related propositions. -/
theorem rel_tProp_eqCand {α a b α' a' b' : 𝕊.S}
    (h : (∃ v, (𝕊.eqCand α a b).mem v) ↔ ∃ v, (𝕊.eqCand α' a' b').mem v) :
    𝕊.Rel 𝕊.tProp (𝕊.cand (𝕊.eqCand α a b)) (𝕊.cand (𝕊.eqCand α' a' b')) :=
  (rel_tProp_iff (cand_mem_tProp (good_eqCand ..))).2
    ⟨cand_mem_tProp (good_eqCand ..), tyRel_cand.2 h⟩

/-- A Π with an element of the domain whose fibre is a data type is a data type. -/
theorem not_isCand_mkPi {D d : 𝕊.S} {F : 𝕊.S → 𝕊.S} (hd : d ∈ₛ 𝕊.El D)
    (hF : ¬ 𝕊.IsCand (F d)) : ¬ 𝕊.IsCand (𝕊.mkPi D F) := by
  intro hc
  unfold mkPi at hc
  by_cases hDc : 𝕊.IsCand D
  · rw [if_pos hDc] at hc
    have hDeq := isCand_eq hDc
    have hds : d = 𝕊.star := by rw [hDeq] at hd; exact (𝕊.mem_El_cand.1 hd).1
    have hne : ∃ v, (𝕊.candOf D).mem v := by rw [hDeq] at hd; exact (𝕊.mem_El_cand.1 hd).2
    subst hds
    rw [if_pos hne, if_neg hF] at hc
    exact absurd hc (not_isCand_of_kind (kind_tPiP ..) (by decide))
  · rw [if_neg hDc] at hc
    by_cases hall : ∀ d, d ∈ₛ 𝕊.El D → 𝕊.IsCand (F d)
    · exact hF (hall d hd)
    · rw [if_neg hall] at hc
      exact absurd hc (not_isCand_of_kind (kind_tPi ..) (by decide))

/-- `α → Prop` as a semantic type. -/
noncomputable def predTy (𝕊 : SetModel) (α : 𝕊.S) : 𝕊.S := 𝕊.mkPi α fun _ => 𝕊.tProp

/-- `α → α → Prop` as a semantic type. -/
noncomputable def relTy (𝕊 : SetModel) (α : 𝕊.S) : 𝕊.S := 𝕊.mkPi α fun _ => 𝕊.predTy α

theorem predTy_valid {n : Nat} {α : 𝕊.S} (hα : 𝕊.ValidAny (𝕊.univList n) α) :
    𝕊.ValidAny (𝕊.univList n) (𝕊.predTy α) :=
  mkPi_valid hα (fun _ _ => .tProp) (fun _ _ _ _ => rfl)
    (.inl fun _ _ hc => (not_isCand_tProp hc).elim)
    (fun _ => famUnif_of_base fun _ _ => .inr (.inr kind_tProp))

theorem relTy_valid {n : Nat} {α : 𝕊.S} (hα : 𝕊.ValidAny (𝕊.univList n) α) :
    𝕊.ValidAny (𝕊.univList n) (𝕊.relTy α) :=
  mkPi_valid hα (fun _ _ => predTy_valid hα) (fun _ _ _ _ => rfl)
    (.inl fun _ _ hc => mkPi_full hc fun _ _ hc' => (not_isCand_tProp hc').elim)
    (fun _ => famUnif_const (predTy_valid hα))

theorem predTy_tyRel {n : Nat} {α α' : 𝕊.S} (hα : 𝕊.ValidAny (𝕊.univList n) α)
    (hα' : 𝕊.ValidAny (𝕊.univList n) α') (h : 𝕊.TyRel α α') :
    𝕊.TyRel (𝕊.predTy α) (𝕊.predTy α') :=
  mkPi_tyRel hα hα' h (fun _ _ => .tProp) (fun _ _ => .tProp) fun _ _ => rfl

theorem relTy_tyRel {n : Nat} {α α' : 𝕊.S} (hα : 𝕊.ValidAny (𝕊.univList n) α)
    (hα' : 𝕊.ValidAny (𝕊.univList n) α') (h : 𝕊.TyRel α α') :
    𝕊.TyRel (𝕊.relTy α) (𝕊.relTy α') :=
  mkPi_tyRel hα hα' h (fun _ _ => predTy_valid hα) (fun _ _ => predTy_valid hα')
    fun _ _ => predTy_tyRel hα hα' h

/-- `fun b => a = b`. -/
noncomputable def eqG (𝕊 : SetModel) (α a : 𝕊.S) : 𝕊.S :=
  𝕊.mkLam α fun b => 𝕊.cand (𝕊.eqCand α a b)

/-- `fun a b => a = b`. -/
noncomputable def eqH (𝕊 : SetModel) (α : 𝕊.S) : 𝕊.S := 𝕊.mkLam α fun a => 𝕊.eqG α a

theorem eqG_mem {n : Nat} {α a : 𝕊.S} (hα : 𝕊.ValidAny (𝕊.univList n) α) (ha : a ∈ₛ 𝕊.El α) :
    𝕊.eqG α a ∈ₛ 𝕊.El (𝕊.predTy α) := by
  have per := hα.isPER
  refine mkLam_mem_mkPi (n := n) (fun _ _ => .tProp)
    (fun b _ => cand_mem_tProp (good_eqCand ..)) (fun b b' hb h => per.mem _ _ hb h)
    (fun b b' hb h => rel_tProp_eqCand ?_)
    (piUnif_of_flat _ (predTy_valid hα) fun _ _ => flat_tProp)
  rw [eqCand_nonempty_iff per, eqCand_nonempty_iff per]
  exact and_congr_right fun _ =>
    ⟨fun h1 => per.trans _ _ _ ha h1 h, fun h1 =>
      per.trans _ _ _ ha h1 (per.symm _ _ hb h)⟩

/-- Coarsely related left endpoints, and coarsely related types, give coarsely related
predicates. -/
theorem eqG_rel {n : Nat} {α α' a a' : 𝕊.S} (hα : 𝕊.ValidAny (𝕊.univList n) α)
    (hα' : 𝕊.ValidAny (𝕊.univList n) α') (hT : 𝕊.TyRel α α') (ha : a ∈ₛ 𝕊.El α)
    (haa' : 𝕊.Rel α a a') : 𝕊.Rel (𝕊.predTy α) (𝕊.eqG α a) (𝕊.eqG α' a') := by
  have per := hα.isPER
  have per' := hα'.isPER
  have same := hα.tyRel_same hα' hT
  have ha' : a' ∈ₛ 𝕊.El α := per.mem _ _ ha haa'
  have hmem' : 𝕊.eqG α' a' ∈ₛ 𝕊.El (𝕊.predTy α) := by
    rw [((predTy_valid hα).tyRel_same (predTy_valid hα') (predTy_tyRel hα hα' hT)).1]
    exact eqG_mem hα' (same.1 ▸ ha')
  refine rel_mkPi_of_pointwise (eqG_mem hα ha) hmem' fun b hb => ?_
  rw [eqG, eqG, 𝕊.mkApp_mkLam hb, 𝕊.mkApp_mkLam (same.1 ▸ hb)]
  refine rel_tProp_eqCand ?_
  rw [eqCand_nonempty_iff per, eqCand_nonempty_iff per', ← same.1, ← same.2 a' b ha']
  exact ⟨fun ⟨_, h⟩ => ⟨ha', per.trans _ _ _ ha' (per.symm _ _ ha haa') h⟩,
    fun ⟨_, h⟩ => ⟨ha, per.trans _ _ _ ha haa' h⟩⟩

theorem eqH_mem {n : Nat} {α : 𝕊.S} (hα : 𝕊.ValidAny (𝕊.univList n) α) :
    𝕊.eqH α ∈ₛ 𝕊.El (𝕊.relTy α) :=
  mkLam_mem_mkPi (n := n) (fun _ _ => predTy_valid hα) (fun _ ha => eqG_mem hα ha)
    (fun _ _ ha h => hα.isPER.mem _ _ ha h) (fun _ _ ha h => eqG_rel hα hα rfl ha h)
    (piUnif_of_flat _ (relTy_valid hα) fun _ _ => flat_mkPi fun _ _ => flat_tProp)

theorem eqH_rel {n : Nat} {α α' : 𝕊.S} (hα : 𝕊.ValidAny (𝕊.univList n) α)
    (hα' : 𝕊.ValidAny (𝕊.univList n) α') (hT : 𝕊.TyRel α α') :
    𝕊.Rel (𝕊.relTy α) (𝕊.eqH α) (𝕊.eqH α') := by
  have same := hα.tyRel_same hα' hT
  have hmem' : 𝕊.eqH α' ∈ₛ 𝕊.El (𝕊.relTy α) := by
    rw [((relTy_valid hα).tyRel_same (relTy_valid hα') (relTy_tyRel hα hα' hT)).1]
    exact eqH_mem hα'
  refine rel_mkPi_of_pointwise (eqH_mem hα) hmem' fun a ha => ?_
  rw [eqH, eqH, 𝕊.mkApp_mkLam ha, 𝕊.mkApp_mkLam (same.1 ▸ ha)]
  exact eqG_rel hα hα' hT ha (hα.isPER.refl _ ha)

/-- `Eq.{l} : ∀ α : Sort l, α → α → Prop`. -/
theorem constOK_Eq (ls : List VLevel) : 𝕊.ConstOK ``Eq ls (canonicalEqType.instL ls) := by
  have hty : canonicalEqType.instL ls =
      .forallE (.sort ((VLevel.param 0).inst ls)) (.forallE (.bvar 0)
        (.forallE (.bvar 1) (.sort .zero))) := by
    simp [canonicalEqType, VExpr.instL, VLevel.inst]
  have hc : 𝕊.constDen ``Eq ls = 𝕊.eqDen (ls.getD 0 .zero) := by simp [constDen]
  have hl : (VLevel.param 0).inst ls = ls.getD 0 .zero := rfl
  rw [hty, hl]
  intro ρ
  rw [hc]
  generalize ls.getD 0 .zero = l
  have hden : 𝕊.den ρ (.forallE (.sort l) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))
      = 𝕊.mkPi (𝕊.sortDen l) fun α => 𝕊.relTy α := rfl
  have heq : 𝕊.eqDen l = 𝕊.mkLam (𝕊.sortDen l) fun α => 𝕊.eqH α := rfl
  rw [hden, heq]
  have hv : ∀ α, α ∈ₛ 𝕊.El (𝕊.sortDen l) → 𝕊.ValidAny (𝕊.univList (sortLv l)) α :=
    fun α hα => (mem_sortDen hα).1
  obtain ⟨N₀, hN₀⟩ := isSemTy_sortDen (𝕊 := 𝕊) l
  have hfam : 𝕊.FamUnif (𝕊.sortDen l) fun α => 𝕊.relTy α := by
    intro m I a ha hu
    obtain ⟨k, hk⟩ := dp_bound_of_unif ha hu
    exact dp_bound_mkPi (D := a) (F := fun i _ => 𝕊.predTy (a i)) ⟨k, hk⟩
      ((dp_bound_mkPi (D := a) (F := fun _ _ => 𝕊.tProp) ⟨k, hk⟩
        ⟨0, fun _ _ _ _ _ => .small (.inl (.inr (.inr kind_tProp)))⟩).imp
        fun _ h i _ _ _ hl => h i hl)
  have hvalid : 𝕊.ValidAny (𝕊.univList (max N₀ (sortLv l)))
      (𝕊.mkPi (𝕊.sortDen l) fun α => 𝕊.relTy α) :=
    mkPi_valid (hN₀.mono (Nat.le_max_left ..))
      (fun α hα => (relTy_valid (hv α hα)).mono (Nat.le_max_right ..))
      (fun α α' hα h => relTy_tyRel (hv α hα) (hv α' (tyRel_of_rel_sortDen hα h).1)
        (tyRel_of_rel_sortDen hα h).2)
      (.inl fun _ _ hc => mkPi_full hc fun _ _ hc' => mkPi_full hc' fun _ _ hc'' =>
        (not_isCand_tProp hc'').elim) (fun _ => hfam)
  refine ⟨mkLam_mem_mkPi (n := sortLv l) (fun α hα => relTy_valid (hv α hα))
    (fun α hα => eqH_mem (hv α hα)) (fun α α' hα h => (tyRel_of_rel_sortDen hα h).1)
    (fun α α' hα h => ?_) (piUnif_of_flat _ hvalid fun _ _ =>
      flat_mkPi fun _ _ => flat_mkPi fun _ _ => flat_tProp), fun hcand => ?_⟩
  · obtain ⟨hα', hT⟩ := tyRel_of_rel_sortDen hα h
    exact eqH_rel (hv α hα) (hv α' hα') hT
  · -- the type is a data type: its fibre at the full candidate is one
    refine absurd hcand (not_isCand_mkPi (full_mem_sortDen l) ?_)
    have hs : 𝕊.star ∈ₛ 𝕊.El (𝕊.cand Candidate.full) := star_mem_cand ⟨.bot, trivial⟩
    refine not_isCand_mkPi hs (not_isCand_mkPi hs not_isCand_tProp)

end SetModel
end VEnv.Strengthening
end Lean4Lean
