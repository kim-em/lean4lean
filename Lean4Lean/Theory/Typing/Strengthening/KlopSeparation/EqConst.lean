import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.EqConsts

/-! # Soundness: the constant `Eq`

`⟦Eq.{l}⟧` is an element of `⟦∀ α : Sort l, α → α → Prop⟧`: the candidate `eqCand α a b` is
inhabited exactly when `a` and `b` are coarsely related, and this is stable under coarse
relatedness of `b`, of `a` and of `α`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace UniverseTower
variable {𝕋 : UniverseTower}

local infix:50 " ∈ₛ " => 𝕋.mem

theorem good_eqCand (α a b : 𝕋.S) : (𝕋.eqCand α a b).Good := by
  unfold eqCand
  split
  · exact Candidate.good_rOrBot
  · split
    · exact Candidate.good_botOnly
    · exact Candidate.good_empty

/-- An equation is inhabited exactly when its endpoints are coarsely related. -/
theorem eqCand_nonempty_iff {α a b : 𝕋.S} (hα : 𝕋.IsPER α) :
    (∃ v, (𝕋.eqCand α a b).mem v) ↔ a ∈ₛ 𝕋.El α ∧ 𝕋.Rel α a b := by
  unfold eqCand
  by_cases h1 : a ∈ₛ 𝕋.El α ∧ a = b
  · rw [if_pos h1]
    obtain ⟨ha, rfl⟩ := h1
    exact ⟨fun _ => ⟨ha, hα.refl _ ha⟩, fun _ => ⟨.r, .inl .rfl⟩⟩
  · rw [if_neg h1]
    by_cases h2 : a ∈ₛ 𝕋.El α ∧ 𝕋.Rel α a b
    · rw [if_pos h2]; exact ⟨fun _ => h2, fun _ => ⟨.bot, .rfl⟩⟩
    · rw [if_neg h2]; exact ⟨fun ⟨_, h⟩ => h.elim, fun h => (h2 h).elim⟩

theorem cand_mem_tProp {c : Candidate} (hc : c.Good) : 𝕋.cand c ∈ₛ 𝕋.El 𝕋.tProp :=
  mem_El_tProp.2 ⟨c, hc, rfl⟩

/-- Two equations with equivalent inhabitation are coarsely related propositions. -/
theorem rel_tProp_eqCand {α a b α' a' b' : 𝕋.S}
    (h : (∃ v, (𝕋.eqCand α a b).mem v) ↔ ∃ v, (𝕋.eqCand α' a' b').mem v) :
    𝕋.Rel 𝕋.tProp (𝕋.cand (𝕋.eqCand α a b)) (𝕋.cand (𝕋.eqCand α' a' b')) :=
  (rel_tProp_iff (cand_mem_tProp (good_eqCand ..))).2
    ⟨cand_mem_tProp (good_eqCand ..), tyRel_cand.2 h⟩

/-- A Π with an element of the domain whose fibre is a data type is a data type. -/
theorem not_isCand_mkPi {D d : 𝕋.S} {F : 𝕋.S → 𝕋.S} (hd : d ∈ₛ 𝕋.El D)
    (hF : ¬ 𝕋.IsCand (F d)) : ¬ 𝕋.IsCand (𝕋.mkPi D F) := by
  intro hc
  unfold mkPi at hc
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc] at hc
    have hDeq := isCand_eq hDc
    have hds : d = 𝕋.star := by rw [hDeq] at hd; exact (𝕋.mem_El_cand.1 hd).1
    have hne : ∃ v, (𝕋.candOf D).mem v := by rw [hDeq] at hd; exact (𝕋.mem_El_cand.1 hd).2
    subst hds
    rw [if_pos hne, if_neg hF] at hc
    exact absurd hc (not_isCand_of_kind (kind_tPiP ..) (by decide))
  · rw [if_neg hDc] at hc
    by_cases hall : ∀ d, d ∈ₛ 𝕋.El D → 𝕋.IsCand (F d)
    · exact hF (hall d hd)
    · rw [if_neg hall] at hc
      exact absurd hc (not_isCand_of_kind (kind_tPi ..) (by decide))

/-- `α → Prop` as a semantic type. -/
noncomputable def predTy (𝕋 : UniverseTower) (α : 𝕋.S) : 𝕋.S := 𝕋.mkPi α fun _ => 𝕋.tProp

/-- `α → α → Prop` as a semantic type. -/
noncomputable def relTy (𝕋 : UniverseTower) (α : 𝕋.S) : 𝕋.S := 𝕋.mkPi α fun _ => 𝕋.predTy α

theorem predTy_valid {n : Nat} {α : 𝕋.S} (hα : 𝕋.ValidAny (𝕋.univList n) α) :
    𝕋.ValidAny (𝕋.univList n) (𝕋.predTy α) :=
  mkPi_valid hα (fun _ _ => .tProp) (fun _ _ _ _ => rfl)
    (.inl fun _ _ hc => (not_isCand_tProp hc).elim)

theorem relTy_valid {n : Nat} {α : 𝕋.S} (hα : 𝕋.ValidAny (𝕋.univList n) α) :
    𝕋.ValidAny (𝕋.univList n) (𝕋.relTy α) :=
  mkPi_valid hα (fun _ _ => predTy_valid hα) (fun _ _ _ _ => rfl)
    (.inl fun _ _ hc => mkPi_full hc fun _ _ hc' => (not_isCand_tProp hc').elim)

theorem predTy_tyRel {n : Nat} {α α' : 𝕋.S} (hα : 𝕋.ValidAny (𝕋.univList n) α)
    (hα' : 𝕋.ValidAny (𝕋.univList n) α') (h : 𝕋.TyRel α α') :
    𝕋.TyRel (𝕋.predTy α) (𝕋.predTy α') :=
  mkPi_tyRel hα hα' h (fun _ _ => .tProp) (fun _ _ => .tProp) fun _ _ => rfl

theorem relTy_tyRel {n : Nat} {α α' : 𝕋.S} (hα : 𝕋.ValidAny (𝕋.univList n) α)
    (hα' : 𝕋.ValidAny (𝕋.univList n) α') (h : 𝕋.TyRel α α') :
    𝕋.TyRel (𝕋.relTy α) (𝕋.relTy α') :=
  mkPi_tyRel hα hα' h (fun _ _ => predTy_valid hα) (fun _ _ => predTy_valid hα')
    fun _ _ => predTy_tyRel hα hα' h

/-- `fun b => a = b`. -/
noncomputable def eqG (𝕋 : UniverseTower) (α a : 𝕋.S) : 𝕋.S :=
  𝕋.mkLam α fun b => 𝕋.cand (𝕋.eqCand α a b)

/-- `fun a b => a = b`. -/
noncomputable def eqH (𝕋 : UniverseTower) (α : 𝕋.S) : 𝕋.S := 𝕋.mkLam α fun a => 𝕋.eqG α a

theorem eqG_mem {n : Nat} {α a : 𝕋.S} (hα : 𝕋.ValidAny (𝕋.univList n) α) (ha : a ∈ₛ 𝕋.El α) :
    𝕋.eqG α a ∈ₛ 𝕋.El (𝕋.predTy α) := by
  have per := hα.isPER
  refine mkLam_mem_mkPi (n := n) (fun _ _ => .tProp)
    (fun b _ => cand_mem_tProp (good_eqCand ..)) (fun b b' hb h => per.mem _ _ hb h)
    (fun b b' hb h => rel_tProp_eqCand ?_)
  rw [eqCand_nonempty_iff per, eqCand_nonempty_iff per]
  exact and_congr_right fun _ =>
    ⟨fun h1 => per.trans _ _ _ ha h1 h, fun h1 =>
      per.trans _ _ _ ha h1 (per.symm _ _ hb h)⟩

/-- Coarsely related left endpoints, and coarsely related types, give coarsely related
predicates. -/
theorem eqG_rel {n : Nat} {α α' a a' : 𝕋.S} (hα : 𝕋.ValidAny (𝕋.univList n) α)
    (hα' : 𝕋.ValidAny (𝕋.univList n) α') (hT : 𝕋.TyRel α α') (ha : a ∈ₛ 𝕋.El α)
    (haa' : 𝕋.Rel α a a') : 𝕋.Rel (𝕋.predTy α) (𝕋.eqG α a) (𝕋.eqG α' a') := by
  have per := hα.isPER
  have per' := hα'.isPER
  have same := hα.tyRel_same hα' hT
  have ha' : a' ∈ₛ 𝕋.El α := per.mem _ _ ha haa'
  have hmem' : 𝕋.eqG α' a' ∈ₛ 𝕋.El (𝕋.predTy α) := by
    rw [((predTy_valid hα).tyRel_same (predTy_valid hα') (predTy_tyRel hα hα' hT)).1]
    exact eqG_mem hα' (same.1 ▸ ha')
  refine rel_mkPi_of_pointwise (eqG_mem hα ha) hmem' fun b hb => ?_
  rw [eqG, eqG, 𝕋.mkApp_mkLam hb, 𝕋.mkApp_mkLam (same.1 ▸ hb)]
  refine rel_tProp_eqCand ?_
  rw [eqCand_nonempty_iff per, eqCand_nonempty_iff per', ← same.1, ← same.2 a' b ha']
  exact ⟨fun ⟨_, h⟩ => ⟨ha', per.trans _ _ _ ha' (per.symm _ _ ha haa') h⟩,
    fun ⟨_, h⟩ => ⟨ha, per.trans _ _ _ ha haa' h⟩⟩

theorem eqH_mem {n : Nat} {α : 𝕋.S} (hα : 𝕋.ValidAny (𝕋.univList n) α) :
    𝕋.eqH α ∈ₛ 𝕋.El (𝕋.relTy α) :=
  mkLam_mem_mkPi (n := n) (fun _ _ => predTy_valid hα) (fun a ha => eqG_mem hα ha)
    (fun a a' ha h => hα.isPER.mem _ _ ha h) (fun a a' ha h => eqG_rel hα hα rfl ha h)

theorem eqH_rel {n : Nat} {α α' : 𝕋.S} (hα : 𝕋.ValidAny (𝕋.univList n) α)
    (hα' : 𝕋.ValidAny (𝕋.univList n) α') (hT : 𝕋.TyRel α α') :
    𝕋.Rel (𝕋.relTy α) (𝕋.eqH α) (𝕋.eqH α') := by
  have same := hα.tyRel_same hα' hT
  have hmem' : 𝕋.eqH α' ∈ₛ 𝕋.El (𝕋.relTy α) := by
    rw [((relTy_valid hα).tyRel_same (relTy_valid hα') (relTy_tyRel hα hα' hT)).1]
    exact eqH_mem hα'
  refine rel_mkPi_of_pointwise (eqH_mem hα) hmem' fun a ha => ?_
  rw [eqH, eqH, 𝕋.mkApp_mkLam ha, 𝕋.mkApp_mkLam (same.1 ▸ ha)]
  exact eqG_rel hα hα' hT ha (hα.isPER.refl _ ha)

/-- `Eq.{l} : ∀ α : Sort l, α → α → Prop`. -/
theorem constOK_Eq (ls : List VLevel) : 𝕋.ConstOK ``Eq ls (canonicalEqType.instL ls) := by
  have hty : canonicalEqType.instL ls =
      .forallE (.sort ((VLevel.param 0).inst ls)) (.forallE (.bvar 0)
        (.forallE (.bvar 1) (.sort .zero))) := by
    simp [canonicalEqType, VExpr.instL, VLevel.inst]
  have hc : 𝕋.constDen ``Eq ls = 𝕋.eqDen (ls.getD 0 .zero) := by simp [constDen]
  have hl : (VLevel.param 0).inst ls = ls.getD 0 .zero := rfl
  rw [hty, hl]
  intro ρ
  rw [hc]
  generalize ls.getD 0 .zero = l
  have hden : 𝕋.den ρ (.forallE (.sort l) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))
      = 𝕋.mkPi (𝕋.sortDen l) fun α => 𝕋.relTy α := rfl
  have heq : 𝕋.eqDen l = 𝕋.mkLam (𝕋.sortDen l) fun α => 𝕋.eqH α := rfl
  rw [hden, heq]
  have hv : ∀ α, α ∈ₛ 𝕋.El (𝕋.sortDen l) → 𝕋.ValidAny (𝕋.univList (sortLv l)) α :=
    fun α hα => (mem_sortDen hα).1
  refine ⟨mkLam_mem_mkPi (n := sortLv l) (fun α hα => relTy_valid (hv α hα))
    (fun α hα => eqH_mem (hv α hα)) (fun α α' hα h => (tyRel_of_rel_sortDen hα h).1)
    (fun α α' hα h => ?_), fun hcand => ?_⟩
  · obtain ⟨hα', hT⟩ := tyRel_of_rel_sortDen hα h
    exact eqH_rel (hv α hα) (hv α' hα') hT
  · -- the type is a data type: its fibre at the full candidate is one
    refine absurd hcand (not_isCand_mkPi (full_mem_sortDen l) ?_)
    have hs : 𝕋.star ∈ₛ 𝕋.El (𝕋.cand Candidate.full) := star_mem_cand ⟨.bot, trivial⟩
    refine not_isCand_mkPi hs (not_isCand_mkPi hs not_isCand_tProp)

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
