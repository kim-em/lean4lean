import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.DenSubst
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.PiCongr
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.MinimalEnv

/-! # Soundness of the Klop model: statement

The semantic judgment `Sem` that every derivable judgment of an environment with the Klop
inventory is to satisfy (`FIRST_PRINCIPLES.md` §28, §29), with its first rule cases. The
head invariant on application spines is in `Spine.lean`, and the fundamental theorem is
assembled in `Fundamental.lean`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

namespace PVal

/-- Lift a simultaneous substitution under a binder. -/
def up (σ : Nat → PVal) : Nat → PVal
  | 0 => .var 0
  | i + 1 => (σ i).liftN 1

/-- Simultaneous substitution of values for variables. -/
def subst : PVal → (Nat → PVal) → PVal
  | .var i, σ => σ i
  | .lam b, σ => .lam (b.subst (up σ))
  | .app f a, σ => .app (f.subst σ) (a.subst σ)
  | .r, _ => .r
  | .bot, _ => .bot
  | .case s u v, σ => .case (s.subst σ) (u.subst σ) (v.subst σ)

end PVal

namespace UniverseTower
variable (𝕋 : UniverseTower)

/-- A semantic type of some level: a good candidate or a valid data type. -/
def IsSemTy (x : 𝕋.S) : Prop := ∃ n, 𝕋.ValidAny (𝕋.univList n) x

/-- A valuation of a context: the type of every variable denotes a semantic type, the
variable denotes an element of it, and its value realizes it when it is a proposition. -/
def ValOK (Γ : List VExpr) (ρ : Nat → 𝕋.S) (w : Nat → PVal) : Prop :=
  ∀ i A, Lookup Γ i A →
    𝕋.IsSemTy (𝕋.den ρ A) ∧
    𝕋.mem (ρ i) (𝕋.El (𝕋.den ρ A)) ∧
    (𝕋.IsCand (𝕋.den ρ A) → (𝕋.candOf (𝕋.den ρ A)).mem (w i))

/-- Two valuations of a context are coarsely related pointwise. -/
def CoRel (Γ : List VExpr) (ρ ρ' : Nat → 𝕋.S) : Prop :=
  ∀ i A, Lookup Γ i A →
    𝕋.TyRel (𝕋.den ρ A) (𝕋.den ρ' A) ∧ 𝕋.Rel (𝕋.den ρ A) (ρ i) (ρ' i)

/-- **The semantic judgment.** At every valuation of the context: the type denotes a
semantic type; the two sides have the same denotation, an element of it; if the type is a
proposition, the values of both sides realize it; and denotations at coarsely related
valuations are coarsely related. -/
def Sem (Γ : List VExpr) (a b A : VExpr) : Prop :=
  ∀ ρ w, 𝕋.ValOK Γ ρ w →
    𝕋.IsSemTy (𝕋.den ρ A) ∧
    𝕋.den ρ a = 𝕋.den ρ b ∧
    𝕋.mem (𝕋.den ρ a) (𝕋.El (𝕋.den ρ A)) ∧
    (𝕋.IsCand (𝕋.den ρ A) →
      (𝕋.candOf (𝕋.den ρ A)).mem ((pval a).subst w) ∧
      (𝕋.candOf (𝕋.den ρ A)).mem ((pval b).subst w)) ∧
    ∀ ρ' w', 𝕋.ValOK Γ ρ' w' → 𝕋.CoRel Γ ρ ρ' →
      𝕋.TyRel (𝕋.den ρ A) (𝕋.den ρ' A) ∧ 𝕋.Rel (𝕋.den ρ A) (𝕋.den ρ a) (𝕋.den ρ' a)

theorem valOK_nil (ρ : Nat → 𝕋.S) (w : Nat → PVal) : 𝕋.ValOK [] ρ w := by
  intro i A h
  cases h

variable {𝕋}

/-- The variable rule. -/
theorem sem_bvar {Γ : List VExpr} {i : Nat} {A : VExpr} (h : Lookup Γ i A) :
    𝕋.Sem Γ (.bvar i) (.bvar i) A := by
  intro ρ w hρ
  obtain ⟨hty, hmem, hval⟩ := hρ i A h
  exact ⟨hty, rfl, hmem, fun hc => ⟨hval hc, hval hc⟩, fun ρ' w' _ hrel => hrel i A h⟩

/-- Symmetry. -/
theorem Sem.symm {Γ : List VExpr} {a b A : VExpr} (H : 𝕋.Sem Γ a b A) : 𝕋.Sem Γ b a A := by
  intro ρ w hρ
  obtain ⟨hty, heq, hmem, hval, hrel⟩ := H ρ w hρ
  refine ⟨hty, heq.symm, heq ▸ hmem, fun hc => ⟨(hval hc).2, (hval hc).1⟩, fun ρ' w' hρ' hr => ?_⟩
  obtain ⟨-, heq', -⟩ := H ρ' w' hρ'
  obtain ⟨h1, h2⟩ := hrel ρ' w' hρ' hr
  exact ⟨h1, heq ▸ heq' ▸ h2⟩

/-- Transitivity. -/
theorem Sem.trans {Γ : List VExpr} {a b c A : VExpr} (H1 : 𝕋.Sem Γ a b A)
    (H2 : 𝕋.Sem Γ b c A) : 𝕋.Sem Γ a c A := by
  intro ρ w hρ
  obtain ⟨hty, heq, hmem, hval, hrel⟩ := H1 ρ w hρ
  obtain ⟨-, heq2, -, hval2, -⟩ := H2 ρ w hρ
  exact ⟨hty, heq.trans heq2, hmem, fun hc => ⟨(hval hc).1, (hval2 hc).2⟩, hrel⟩

/-- `𝒰ₙ` is a semantic type. -/
theorem isSemTy_univ (n : Nat) : 𝕋.IsSemTy (𝕋.univ n) :=
  ⟨n + 1, .univ (univ_mem_univList n)⟩

/-- The sort rule. -/
theorem sem_sort {Γ : List VExpr} {l l' : VLevel} (h : l ≈ l') :
    𝕋.Sem Γ (.sort l) (.sort l') (.sort (.succ l)) := by
  intro ρ w _
  have hm : 𝕋.mem (𝕋.sortDen l) (𝕋.El (𝕋.univ (l.eval []))) := sortDen_mem l
  refine ⟨isSemTy_univ _, sortDen_congr h, hm,
    fun hc => (not_isCand_univ _ hc).elim, fun ρ' w' _ _ => ⟨rfl, rel_univ_refl hm⟩⟩

/-- Conversion: the stated type may be replaced by a type with the same denotation. -/
theorem Sem.defeq {Γ : List VExpr} {a b A B S : VExpr} (HT : 𝕋.Sem Γ A B S)
    (H : 𝕋.Sem Γ a b A) : 𝕋.Sem Γ a b B := by
  intro ρ w hρ
  obtain ⟨-, hAB, -⟩ := HT ρ w hρ
  have h := H ρ w hρ
  rw [hAB] at h
  obtain ⟨hty, heq, hmem, hval, hrel⟩ := h
  refine ⟨hty, heq, hmem, hval, fun ρ' w' hρ' hr => ?_⟩
  obtain ⟨-, hAB', -⟩ := HT ρ' w' hρ'
  have := hrel ρ' w' hρ' hr
  rwa [hAB'] at this

/-! ### Elements of sorts -/

/-- The level at which the elements of `⟦Sort ℓ⟧` are valid. -/
def sortLv (l : VLevel) : Nat := l.eval [] - 1

/-- The elements of `⟦Sort ℓ⟧` are valid semantic types at level `sortLv ℓ`; they are all
propositions (`ℓ = 0`) or propositions among them are the full candidate. -/
theorem mem_sortDen {l : VLevel} {x : 𝕋.S} (hx : 𝕋.mem x (𝕋.El (𝕋.sortDen l))) :
    𝕋.ValidAny (𝕋.univList (sortLv l)) x ∧
    ((∀ y, 𝕋.mem y (𝕋.El (𝕋.sortDen l)) → 𝕋.IsCand y) ∨
      ∀ y, 𝕋.mem y (𝕋.El (𝕋.sortDen l)) → 𝕋.IsCand y → y = 𝕋.cand Candidate.full) := by
  unfold sortDen at hx ⊢
  unfold sortLv
  cases h : l.eval [] with
  | zero =>
    rw [h] at hx
    obtain ⟨c, hc, rfl⟩ := mem_El_tProp.1 hx
    exact ⟨.prop hc, .inl fun y hy => let ⟨d, _, e⟩ := mem_El_tProp.1 hy; ⟨d, e⟩⟩
  | succ m =>
    rw [h] at hx
    exact ⟨(mem_El_univ.1 hx).2.1, .inr fun y hy => (mem_El_univ.1 hy).2.2⟩

theorem isSemTy_of_mem_sortDen {l : VLevel} {x : 𝕋.S}
    (hx : 𝕋.mem x (𝕋.El (𝕋.sortDen l))) : 𝕋.IsSemTy x := ⟨_, (mem_sortDen hx).1⟩

/-- Coarsely related elements of a sort are coarsely related types. -/
theorem tyRel_of_rel_sortDen {l : VLevel} {x y : 𝕋.S}
    (hx : 𝕋.mem x (𝕋.El (𝕋.sortDen l))) (h : 𝕋.Rel (𝕋.sortDen l) x y) :
    𝕋.mem y (𝕋.El (𝕋.sortDen l)) ∧ 𝕋.TyRel x y := by
  unfold sortDen at hx h ⊢
  cases hl : l.eval [] with
  | zero => rw [hl] at hx h; exact (rel_tProp_iff hx).1 h
  | succ m => rw [hl] at hx h; exact (rel_univ_iff hx).1 h

/-! ### Extending a valuation -/

/-- Extend a value assignment. -/
def consV (u : PVal) (w : Nat → PVal) : Nat → PVal
  | 0 => u
  | i + 1 => w i

theorem valOK_cons {Γ : List VExpr} {ρ : Nat → 𝕋.S} {w : Nat → PVal} {A : VExpr} {d : 𝕋.S}
    {u : PVal} (hρ : 𝕋.ValOK Γ ρ w) (hA : 𝕋.IsSemTy (𝕋.den ρ A))
    (hd : 𝕋.mem d (𝕋.El (𝕋.den ρ A)))
    (hu : 𝕋.IsCand (𝕋.den ρ A) → (𝕋.candOf (𝕋.den ρ A)).mem u) :
    𝕋.ValOK (A :: Γ) (𝕋.cons d ρ) (consV u w) := by
  intro i B h
  cases h with
  | zero => rw [den_lift]; exact ⟨hA, hd, hu⟩
  | succ h => rw [den_lift]; exact hρ _ _ h

/-- Every element of a semantic type extends a valuation, with some value. -/
theorem exists_valOK_cons {Γ : List VExpr} {ρ : Nat → 𝕋.S} {w : Nat → PVal} {A : VExpr}
    {d : 𝕋.S} (hρ : 𝕋.ValOK Γ ρ w) (hA : 𝕋.IsSemTy (𝕋.den ρ A))
    (hd : 𝕋.mem d (𝕋.El (𝕋.den ρ A))) : ∃ u, 𝕋.ValOK (A :: Γ) (𝕋.cons d ρ) (consV u w) := by
  by_cases hc : 𝕋.IsCand (𝕋.den ρ A)
  · have hd' := hd
    rw [isCand_eq hc] at hd'
    obtain ⟨u, hu⟩ := (𝕋.mem_El_cand.1 hd').2
    exact ⟨u, valOK_cons hρ hA hd fun _ => hu⟩
  · exact ⟨.bot, valOK_cons hρ hA hd fun h => (hc h).elim⟩

/-! ### Application -/

/-- The application rule (`IsDefEqStrong.appDF`). -/
theorem Sem.app {Γ : List VExpr} {A B f f' a a' : VExpr} {u v : VLevel}
    (HA : 𝕋.Sem Γ A A (.sort u)) (HB : 𝕋.Sem (A :: Γ) B B (.sort v))
    (Hf : 𝕋.Sem Γ f f' (.forallE A B)) (Ha : 𝕋.Sem Γ a a' A)
    (HBa : 𝕋.Sem Γ (B.inst a) (B.inst a') (.sort v)) :
    𝕋.Sem Γ (.app f a) (.app f' a') (B.inst a) := by
  intro ρ w hρ
  obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
  have hAty : 𝕋.IsSemTy (𝕋.den ρ A) := isSemTy_of_mem_sortDen hAm
  obtain ⟨-, hff', hfm, hfv, hfr⟩ := Hf ρ w hρ
  obtain ⟨-, haa', ham, hav, har⟩ := Ha ρ w hρ
  obtain ⟨-, -, hBam, -, hBar⟩ := HBa ρ w hρ
  -- the fibres
  have hfib : ∀ d, 𝕋.mem d (𝕋.El (𝕋.den ρ A)) →
      𝕋.mem (𝕋.den (𝕋.cons d ρ) B) (𝕋.El (𝕋.sortDen v)) := fun d hd => by
    obtain ⟨u', hu'⟩ := exists_valOK_cons hρ hAty hd
    exact (HB _ _ hu').2.2.1
  have hinst : 𝕋.den ρ (B.inst a) = 𝕋.den (𝕋.cons (𝕋.den ρ a) ρ) B := 𝕋.den_inst0 ..
  have hfm' : 𝕋.mem (𝕋.den ρ f)
      (𝕋.El (𝕋.mkPi (𝕋.den ρ A) fun d => 𝕋.den (𝕋.cons d ρ) B)) := hfm
  refine ⟨isSemTy_of_mem_sortDen hBam, ?_, ?_, ?_, ?_⟩
  · show 𝕋.mkApp _ _ = 𝕋.mkApp _ _
    rw [hff', haa']
  · rw [hinst]; exact mkApp_mem hfm' ham
  · intro hc
    rw [hinst] at hc ⊢
    have hmix : (¬ ∀ d, 𝕋.mem d (𝕋.El (𝕋.den ρ A)) → 𝕋.IsCand (𝕋.den (𝕋.cons d ρ) B)) →
        ∀ d, 𝕋.mem d (𝕋.El (𝕋.den ρ A)) → 𝕋.IsCand (𝕋.den (𝕋.cons d ρ) B) →
          𝕋.den (𝕋.cons d ρ) B = 𝕋.cand Candidate.full := by
      intro hn d hd hdc
      rcases (mem_sortDen (hfib d hd)).2 with h | h
      · exact (hn fun d hd => h _ (hfib d hd)).elim
      · exact h _ (hfib d hd) hdc
    exact ⟨app_val_mem ham (fun h => (hfv h).1) (fun h => (hav h).1) hmix hc,
      app_val_mem ham (fun h => (hfv h).2) (fun h => (hav h).2) hmix hc⟩
  · intro ρ' w' hρ' hr
    obtain ⟨hty, hrel⟩ := hBar ρ' w' hρ' hr
    refine ⟨(tyRel_of_rel_sortDen hBam hrel).2, ?_⟩
    rw [hinst]
    exact mkApp_rel (n := sortLv v) (fun d hd => (mem_sortDen (hfib d hd)).1) hfm'
      (hfr ρ' w' hρ' hr).2 ham (har ρ' w' hρ' hr).2

/-! ### Function types -/

theorem isSemTy_sortDen (l : VLevel) : 𝕋.IsSemTy (𝕋.sortDen l) := by
  unfold sortDen
  cases l.eval [] with
  | zero => exact ⟨0, .tProp⟩
  | succ m => exact isSemTy_univ m

theorem not_isCand_sortDen (l : VLevel) : ¬ 𝕋.IsCand (𝕋.sortDen l) := by
  unfold sortDen
  cases l.eval [] with
  | zero => exact not_isCand_tProp
  | succ m => exact not_isCand_univ m

theorem rel_sortDen_of_tyRel {l : VLevel} {x y : 𝕋.S}
    (hx : 𝕋.mem x (𝕋.El (𝕋.sortDen l))) (hy : 𝕋.mem y (𝕋.El (𝕋.sortDen l)))
    (h : 𝕋.TyRel x y) : 𝕋.Rel (𝕋.sortDen l) x y := by
  unfold sortDen at hx hy ⊢
  cases hl : l.eval [] with
  | zero => rw [hl] at hx hy; exact (rel_tProp_iff hx).2 ⟨hy, h⟩
  | succ m => rw [hl] at hx hy; exact (rel_univ_iff hx).2 ⟨hy, h⟩

/-- Extending two coarsely related valuations by coarsely related elements. -/
theorem coRel_cons {Γ : List VExpr} {ρ ρ' : Nat → 𝕋.S} {A : VExpr} {d d' : 𝕋.S}
    (hr : 𝕋.CoRel Γ ρ ρ') (hT : 𝕋.TyRel (𝕋.den ρ A) (𝕋.den ρ' A))
    (hd : 𝕋.Rel (𝕋.den ρ A) d d') : 𝕋.CoRel (A :: Γ) (𝕋.cons d ρ) (𝕋.cons d' ρ') := by
  intro i B h
  cases h with
  | zero => rw [den_lift, den_lift]; exact ⟨hT, hd⟩
  | succ h => rw [den_lift, den_lift]; exact hr _ _ h

/-- A valuation is coarsely related to itself. -/
theorem coRel_refl {Γ : List VExpr} {ρ : Nat → 𝕋.S} {w : Nat → PVal} (hρ : 𝕋.ValOK Γ ρ w) :
    𝕋.CoRel Γ ρ ρ := by
  intro i A h
  obtain ⟨⟨n, hty⟩, hm, -⟩ := hρ i A h
  exact ⟨rfl, hty.isPER.refl _ hm⟩

/-- A Π over a type without elements is the full candidate. -/
theorem mkPi_of_empty {D : 𝕋.S} {F : 𝕋.S → 𝕋.S} (h : ¬ ∃ d, 𝕋.mem d (𝕋.El D)) :
    𝕋.mkPi D F = 𝕋.cand Candidate.full := by
  unfold mkPi
  by_cases hDc : 𝕋.IsCand D
  · rw [if_pos hDc, if_neg]
    intro hn
    exact h ⟨𝕋.star, by rw [isCand_eq hDc]; exact star_mem_cand hn⟩
  · rw [if_neg hDc, if_pos fun d hd => (h ⟨d, hd⟩).elim]
    congr 1
    exact Candidate.ext' fun v => ⟨fun _ => trivial, fun _ d hd => (h ⟨d, hd⟩).elim⟩

/-- The full candidate is an element of every sort. -/
theorem full_mem_sortDen (l : VLevel) :
    𝕋.mem (𝕋.cand Candidate.full) (𝕋.El (𝕋.sortDen l)) := by
  unfold sortDen
  cases l.eval [] with
  | zero => exact mem_El_tProp.2 ⟨_, Candidate.good_full, rfl⟩
  | succ m => exact (ValidAny.prop Candidate.good_full).mem_univ fun _ => rfl

/-- The membership part of the Π rule: a Π over a domain in `⟦Sort u⟧` with fibres in
`⟦Sort v⟧` that respect `~` is an element of `⟦Sort (imax u v)⟧`. -/
theorem mkPi_mem_sortDen {u v : VLevel} {D : 𝕋.S} {F : 𝕋.S → 𝕋.S}
    (hD : 𝕋.mem D (𝕋.El (𝕋.sortDen u)))
    (hF : ∀ d, 𝕋.mem d (𝕋.El D) → 𝕋.mem (F d) (𝕋.El (𝕋.sortDen v)))
    (hFrel : ∀ d d', 𝕋.mem d (𝕋.El D) → 𝕋.Rel D d d' → 𝕋.TyRel (F d) (F d')) :
    𝕋.mem (𝕋.mkPi D F) (𝕋.El (𝕋.sortDen (.imax u v))) := by
  let N := max (sortLv u) (sortLv v)
  have hDv : 𝕋.ValidAny (𝕋.univList N) D := (mem_sortDen hD).1.mono (Nat.le_max_left ..)
  have hFv : ∀ d, 𝕋.mem d (𝕋.El D) → 𝕋.ValidAny (𝕋.univList N) (F d) := fun d hd =>
    (mem_sortDen (hF d hd)).1.mono (Nat.le_max_right ..)
  by_cases hDe : ∃ d, 𝕋.mem d (𝕋.El D)
  case neg =>
    -- no element: the Π is the full candidate
    rw [mkPi_of_empty hDe]
    exact full_mem_sortDen _
  obtain ⟨d₀, hd₀⟩ := hDe
  have hsort : (∀ d, 𝕋.mem d (𝕋.El D) → 𝕋.IsCand (F d) → F d = 𝕋.cand Candidate.full) ∨
      ∀ d, 𝕋.mem d (𝕋.El D) → 𝕋.IsCand (F d) := by
    rcases (mem_sortDen (hF d₀ hd₀)).2 with h | h
    · exact .inr fun d hd => h _ (hF d hd)
    · exact .inl fun d hd => h _ (hF d hd)
  have hval := mkPi_valid hDv hFv hFrel hsort
  unfold sortDen
  have himax : (VLevel.imax u v).eval [] = Lean.Nat.imax (u.eval []) (v.eval []) := rfl
  rw [himax]
  cases hv : v.eval [] with
  | zero =>
    have hall : ∀ d, 𝕋.mem d (𝕋.El D) → 𝕋.IsCand (F d) := fun d hd => by
      have := hF d hd
      unfold sortDen at this
      rw [hv] at this
      obtain ⟨c, -, e⟩ := mem_El_tProp.1 this
      exact ⟨c, e⟩
    have hc := mkPi_isCand hall
    simp only [Lean.Nat.imax]
    rw [isCand_eq hc] at hval ⊢
    exact mem_El_tProp.2 ⟨_, hval.good, rfl⟩
  | succ k =>
    have hmax : Lean.Nat.imax (u.eval []) (k + 1) = max (u.eval []) (k + 1) - 1 + 1 := by
      simp only [Lean.Nat.imax, Nat.succ_ne_zero, if_false]
      show Nat.max (u.eval []) (k + 1) = _
      have : Nat.max (u.eval []) (k + 1) = max (u.eval []) (k + 1) := rfl
      omega
    rw [hmax]
    have hle : N ≤ max (u.eval []) (k + 1) - 1 := by
      show max (sortLv u) (sortLv v) ≤ _
      unfold sortLv; rw [hv]; omega
    refine (hval.mono hle).mem_univ fun hc => mkPi_full hc fun d hd hdc => ?_
    have := hF d hd
    unfold sortDen at this
    rw [hv] at this
    exact (mem_El_univ.1 this).2.2 hdc

/-- The fibres of a binder, from the semantic judgment of its body: they are elements of the
sort, agree on both sides, and respect the coarse relation. -/
theorem Sem.fibres {Γ : List VExpr} {A B B' : VExpr} {v : VLevel}
    (HB : 𝕋.Sem (A :: Γ) B B' (.sort v)) {ρ : Nat → 𝕋.S} {w : Nat → PVal}
    (hρ : 𝕋.ValOK Γ ρ w) (hAty : 𝕋.IsSemTy (𝕋.den ρ A)) :
    (∀ d, 𝕋.mem d (𝕋.El (𝕋.den ρ A)) →
      𝕋.mem (𝕋.den (𝕋.cons d ρ) B) (𝕋.El (𝕋.sortDen v)) ∧
      𝕋.den (𝕋.cons d ρ) B = 𝕋.den (𝕋.cons d ρ) B') ∧
    ∀ d d', 𝕋.mem d (𝕋.El (𝕋.den ρ A)) → 𝕋.Rel (𝕋.den ρ A) d d' →
      𝕋.TyRel (𝕋.den (𝕋.cons d ρ) B) (𝕋.den (𝕋.cons d' ρ) B) := by
  obtain ⟨n, hAv⟩ := hAty
  refine ⟨fun d hd => ?_, fun d d' hd hdd' => ?_⟩
  · obtain ⟨u', hu'⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hd
    obtain ⟨-, heq, hm, -⟩ := HB _ _ hu'
    exact ⟨hm, heq⟩
  · have hd' := hAv.isPER.mem _ _ hd hdd'
    obtain ⟨u₁, h₁⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hd
    obtain ⟨u₂, h₂⟩ := exists_valOK_cons hρ ⟨n, hAv⟩ hd'
    obtain ⟨-, -, hm, -, hrel⟩ := HB _ _ h₁
    have := (hrel _ _ h₂ (coRel_cons (coRel_refl hρ) rfl hdd')).2
    exact (tyRel_of_rel_sortDen hm this).2

/-- The Π rule (`IsDefEqStrong.forallEDF`). -/
theorem Sem.forallE {Γ : List VExpr} {A A' B B' : VExpr} {u v : VLevel}
    (HA : 𝕋.Sem Γ A A' (.sort u)) (HB : 𝕋.Sem (A :: Γ) B B' (.sort v)) :
    𝕋.Sem Γ (.forallE A B) (.forallE A' B') (.sort (.imax u v)) := by
  have key : ∀ ρ w, 𝕋.ValOK Γ ρ w →
      𝕋.mem (𝕋.den ρ (.forallE A B)) (𝕋.El (𝕋.sortDen (.imax u v))) := by
    intro ρ w hρ
    obtain ⟨-, -, hAm, -, -⟩ := HA ρ w hρ
    obtain ⟨hfib, hrel⟩ := HB.fibres hρ (isSemTy_of_mem_sortDen hAm)
    exact mkPi_mem_sortDen hAm (fun d hd => (hfib d hd).1) hrel
  intro ρ w hρ
  obtain ⟨-, hAA', hAm, -, hAr⟩ := HA ρ w hρ
  have hAty : 𝕋.IsSemTy (𝕋.den ρ A) := isSemTy_of_mem_sortDen hAm
  obtain ⟨hfib, hrel⟩ := HB.fibres hρ hAty
  refine ⟨isSemTy_sortDen _, ?_, key ρ w hρ, fun hc => (not_isCand_sortDen _ hc).elim, ?_⟩
  · show 𝕋.mkPi _ _ = 𝕋.mkPi _ _
    rw [← hAA']
    exact mkPi_congr fun d hd => (hfib d hd).2
  · intro ρ' w' hρ' hr
    refine ⟨rfl, rel_sortDen_of_tyRel (key ρ w hρ) (key ρ' w' hρ') ?_⟩
    obtain ⟨-, -, hAm', -, -⟩ := HA ρ' w' hρ'
    have hAty' : 𝕋.IsSemTy (𝕋.den ρ' A) := isSemTy_of_mem_sortDen hAm'
    obtain ⟨hfib', -⟩ := HB.fibres hρ' hAty'
    have hTA : 𝕋.TyRel (𝕋.den ρ A) (𝕋.den ρ' A) :=
      (tyRel_of_rel_sortDen hAm (hAr ρ' w' hρ' hr).2).2
    let N := max (sortLv u) (sortLv v)
    have hDv : 𝕋.ValidAny (𝕋.univList N) (𝕋.den ρ A) :=
      (mem_sortDen hAm).1.mono (Nat.le_max_left ..)
    have hDv' : 𝕋.ValidAny (𝕋.univList N) (𝕋.den ρ' A) :=
      (mem_sortDen hAm').1.mono (Nat.le_max_left ..)
    have hsame := hDv.tyRel_same hDv' hTA
    refine mkPi_tyRel hDv hDv' hTA
      (fun d hd => (mem_sortDen (hfib d hd).1).1.mono (Nat.le_max_right ..))
      (fun d hd => (mem_sortDen (hfib' d hd).1).1.mono (Nat.le_max_right ..)) fun d hd => ?_
    have hd' : 𝕋.mem d (𝕋.El (𝕋.den ρ' A)) := hsame.1 ▸ hd
    obtain ⟨u₁, h₁⟩ := exists_valOK_cons hρ hAty hd
    obtain ⟨u₂, h₂⟩ := exists_valOK_cons hρ' hAty' hd'
    obtain ⟨-, -, hm, -, hrelB⟩ := HB _ _ h₁
    have := (hrelB _ _ h₂ (coRel_cons hr hTA (hDv.isPER.refl _ hd))).2
    exact (tyRel_of_rel_sortDen hm this).2

end UniverseTower

end VEnv.Strengthening
end Lean4Lean
