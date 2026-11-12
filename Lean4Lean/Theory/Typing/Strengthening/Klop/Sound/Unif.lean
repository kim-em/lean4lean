import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.Judgment

/-! # Soundness: the uniformity clause, rule by rule

The rules for `SemU`, the clause of the semantic judgment that bounds the depth of families
of types: variable, sort, conversion, Π formation, abstraction and application. The equality
rules need no case of their own, because both sides of a derivable equation have the same
denotation (`SemU.of_sem`).

`SemDU` is the same clause for a semantic term, a function of the valuation, so that the
abstraction rule also serves the denotation of `Eq.rec`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

namespace SetModel
variable {𝕊 : SetModel}

local infix:50 " ∈ₛ " => 𝕊.mem

/-- The uniformity clause for a semantic term. -/
def SemDU (𝕊 : SetModel) (Γ : List VExpr) (d : (Nat → 𝕊.S) → 𝕊.S) (A : VExpr) : Prop :=
  ∀ (n : Nat) (I : World) (ρ : I → Nat → 𝕊.S) (w : I → Nat → PVal),
    (∀ i, 𝕊.ValOK Γ (ρ i) (w i)) → 𝕊.CtxUnif n Γ ρ →
    𝕊.Unif n I (fun i => 𝕊.den (ρ i) A) (fun i => d (ρ i))

theorem CtxUnif.comp {Γ : List VExpr} {n n' : Nat} (hn : n ≤ n') {I J : World}
    {ρ : I → Nat → 𝕊.S} (h : 𝕊.CtxUnif n Γ ρ) (ψ : J → I) :
    𝕊.CtxUnif n' Γ (fun j => ρ (ψ j)) := fun j A hl => ((h j A hl).mono hn).comp ψ

/-- The variable rule. -/
theorem semU_bvar {Γ : List VExpr} {i : Nat} {A : VExpr} (h : Lookup Γ i A) :
    𝕊.SemU Γ (.bvar i) A := fun _ _ _ _ _ hctx => hctx i A h

/-- The sort rule. -/
theorem semU_sort {Γ : List VExpr} (l : VLevel) : 𝕊.SemU Γ (.sort l) (.sort (.succ l)) := by
  intro n I ρ w _ _
  obtain ⟨k, hv⟩ := isSemTy_sortDen (𝕊 := 𝕊) (.succ l)
  exact (hv.unif_const I (sortDen_mem l)).mono (Nat.zero_le n)

/-- Both sides of a semantic equation satisfy the clause if one does. -/
theorem SemDU.of_den_eq {Γ : List VExpr} {d d' : (Nat → 𝕊.S) → 𝕊.S} {A : VExpr}
    (H : 𝕊.SemDU Γ d A) (h : ∀ ρ w, 𝕊.ValOK Γ ρ w → d ρ = d' ρ) : 𝕊.SemDU Γ d' A := by
  intro n I ρ w hρ hctx
  have e : (fun i => d' (ρ i)) = fun i => d (ρ i) := funext fun i => (h _ _ (hρ i)).symm
  rw [e]; exact H n I ρ w hρ hctx

theorem SemU.of_sem {Γ : List VExpr} {a b A : VExpr} (H : 𝕊.SemU Γ a A) (h : 𝕊.Sem Γ a b A) :
    𝕊.SemU Γ b A :=
  SemDU.of_den_eq (d := fun ρ => 𝕊.den ρ a) H fun ρ w hρ => (h ρ w hρ).2.1

theorem SemU.of_sem' {Γ : List VExpr} {a b A : VExpr} (H : 𝕊.SemU Γ b A) (h : 𝕊.Sem Γ a b A) :
    𝕊.SemU Γ a A :=
  SemDU.of_den_eq (d := fun ρ => 𝕊.den ρ b) H fun ρ w hρ => (h ρ w hρ).2.1.symm

/-- Conversion. -/
theorem SemDU.defeq {Γ : List VExpr} {d : (Nat → 𝕊.S) → 𝕊.S} {A B S : VExpr}
    (HT : 𝕊.Sem Γ A B S) (H : 𝕊.SemDU Γ d A) : 𝕊.SemDU Γ d B := by
  intro n I ρ w hρ hctx
  have e : (fun i => 𝕊.den (ρ i) B) = fun i => 𝕊.den (ρ i) A :=
    funext fun i => (HT _ _ (hρ i)).2.1.symm
  rw [e]; exact H n I ρ w hρ hctx

theorem SemU.defeq {Γ : List VExpr} {a A B S : VExpr} (HT : 𝕊.Sem Γ A B S)
    (H : 𝕊.SemU Γ a A) : 𝕊.SemU Γ a B :=
  SemDU.defeq (d := fun ρ => 𝕊.den ρ a) HT H

/-- A term whose type is a proposition, `T` or `Prop` at every valuation satisfies the
clause. -/
theorem semDU_of_base {Γ : List VExpr} {d : (Nat → 𝕊.S) → 𝕊.S} {A : VExpr}
    (h : ∀ ρ w, 𝕊.ValOK Γ ρ w → 𝕊.IsBase (𝕊.den ρ A)) : 𝕊.SemDU Γ d A :=
  fun _ _ _ _ hρ _ => unif_of_small (fun i => .inl (h _ _ (hρ i))) _

/-- A term of type `Prop` satisfies the clause: its values are propositions. -/
theorem semU_prop {Γ : List VExpr} (a : VExpr) : 𝕊.SemU Γ a (.sort .zero) :=
  semDU_of_base (d := fun ρ => 𝕊.den ρ a) fun _ _ _ =>
    show 𝕊.IsBase 𝕊.tProp from .inr (.inr kind_tProp)

theorem sortDen_leaf (l : VLevel) : 𝕊.IsBase (𝕊.sortDen l) ∨ 𝕊.kind (𝕊.sortDen l) = 𝕊.tagN 3 := by
  rcases sortDen_cases (𝕊 := 𝕊) l with e | ⟨j, e⟩
  · rw [e]; exact .inl (.inr (.inr kind_tProp))
  · rw [e]; exact .inr (kind_tU ..)

/-- The Π rule. -/
theorem SemU.forallE {Γ : List VExpr} {A B : VExpr} {u v : VLevel}
    (HA : 𝕊.Sem Γ A A (.sort u)) (HB : 𝕊.Sem (A :: Γ) B B (.sort v))
    (HAU : 𝕊.SemU Γ A (.sort u)) (HBU : 𝕊.SemU (A :: Γ) B (.sort v)) :
    𝕊.SemU Γ (.forallE A B) (.sort (.imax u v)) := by
  intro n I ρ w hρ hctx m' hm
  have hDm : ∀ i, 𝕊.mem (𝕊.den (ρ i) A) (𝕊.El (𝕊.sortDen u)) := fun i =>
    (HA _ _ (hρ i)).2.2.1
  have hfib : ∀ i d, 𝕊.mem d (𝕊.El (𝕊.den (ρ i) A)) →
      𝕊.mem (𝕊.den (𝕊.cons d (ρ i)) B) (𝕊.El (𝕊.sortDen v)) := fun i d hd =>
    ((HB.fibres (hρ i) (isSemTy_of_mem_sortDen (hDm i))).1 d hd).1
  obtain ⟨kD, hkD⟩ := dp_bound_of_unif hDm ((HAU n I ρ w hρ hctx).mono hm)
  -- the world of all elements of the domains of level `m'`
  let J : World := {p : I × 𝕊.S // 𝕊.LvLe m' (𝕊.den (ρ p.1) A) ∧ 𝕊.mem p.2 (𝕊.El (𝕊.den (ρ p.1) A))}
  have hex := fun j : J => exists_valOK_cons (hρ j.1.1) (isSemTy_of_mem_sortDen (hDm j.1.1)) j.2.2
  have hnew : 𝕊.Unif m' J (fun j => 𝕊.den (ρ j.1.1) A) (fun j => j.1.2) :=
    unif_full (k := kD) fun j => ⟨⟨_, (mem_sortDen (hDm j.1.1)).1⟩, j.2.1, hkD _ j.2.1, j.2.2⟩
  have hctxJ : 𝕊.CtxUnif m' (A :: Γ) (fun j : J => 𝕊.cons j.1.2 (ρ j.1.1)) :=
    ctxUnif_cons (hctx.comp hm fun j : J => j.1.1) hnew
  obtain ⟨kF, hkF⟩ := dp_bound_of_unif (fun j : J => hfib _ _ j.2.2)
    (HBU m' J _ (fun j => consV (hex j).choose (w j.1.1)) (fun j => (hex j).choose_spec) hctxJ)
  obtain ⟨k, hk⟩ := dp_bound_mkPi (D := fun i => 𝕊.den (ρ i) A)
    (F := fun i d => 𝕊.den (𝕊.cons d (ρ i)) B) ⟨kD, hkD⟩
    ⟨kF, fun i d hl hd => hkF ⟨(i, d), hl, hd⟩⟩
  obtain ⟨N, hN⟩ := isSemTy_sortDen (𝕊 := 𝕊) (.imax u v)
  exact ⟨_, Lf_leaf (fun _ => sortDen_leaf _) (fun _ => hN.lvLe) ⟨k, fun i _ _ hl => hk i hl⟩⟩

/-- The abstraction rule, for a semantic body. -/
theorem SemDU.lam {Γ : List VExpr} {A B : VExpr} {u v : VLevel} {d : (Nat → 𝕊.S) → 𝕊.S}
    (HA : 𝕊.Sem Γ A A (.sort u)) (HB : 𝕊.Sem (A :: Γ) B B (.sort v))
    (hd : ∀ ρ w, 𝕊.ValOK (A :: Γ) ρ w → 𝕊.mem (d ρ) (𝕊.El (𝕊.den ρ B)))
    (HAU : 𝕊.SemU Γ A (.sort u)) (HBU : 𝕊.SemU (A :: Γ) B (.sort v))
    (HdU : 𝕊.SemDU (A :: Γ) d B) :
    𝕊.SemDU Γ (fun ρ => 𝕊.mkLam (𝕊.den ρ A) fun x => d (𝕊.cons x ρ)) (.forallE A B) := by
  intro n I ρ w hρ hctx
  have hDm : ∀ i, 𝕊.mem (𝕊.den (ρ i) A) (𝕊.El (𝕊.sortDen u)) := fun i =>
    (HA _ _ (hρ i)).2.2.1
  have hAty := fun i => isSemTy_of_mem_sortDen (hDm i)
  have hfib : ∀ i x, 𝕊.mem x (𝕊.El (𝕊.den (ρ i) A)) →
      𝕊.mem (𝕊.den (𝕊.cons x (ρ i)) B) (𝕊.El (𝕊.sortDen v)) := fun i x hx =>
    ((HB.fibres (hρ i) (hAty i)).1 x hx).1
  have HPi := Sem.forallE HA HB HBU
  refine unif_mkLam (D := fun i => 𝕊.den (ρ i) A) (F := fun i x => 𝕊.den (𝕊.cons x (ρ i)) B)
    (f := fun i x => d (𝕊.cons x (ρ i)))
    (fun i x hx => ⟨_, (mem_sortDen (hfib i x hx)).1⟩) (fun i x hx => ?_) ?_ ?_
  · obtain ⟨u', hu'⟩ := exists_valOK_cons (hρ i) (hAty i) hx
    exact hd _ _ hu'
  · exact tame_of_unif_sort (v := .imax u v) (fun i => (HPi _ _ (hρ i)).2.2.1)
      (SemU.forallE HA HB HAU HBU n I ρ w hρ hctx)
  · intro m' hm I' φ a ha hu _
    have hex := fun i' => exists_valOK_cons (hρ (φ i')) (hAty (φ i')) (ha i')
    exact HdU m' I' (fun i' => 𝕊.cons (a i') (ρ (φ i')))
      (fun i' => consV (hex i').choose (w (φ i'))) (fun i' => (hex i').choose_spec)
      (ctxUnif_cons (hctx.comp hm φ) hu) m' (Nat.le_refl m')

/-- The abstraction rule. -/
theorem SemU.lam {Γ : List VExpr} {A B b : VExpr} {u v : VLevel}
    (HA : 𝕊.Sem Γ A A (.sort u)) (HB : 𝕊.Sem (A :: Γ) B B (.sort v))
    (Hb : 𝕊.Sem (A :: Γ) b b B)
    (HAU : 𝕊.SemU Γ A (.sort u)) (HBU : 𝕊.SemU (A :: Γ) B (.sort v))
    (HbU : 𝕊.SemU (A :: Γ) b B) : 𝕊.SemU Γ (.lam A b) (.forallE A B) :=
  SemDU.lam HA HB (fun ρ w hρ => (Hb ρ w hρ).2.2.1) HAU HBU HbU

/-- The application rule. -/
theorem SemU.app {Γ : List VExpr} {A B f a : VExpr} {v : VLevel}
    (Hf : 𝕊.Sem Γ f f (.forallE A B)) (Ha : 𝕊.Sem Γ a a A)
    (HBa : 𝕊.Sem Γ (B.inst a) (B.inst a) (.sort v))
    (HfU : 𝕊.SemU Γ f (.forallE A B)) (HaU : 𝕊.SemU Γ a A)
    (HBaU : 𝕊.SemU Γ (B.inst a) (.sort v)) : 𝕊.SemU Γ (.app f a) (B.inst a) := by
  intro n I ρ w hρ hctx
  have e : (fun i => 𝕊.den (ρ i) (B.inst a)) =
      fun i => 𝕊.den (𝕊.cons (𝕊.den (ρ i) a) (ρ i)) B := funext fun i => 𝕊.den_inst0 ..
  have hT : 𝕊.Tame n (fun i => 𝕊.den (𝕊.cons (𝕊.den (ρ i) a) (ρ i)) B) := by
    rw [← e]
    exact tame_of_unif_sort (fun i => (HBa _ _ (hρ i)).2.2.1) (HBaU n I ρ w hρ hctx)
  rw [e]
  exact unif_mkApp (D := fun i => 𝕊.den (ρ i) A) (F := fun i x => 𝕊.den (𝕊.cons x (ρ i)) B)
    (g := fun i => 𝕊.den (ρ i) f) (a := fun i => 𝕊.den (ρ i) a)
    (HfU n I ρ w hρ hctx) (fun i => (Hf _ _ (hρ i)).2.2.1) (fun i => (Ha _ _ (hρ i)).2.2.1)
    (HaU n I ρ w hρ hctx) hT

/-- The uniformity of an abstraction at one valuation, in the form the element set of a Π
record asks for. -/
theorem SemDU.piUnif {Γ : List VExpr} {A B : VExpr} {d : (Nat → 𝕊.S) → 𝕊.S}
    (H : 𝕊.SemDU Γ (fun ρ => 𝕊.mkLam (𝕊.den ρ A) fun x => d (𝕊.cons x ρ)) (.forallE A B))
    {ρ : Nat → 𝕊.S} {w : Nat → PVal} (hρ : 𝕊.ValOK Γ ρ w)
    (hFv : ∀ x, 𝕊.mem x (𝕊.El (𝕊.den ρ A)) → 𝕊.Valid (𝕊.den (𝕊.cons x ρ) B))
    (hf : ∀ x, 𝕊.mem x (𝕊.El (𝕊.den ρ A)) → 𝕊.mem (d (𝕊.cons x ρ)) (𝕊.El (𝕊.den (𝕊.cons x ρ) B)))
    (hDc : ¬ 𝕊.IsCand (𝕊.den ρ A))
    (hall : ¬ ∀ x, 𝕊.mem x (𝕊.El (𝕊.den ρ A)) → 𝕊.IsCand (𝕊.den (𝕊.cons x ρ) B)) :
    𝕊.PiUnif (𝕊.den ρ A) (fun x => 𝕊.den (𝕊.cons x ρ) B)
      (𝕊.fn (𝕊.El (𝕊.den ρ A)) fun x => d (𝕊.cons x ρ)) := by
  have h : 𝕊.Unif 0 PUnit (fun _ => 𝕊.den ρ (.forallE A B))
      (fun _ => 𝕊.mkLam (𝕊.den ρ A) fun x => d (𝕊.cons x ρ)) :=
    H 0 PUnit (fun _ => ρ) (fun _ => w) (fun _ => hρ) (ctxUnif_const hρ 0 _)
  obtain ⟨x₀, hx₀, hc₀⟩ : ∃ x₀, 𝕊.mem x₀ (𝕊.El (𝕊.den ρ A)) ∧
      ¬ 𝕊.IsCand (𝕊.den (𝕊.cons x₀ ρ) B) :=
    Classical.byContradiction fun hn => hall fun x hx =>
      Classical.byContradiction fun hc => hn ⟨x, hx, hc⟩
  have e1 : 𝕊.den ρ (.forallE A B) =
      𝕊.tPi (𝕊.den ρ A) (fun x => 𝕊.den (𝕊.cons x ρ) B) := by
    show 𝕊.mkPi _ _ = _
    rw [mkPi, if_neg hDc, if_neg hall]
  rw [e1, mkLam_eq_fn (F := fun x => 𝕊.den (𝕊.cons x ρ) B) hx₀ (hFv _ hx₀) hc₀ (hf _ hx₀)] at h
  exact piUnif_of_unif h

/-- The denotation of a term depends only on the variables that occur in it. -/
theorem den_congr_closed (e : VExpr) : ∀ (k : Nat) (ρ ρ' : Nat → 𝕊.S), e.ClosedN k →
    (∀ i, i < k → ρ i = ρ' i) → 𝕊.den ρ e = 𝕊.den ρ' e := by
  induction e with
  | bvar i => exact fun k ρ ρ' hc h => h i hc
  | sort => exact fun _ _ _ _ _ => rfl
  | const => exact fun _ _ _ _ _ => rfl
  | proj => exact fun _ _ _ _ _ => rfl
  | app f a ihf iha =>
    intro k ρ ρ' hc h
    show 𝕊.mkApp _ _ = 𝕊.mkApp _ _
    rw [ihf k ρ ρ' hc.1 h, iha k ρ ρ' hc.2 h]
  | lam A b ihA ihb =>
    intro k ρ ρ' hc h
    show 𝕊.mkLam _ _ = 𝕊.mkLam _ _
    rw [ihA k ρ ρ' hc.1 h]
    congr 1
    funext d
    refine ihb (k + 1) _ _ hc.2 fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact h i (Nat.lt_of_succ_lt_succ hi)
  | forallE A B ihA ihB =>
    intro k ρ ρ' hc h
    show 𝕊.mkPi _ _ = 𝕊.mkPi _ _
    rw [ihA k ρ ρ' hc.1 h]
    congr 1
    funext d
    refine ihB (k + 1) _ _ hc.2 fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact h i (Nat.lt_of_succ_lt_succ hi)

theorem unif_of_isEmpty {m : Nat} {I : World} (hI : I → False) (H s : I → 𝕊.S) :
    𝕊.Unif m I H s := fun _ _ => ⟨(0, 0), Lf_of_isEmpty _ _ hI _ _⟩

/-- **The constant rule**: a constant with a closed type is an element of the denotation of
that type, which does not depend on the valuation, and elements are uniform. -/
theorem semU_const_of {Γ : List VExpr} {c : Name} {ls : List VLevel} {ty : VExpr}
    (hcl : ty.ClosedN 0) (H : 𝕊.Sem Γ (.const c ls) (.const c ls) ty) :
    𝕊.SemU Γ (.const c ls) ty := by
  intro n I ρ w hρ _
  by_cases hI : Nonempty I
  · obtain ⟨i₀⟩ := hI
    have e : (fun i => 𝕊.den (ρ i) ty) = fun _ => 𝕊.den (ρ i₀) ty :=
      funext fun i => den_congr_closed ty 0 _ _ hcl fun _ h => (Nat.not_lt_zero _ h).elim
    obtain ⟨⟨k, hv⟩, -, hm, -⟩ := H _ _ (hρ i₀)
    rw [e]
    exact (hv.unif_const I hm).mono (Nat.zero_le n)
  · exact unif_of_isEmpty (fun i => hI ⟨i⟩) _ _

end SetModel
end VEnv.Strengthening
end Lean4Lean
