import Lean4Lean.Theory.Typing.ShapeModel.RuleValidCore
import Lean4Lean.Theory.Typing.ShapeModel.EnvSigSyntax

/-!
# Validity of computation rules with a constructor major

For a rule `r` of a head `h` whose left body is `h pre major`, with
`pre = vars npre nf ++ idx` (the prefix variables, then index expressions) and
`major = c lv (ps ++ vars nf 0)` (a constructor applied to some arguments and the `nf` field
variables), and whose right body is `R`, this file proves the body claim of rule validity:
under a valuation `σ` fitting the binders (`Valuation.Fits`), `h pre major` and `R` have the same
approximations (`body_valid`), from hypotheses that isolate what depends on the kind of the rule:

* `hidx`: every field index read (`r.fieldIndex`) is semantically the field at `σ` (trivial for a
  literal occurrence; the leftover-parameter case needs a semantic argument);
* `hAB`: in mode AB (the major's family is not a proposition at the levels), a constructor shape
  approximating the major whose stored fields aligned with the rule's fields are above the keys
  (from the realization of constructor applications), and unstored fields are read or bottom;
* `hC`: in mode C, every rule of the head has this major constructor (D7) and every field that is
  not read through `r.fieldIndex` has a bottom key.

`⊆`: an approximation of the left body is below a table of the spine machine at argument shapes
approximating the arguments (`Interp.mkApps_head_inv`); junk tables are bottom (`Terminal`); a
firing rule is `r` itself (`major_ctor_eq`, through `Interp.ctor'_major_inv` and
`Coherent.struct_unique` for a collapsed structure major), and its valuation `ruleVal` is below
`σ`. `⊇`: an approximation of `R` is below one typed at an approximation of `R`'s type, which is
the left body's type at `σ`; the rule clause fires at argument shapes chosen from the keys, with
`ruleVal` above `σ` on the binders, and `Spine.realize_head'` realizes the spine.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Syntactic helpers -/

theorem vars_getElem? {count below i : Nat} (h : i < count) :
    (vars count below)[i]? = some (.bvar (below + (count - 1 - i))) := by
  simp [vars, h]

theorem vars_length' (count below : Nat) : (vars count below).length = count := by simp [vars]

theorem vars_getElem {count below i : Nat} (h : i < (vars count below).length) :
    (vars count below)[i] = .bvar (below + (count - 1 - i)) := by
  have := vars_getElem? (count := count) (below := below) (i := i) (by simpa [vars_length'] using h)
  rw [List.getElem?_eq_getElem h] at this
  exact Option.some.inj this

section helpers
variable [ShapeParams]

theorem lookupVar_eq_getD {b : Nat} :
    ∀ {vs : List (Option Nat)} {args : List TShape} {j : Nat},
      vs[j]? = some (some b) → (∀ j' < j, vs[j']? ≠ some (some b)) →
      lookupVar b vs args = args.getD j .bot
  | [], _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _ => by simp
  | v :: vs, a :: as, 0, h, _ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [lookupVar]
  | v :: vs, a :: as, j + 1, h, hf => by
    have h0 := hf 0 (Nat.zero_lt_succ _)
    simp only [List.getElem?_cons_zero, ne_eq] at h0
    have ih := lookupVar_eq_getD (vs := vs) (args := as) (j := j) (by simpa using h)
      (fun j' hj' => by simpa using hf (j' + 1) (by omega))
    rcases v with _ | b'
    · simpa [lookupVar] using ih
    · have hb : b' ≠ b := fun e => h0 (by rw [e])
      simpa [lookupVar, hb] using ih

end helpers

theorem fieldPos_range_reverse {nf b : Nat} (hb : b < nf) :
    fieldPos b (List.range nf).reverse = some (nf - 1 - b) := by
  induction nf with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, fieldPos]
    by_cases h : n = b
    · subst h; simp
    · rw [if_neg h, ih (by omega)]; simp; omega

theorem fieldPos_range_reverse_none {nf b : Nat} (hb : nf ≤ b) :
    fieldPos b (List.range nf).reverse = none := by
  induction nf with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, fieldPos]
    rw [if_neg (by omega), ih (by omega)]; rfl

section ruleVal
variable [SemSig] {r : Rule} {npre nf : Nat} {idx : List VExpr} {c : Name} {lv : List VLevel}

theorem ruleVal_field (hnb : r.nbind = npre + nf)
    (hmaj : r.major = some ⟨c, lv, (List.range nf).reverse⟩) (hb : b < nf) :
    ruleVal r args fs? b = ruleField r args fs? nf (nf - 1 - b) := by
  simp only [ruleVal, hnb, hmaj, if_pos (show b < npre + nf by omega),
    fieldPos_range_reverse hb, List.length_reverse, List.length_range]

theorem ruleVal_var (hnb : r.nbind = npre + nf)
    (hmaj : r.major = some ⟨c, lv, (List.range nf).reverse⟩)
    (hrv : r.vars = (vars npre nf ++ idx).map argVar) (hb1 : nf ≤ b) (hb2 : b < npre + nf) :
    ruleVal r args fs? b = args.getD (nf + npre - 1 - b) .bot := by
  simp only [ruleVal, hnb, hmaj, if_pos hb2, fieldPos_range_reverse_none hb1, hrv]
  apply lookupVar_eq_getD
  · rw [List.getElem?_map, List.getElem?_append_left (by simp [vars_length']; omega),
      vars_getElem? (by omega)]
    simp [argVar]; omega
  · intro j' hj' h
    rw [List.getElem?_map, List.getElem?_append_left (by simp [vars_length']; omega),
      vars_getElem? (by omega)] at h
    simp [argVar] at h; omega

theorem ruleVal_out (hb : r.nbind ≤ b) : ruleVal r args fs? b = .bot := by
  simp only [ruleVal, if_neg (show ¬b < r.nbind by omega)]

end ruleVal

/-! ### Constructor majors -/

variable {env : VEnv} [SemSig] [SemSig.Coherent]

theorem wshape_list_ext : ∀ {l l' : List (WShape n)}, l.map (·.val) = l'.map (·.val) → l = l'
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [WShape.ext h.1, wshape_list_ext h.2]

theorem TShape.ctor'_le_ctor'_cases {l₁ : List (WShape n₁)} {l₂ : List (WShape n₂)}
    (h : (WShape.ctor' c₁ l₁).T ≤ (WShape.ctor' c₂ l₂).T) :
    (IsStruct c₁ ∧ ∀ x ∈ l₁, x ≤ .bot) ∨
      (c₁ = c₂ ∧ List.Forall₂ (fun x y => x.T ≤ y.T) l₁ l₂) := by
  have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂), WShape.lift_ctor' le₁,
    WShape.lift_ctor' le₂, WShape.ctor'_le] at h
  by_cases hs : IsStruct c₁ → WShape.ListNonZero (l₁.map (WShape.lift (max n₁ n₂)))
  · obtain ⟨l', h', he, hl⟩ := h hs
    unfold WShape.ctor' at he
    split at he
    · have := congrArg (·.1) he
      simp only [WShape.ctor] at this
      injection this with hc hm
      subst hc
      right; refine ⟨rfl, ?_⟩
      have hl'eq : l' = l₂.map (WShape.lift (max n₁ n₂)) := by
        exact wshape_list_ext (by simpa using hm.symm)
      rw [hl'eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff] at hl
      exact hl.imp fun x y h => (TShape.LE.def le₁ le₂).2 h
    · cases congrArg (·.1) he
  · left
    simp only [Classical.not_imp] at hs
    refine ⟨hs.1, fun x hx => ?_⟩
    have hx2 : ¬¬(x.lift (max n₁ n₂)).1 ≤ Shape.bot := fun hn =>
      hs.2 ⟨_, List.mem_map_of_mem hx, hn⟩
    exact WShape.le_bot.2 ((WShape.lift_le_bot le₁).1 (Classical.not_not.1 hx2))

theorem TShape.ctor'_le_bot_cases {l : List (WShape n)} (h : (WShape.ctor' c l).T ≤ .bot) :
    IsStruct c ∧ ∀ x ∈ l, x ≤ .bot := by
  rw [TShape.le_bot] at h
  change WShape.ctor' c l = WShape.bot at h
  unfold WShape.ctor' at h
  split at h
  · cases congrArg (·.1) h
  · rename_i hs
    simp only [Classical.not_imp] at hs
    refine ⟨hs.1, fun x hx => ?_⟩
    have := hs.2
    simp only [WShape.ListNonZero, not_exists, not_and] at this
    exact Classical.not_not.1 (this x hx)

theorem TShape.ctor'_le_lam'_cases {l : List (WShape n)} {g : WShapeFun k}
    (h : (WShape.ctor' c l).T ≤ (WShape.lam' g).T) : IsStruct c ∧ ∀ x ∈ l, x ≤ .bot := by
  unfold WShape.ctor' at h
  split at h
  · exact absurd h TShape.ctor_not_le_lam'
  · rename_i hs
    simp only [Classical.not_imp] at hs
    refine ⟨hs.1, fun x hx => ?_⟩
    have := hs.2
    simp only [WShape.ListNonZero, not_exists, not_and] at this
    exact Classical.not_not.1 (this x hx)

theorem forall₂_interp_of_le {l₁ : List (WShape n₁)} {l₂ : List (WShape n₂)} {l₃ : List VExpr}
    (h₁ : List.Forall₂ (fun x y => x.T ≤ y.T) l₁ l₂)
    (h₂ : List.Forall₂ (fun y A => Interp env σ y.T A) l₂ l₃) :
    List.Forall₂ (fun x A => Interp env σ x.T A) l₁ l₃ := by
  induction h₁ generalizing l₃ with
  | nil => cases h₂; exact .nil
  | cons h _ ih => cases h₂ with | cons h' t' => exact .cons (h'.mono h) (ih t')

/-- A constructor shape approximating a constructor application: either it collapses (a
structure constructor with bottom fields), or it is a shape of the same constructor, the
application is saturated, and the stored fields approximate the stored arguments. -/
theorem Interp.ctor'_major_inv {c c' : Name} {ci : CtorInfo} (hci : SemSig.ctor c = some ci)
    {fs : List (WShape n)}
    (H : Interp env σ (WShape.ctor' c' fs).T (VExpr.mkApps (.const c lv) margs)) :
    (IsStruct c' ∧ ∀ x ∈ fs, x ≤ .bot) ∨
      (c' = c ∧ margs.length = ci.nparams + ci.nfields ∧
        List.Forall₂ (fun x A => Interp env σ x.T A) fs (margs.drop ci.nparams)) := by
  have hnr : ∀ r, SemSig.rules r → r.head ≠ .const c := fun r hr =>
    SemSig.Coherent.ctor_no_rule hci hr
  rcases Interp.mkApps_const_inv hnr H with hb | ⟨k, rargs, y, hC, hy, hargs⟩
  · exact .inl (TShape.ctor'_le_bot_cases hb)
  cases hC with
  | bot => exact .inl (TShape.ctor'_le_bot_cases (hy.trans TShape.bot_eqv.1))
  | lam _ h2 => exact .inl (TShape.ctor'_le_lam'_cases (hy.trans h2))
  | ctor e1 e2 e3 e4 =>
    cases e1; cases hci.symm.trans e2
    rcases TShape.ctor'_le_ctor'_cases (hy.trans e4) with h | ⟨rfl, hl⟩
    · exact .inl h
    · refine .inr ⟨rfl, by rw [← hargs.length_eq, List.length_reverse, e3], ?_⟩
      exact forall₂_interp_of_le hl (forall₂_drop hargs ci.nparams)
  | rigid e1 e2 => cases e1; rw [hci] at e2; cases e2
  | rule e1 e2 => cases hnr _ e1 e2
  | ruleAB e1 e2 => cases hnr _ e1 e2
  | ruleC e1 e2 => cases hnr _ e1 e2

/-! ### The body claim, `⊆` -/

theorem forall₂_snoc_inv {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {a : α} {b : β},
      List.Forall₂ R (l ++ [a]) (l' ++ [b]) → List.Forall₂ R l l' ∧ R a b
  | [], [], _, _, .cons h .nil => ⟨.nil, h⟩
  | [], _ :: _ :: _, _, _, .cons _ h => by cases h
  | _ :: _ :: _, [], _, _, .cons _ h => by cases h
  | _ :: _, _ :: _, _, _, .cons h t => by
    have := forall₂_snoc_inv t
    exact ⟨.cons h this.1, this.2⟩

theorem List.getD_of_lt' {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem forall₂_getD {R : TShape → VExpr → Prop} {xs : List TShape} {As : List VExpr}
    (h : List.Forall₂ R xs As) {j : Nat} (hj : j < As.length) :
    R (xs.getD j .bot) (As.getD j (.sort .zero)) := by
  have hj' : j < xs.length := h.length_eq ▸ hj
  rw [List.getD_of_lt' hj', List.getD_of_lt' hj]
  exact forall₂_getElem h hj'

theorem forall₂_getD_append {R : TShape → VExpr → Prop} {xs : List TShape}
    {As Bs : List VExpr} (h : List.Forall₂ R xs (As ++ Bs)) {j : Nat} (hj : j < As.length) :
    R (xs.getD j .bot) (As.getD j (.sort .zero)) := by
  have := forall₂_getD h (j := j) (by rw [List.length_append]; omega)
  rwa [show (As ++ Bs).getD j (.sort .zero) = As.getD j (.sort .zero) by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]] at this

/-- The field index reads of a rule are semantically its fields at `σ`. -/
def FieldReads (env : VEnv) [SemSig] (σ : Valuation) (r : Rule) (pre : List VExpr) (nf : Nat) :
    Prop :=
  ∀ i < nf, ∀ j, r.fieldIndex[i]? = some (some j) → j < pre.length ∧
    ∀ t, Interp env σ t (pre.getD j (.sort .zero)) ↔ t ≤ σ (nf - 1 - i)

section body
variable {r : Rule} {h : Head} {ls : List VLevel} {npre nf : Nat} {idx idx' ps' : List VExpr}
  {c : Name} {lv lv' : List VLevel} {R : VExpr} {ci : CtorInfo}

theorem rule_arity_of (hrv : r.vars = (vars npre nf ++ idx).map argVar)
    (hmaj : r.major = some ⟨c, lv, (List.range nf).reverse⟩) :
    r.arity = npre + idx.length + 1 := by
  simp [Rule.arity, hrv, hmaj, vars_length']

/-- `⊆` of the body claim of rule validity. -/
theorem body_sub (hr : SemSig.rules r) (hh : r.head = h)
    (hnb : r.nbind = npre + nf) (hrv : r.vars = (vars npre nf ++ idx).map argVar)
    (hmaj : r.major = some ⟨c, lv, (List.range nf).reverse⟩) (hrhs : r.rhs = R)
    (hci : SemSig.ctor c = some ci) (hlen : idx'.length = idx.length)
    (hidx : FieldReads env σ r (vars npre nf ++ idx') nf)
    (H : Interp env σ m (VExpr.mkApps (h.toExpr ls)
      (vars npre nf ++ idx' ++ [VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)]))) :
    Interp env σ m (R.instL ls) := by
  have har := rule_arity_of hrv hmaj
  have hargl : (vars npre nf ++ idx' ++ [VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)]).length =
      r.arity := by simp [har, vars_length', hlen]; omega
  have hr' : ∀ r', SemSig.rules r' → r'.head = h →
      (vars npre nf ++ idx' ++ [VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)]).length ≤
        r'.arity := fun r' h1 h2 => by
    rw [hargl, Rule.arity_eq hr h1 (hh.trans h2.symm)]; exact Nat.le_refl _
  rcases Interp.mkApps_head_inv hr' H with hb | ⟨n, rargs, y, hC, hmy, hargs⟩
  · exact .mono hb .bot
  refine Interp.mono hmy ?_
  have hterm : Terminal h rargs.length := .inr ⟨r, hr, hh, by
    rw [← List.length_reverse, hargs.length_eq, hargl]⟩
  -- the valuation of a firing rule is below `σ`
  have hvar : ∀ (args : List TShape) (ex : List VExpr),
      List.Forall₂ (fun x A => Interp env σ x A) args (vars npre nf ++ idx' ++ ex) →
      ∀ b, nf ≤ b → b < npre + nf → args.getD (nf + npre - 1 - b) .bot ≤ σ b := by
    intro args ex hA b hb1 hb2
    have hj : nf + npre - 1 - b < (vars npre nf ++ idx').length := by
      simp [vars_length']; omega
    have := forall₂_getD_append hA hj
    rw [List.getD_of_lt' hj, List.getElem_append_left (by simp [vars_length']; omega),
      vars_getElem] at this
    rw [show nf + (npre - 1 - (nf + npre - 1 - b)) = b by omega] at this
    exact Interp.bvar_iff.1 this
  have hindex : ∀ (args : List TShape) (ex : List VExpr),
      List.Forall₂ (fun x A => Interp env σ x A) args (vars npre nf ++ idx' ++ ex) →
      ∀ i < nf, indexField r args i ≤ σ (nf - 1 - i) := by
    intro args ex hA i hi
    simp only [indexField]
    split
    · rename_i j hj
      obtain ⟨hjl, hjr⟩ := hidx i hi j hj
      exact (hjr _).1 (forall₂_getD_append hA hjl)
    · exact TShape.bot_le
  have hle : ∀ (args : List TShape) (ex : List VExpr) (fs? : Option (List TShape)),
      List.Forall₂ (fun x A => Interp env σ x A) args (vars npre nf ++ idx' ++ ex) →
      (∀ i < nf, ruleField r args fs? nf i ≤ σ (nf - 1 - i)) →
      (ruleVal r args fs?).LE σ := by
    intro args ex fs? hA hF b
    by_cases hb : b < nf
    · rw [ruleVal_field hnb hmaj hb]
      have := hF (nf - 1 - b) (by omega)
      rwa [show nf - 1 - (nf - 1 - b) = b by omega] at this
    by_cases hb2 : b < npre + nf
    · rw [ruleVal_var hnb hmaj hrv (by omega) hb2]
      exact hvar args ex hA b (by omega) hb2
    · rw [ruleVal_out (by omega)]; exact TShape.bot_le
  cases hC with
  | bot => exact .bot
  | lam hf hle' => exact .mono (hle'.trans (Const.lam_le_bot_of_terminal hf hterm)) .bot
  | ctor e1 e2 => exact absurd (hh.trans e1) (SemSig.Coherent.ctor_no_rule e2 hr)
  | rigid e1 _ e3 => exact absurd (hh.trans e1) (e3 r hr)
  | rule e1 e2 _ e4 =>
    have := (SemSig.Coherent.same_shape e1 hr (e2.trans hh.symm)).2
    simp [e4, hmaj] at this
  | ruleAB e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 =>
    rename_i n₀ r' mj' ci' rargs₀ a fs'
    rw [List.reverse_cons] at hargs
    obtain ⟨hpre, hmaj'⟩ := forall₂_snoc_inv hargs
    have hpre' : List.Forall₂ (fun x A => Interp env σ x A) (rargs₀.reverse.map (·.T))
        (vars npre nf ++ idx' ++ []) := by
      rw [List.append_nil]; exact List.forall₂_map_left_iff.2 hpre
    have hM : Interp env σ (WShape.ctor' mj'.ctor fs').T
        (VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)) := hmaj'.mono (WShape.LE.T e9)
    have hfam := SemSig.Coherent.major_family e1 hr (e2.trans hh.symm) e4 hmaj e5 hci
    have hcases := Interp.ctor'_major_inv hci hM
    have hcc : mj'.ctor = c := by
      rcases hcases with ⟨hs, -⟩ | ⟨e, -⟩
      · exact (SemSig.Coherent.struct_unique hs e5 hci hfam.1.symm).symm
      · exact e
    obtain rfl := SemSig.Coherent.major_ctor_eq e1 hr (e2.trans hh.symm) e4 hmaj hcc
    rw [hmaj] at e4; cases e4
    rw [hrhs] at e10
    refine e10.mono_l (hle _ _ _ hpre' fun i hi => ?_)
    simp only [ruleField]
    split
    · rename_i hal
      simp only [List.length_map] at hal ⊢
      rcases hcases with ⟨-, hbot⟩ | ⟨-, hml, hfa⟩
      · rw [List.getD_of_lt' (by simp; omega)]
        simp only [List.getElem_map]
        exact (TShape.le_bot.2 (WShape.le_bot.1 (hbot _ (List.getElem_mem _)))).trans TShape.bot_le
      · have hnfc : fs'.length = ci.nfields := by
          rw [e8]; simp [SemSig.nfields, hci]
        have hk : i + fs'.length - nf < fs'.length := by omega
        rw [List.getD_of_lt' (by simpa using hk)]
        simp only [List.getElem_map]
        have hx := forall₂_getElem hfa hk
        have hpos : ci.nparams + (i + fs'.length - nf) = ps'.length + i := by
          simp [vars_length'] at hml; omega
        simp only [List.getElem_drop, hpos] at hx
        rw [List.getElem_append_right (by omega), vars_getElem] at hx
        rw [show 0 + (nf - 1 - (ps'.length + i - ps'.length)) = nf - 1 - i by omega] at hx
        exact Interp.bvar_iff.1 hx
    · exact hindex _ _ hpre' i hi
  | ruleC e1 e2 e3 e4 e5 e6 e7 e8 e9 =>
    rename_i r' mj' ci'
    have hcc : mj'.ctor = c := by
      have := e7 r hr hh
      rw [hmaj] at this; exact (Option.some.inj this).symm
    obtain rfl := SemSig.Coherent.major_ctor_eq e1 hr (e2.trans hh.symm) e4 hmaj hcc
    rw [hmaj] at e4; cases e4
    rw [hrhs] at e9
    have hargs' : List.Forall₂ (fun x A => Interp env σ x A) (rargs.reverse.map (·.T))
        (vars npre nf ++ idx' ++ [VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)]) :=
      List.forall₂_map_left_iff.2 hargs
    exact e9.mono_l (hle _ _ none hargs' fun i hi => hindex _ _ hargs' i hi)

/-- Argument approximations of the prefix chosen from the keys: every prefix variable gets its
key, every field read gets (a key equivalent to) its field's key. -/
theorem prefix_keys (hidx : FieldReads env σ r (vars npre nf ++ idx') nf) :
    ∃ xs : List TShape, List.Forall₂ (fun x A => Interp env σ x A) xs (vars npre nf ++ idx') ∧
      (∀ b, nf ≤ b → b < npre + nf → σ b ≤ xs.getD (nf + npre - 1 - b) .bot) ∧
      (∀ i < nf, ∀ j, r.fieldIndex[i]? = some (some j) → σ (nf - 1 - i) ≤ xs.getD j .bot) := by
  classical
  let pre := vars npre nf ++ idx'
  let f : Nat → TShape := fun j =>
    if h : ∃ i, i < nf ∧ r.fieldIndex[i]? = some (some j) then σ (nf - 1 - h.choose)
    else match pre.getD j (.sort .zero) with
      | .bvar b => σ b
      | _ => .bot
  have hf : ∀ j < pre.length, Interp env σ (f j) (pre.getD j (.sort .zero)) := by
    intro j hj
    simp only [f]
    split
    · rename_i h
      exact ((hidx _ h.choose_spec.1 j h.choose_spec.2).2 _).2 .rfl
    · split
      · rename_i b hb; rw [hb]; exact .bvar' 
      · exact .bot
  have hfr : ∀ i < nf, ∀ j, r.fieldIndex[i]? = some (some j) → σ (nf - 1 - i) ≤ f j := by
    intro i hi j hj
    have hex : ∃ i, i < nf ∧ r.fieldIndex[i]? = some (some j) := ⟨i, hi, hj⟩
    simp only [f, dif_pos hex]
    have h1 := hidx i hi j hj
    have h2 := hidx _ hex.choose_spec.1 j hex.choose_spec.2
    exact (h2.2 _).1 ((h1.2 _).2 .rfl)
  refine ⟨(List.range pre.length).map f, ?_, ?_, ?_⟩
  · refine List.forall₂_of_getElem (by simp [pre]) fun j h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    have := hf j h2
    rwa [List.getD_of_lt' h2] at this
  · intro b hb1 hb2
    have hj : nf + npre - 1 - b < pre.length := by simp [pre, vars_length']; omega
    rw [List.getD_of_lt' (by simpa using hj)]
    simp only [List.getElem_map, List.getElem_range]
    have hpre : pre.getD (nf + npre - 1 - b) (.sort .zero) = .bvar b := by
      rw [List.getD_of_lt' hj]
      simp only [pre]
      rw [List.getElem_append_left (by simp [vars_length']; omega), vars_getElem]
      congr 1; omega
    simp only [f]
    split
    · rename_i h
      have := ((hidx _ h.choose_spec.1 _ h.choose_spec.2).2 (σ b)).1
      rw [hpre] at this
      exact this .bvar'
    · rw [hpre]; exact .rfl
  · intro i hi j hj
    have hjl := (hidx i hi j hj).1
    rw [List.getD_of_lt' (by simpa [pre] using hjl)]
    simp only [List.getElem_map, List.getElem_range]
    exact hfr i hi j hj

theorem depth_bound (xs : List TShape) : ∃ K, ∀ x ∈ xs, x.1 ≤ K :=
  ⟨xs.foldr (fun x k => max x.1 k) 0, by
    intro x hx
    induction xs with
    | nil => cases hx
    | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.1 hx with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)⟩

theorem getD_map_lift_ge {xs : List TShape} {N : Nat} (hN : ∀ x ∈ xs, x.1 ≤ N) (j : Nat) :
    xs.getD j .bot ≤ ((xs.map fun x => x.2.lift N).map (·.T)).getD j .bot := by
  by_cases hj : j < xs.length
  · rw [List.getD_of_lt' hj, List.getD_of_lt' (by simpa using hj)]
    simp only [List.getElem_map]
    exact (TShape.lift_eqv (hN _ (List.getElem_mem hj))).2
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact TShape.bot_le

theorem forall₂_map_lift {xs : List TShape} {As : List VExpr} {N : Nat}
    (hN : ∀ x ∈ xs, x.1 ≤ N) (h : List.Forall₂ (fun x A => Interp env σ x A) xs As) :
    List.Forall₂ (fun x A => Interp env σ (WShape.T x) A) (xs.map fun x => x.2.lift N) As :=
  List.forall₂_map_left_iff.2 <| (h.and_mem).imp fun x _ ⟨hx, hm, _⟩ => hx.lift (hN x hm)

/-- `⊇` of the body claim of rule validity. -/
theorem body_sup (hcl : ConstClosed env) (hr : SemSig.rules r) (hh : r.head = h)
    (huv : ls.length = r.uvars)
    (hnb : r.nbind = npre + nf) (hrv : r.vars = (vars npre nf ++ idx).map argVar)
    (hmaj : r.major = some ⟨c, lv, (List.range nf).reverse⟩) (hrhs : r.rhs = R)
    (hfil : r.fieldIndex.length = nf)
    (hci : SemSig.ctor c = some ci) (hlen : idx'.length = idx.length)
    (hidx : FieldReads env σ r (vars npre nf ++ idx') nf)
    (W : Valuation.Fits env Γ₀ Γ σ)
    (hL : StrongSound env Γ (VExpr.mkApps (h.toExpr ls)
      (vars npre nf ++ idx' ++ [VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)])) B₁)
    (hRr : StrongSound env Γ (R.instL ls) B₂)
    (hB : ∀ m, Interp env σ m B₁ ↔ Interp env σ m B₂)
    (hRcl : (R.instL ls).ClosedN (npre + nf))
    (hAB : SemSig.famProp ci.family (RuleMajor.lvls ⟨c, lv, (List.range nf).reverse⟩ ls) = false →
      ∃ n₀, ∃ fs : List (WShape n₀), fs.length = SemSig.nfields c ∧
        Interp env σ (WShape.ctor' c fs).T (VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)) ∧
        ∀ i < nf, (nf ≤ i + fs.length → σ (nf - 1 - i) ≤ (fs.getD (i + fs.length - nf) .bot).T) ∧
          (i + fs.length < nf → (∃ j, r.fieldIndex[i]? = some (some j)) ∨ σ (nf - 1 - i) ≤ .bot))
    (hC : SemSig.famProp ci.family (RuleMajor.lvls ⟨c, lv, (List.range nf).reverse⟩ ls) = true →
      (∀ r', SemSig.rules r' → r'.head = h → r'.major.map (·.ctor) = some c) ∧
        ∀ i < nf, r.fieldIndex[i]? = some none → σ (nf - 1 - i) ≤ .bot)
    (H : Interp env σ m (R.instL ls)) :
    Interp env σ m (VExpr.mkApps (h.toExpr ls)
      (vars npre nf ++ idx' ++ [VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)])) := by
  obtain ⟨m₁, a₁, hle, hm₁, ha₁, hty⟩ := hRr.sound W H
  have ha₁' : Interp env σ a₁ B₁ := (hB a₁).2 ha₁
  refine Interp.mono hle ?_
  obtain ⟨xs, hxs, hxv, hxf⟩ := prefix_keys hidx
  have hxl : xs.length = r.vars.length := by
    rw [hxs.length_eq, hrv]; simp [vars_length', hlen]
  have hm₁' : ∀ ρ' : Valuation, (∀ b < npre + nf, σ b ≤ ρ' b) →
      Interp env ρ' m₁ (r.rhs.instL ls) := by
    intro ρ' hρ'
    rw [hrhs]
    have := Interp.closed hRcl (ρ' := fun b => if b < npre + nf then σ b else .bot)
      (fun i hi => by simp [hi]) hm₁
    refine this.mono_l fun b => ?_
    by_cases hb : b < npre + nf
    · simp only [hb, if_true]; exact hρ' b hb
    · simp only [hb, if_false]; exact TShape.bot_le
  -- the variable and field reads of the chosen arguments are above the keys
  have hge : ∀ (args : List TShape) (fs? : Option (List TShape)),
      (∀ j, xs.getD j .bot ≤ args.getD j .bot) →
      (∀ i < nf, σ (nf - 1 - i) ≤ ruleField r args fs? nf i) →
      ∀ b < npre + nf, σ b ≤ ruleVal r args fs? b := by
    intro args fs? hA hF b hb2
    by_cases hb : b < nf
    · rw [ruleVal_field hnb hmaj hb]
      have := hF (nf - 1 - b) (by omega)
      rwa [show nf - 1 - (nf - 1 - b) = b by omega] at this
    · rw [ruleVal_var hnb hmaj hrv (by omega) hb2]
      exact (hxv b (by omega) hb2).trans (hA _)
  have hindex : ∀ (args : List TShape), (∀ j, xs.getD j .bot ≤ args.getD j .bot) →
      ∀ i < nf, (r.fieldIndex[i]? = some none → σ (nf - 1 - i) ≤ .bot) →
      σ (nf - 1 - i) ≤ indexField r args i := by
    intro args hA i hi hnone
    simp only [indexField]
    split
    · rename_i j hj; exact (hxf i hi j hj).trans (hA j)
    · rename_i hnot
      have hlt : i < r.fieldIndex.length := by omega
      rw [List.getElem?_eq_getElem hlt] at hnot
      cases hfi : r.fieldIndex[i] with
      | none => exact hnone (by rw [List.getElem?_eq_getElem hlt, hfi])
      | some j => exact absurd (by rw [hfi]) (hnot j)
  obtain ⟨K, hK⟩ := depth_bound xs
  cases hfp : SemSig.famProp ci.family (RuleMajor.lvls ⟨c, lv, (List.range nf).reverse⟩ ls) with
  | false =>
    obtain ⟨n₀, fs, hfsl, hfsI, hfal⟩ := hAB hfp
    let N := max n₀ K
    have hn₀ : n₀ ≤ N := Nat.le_max_left _ _
    have hKN : ∀ x ∈ xs, x.1 ≤ N + 1 := fun x hx => Nat.le_succ_of_le
      (Nat.le_trans (hK x hx) (Nat.le_max_right _ _))
    let rargsW : List (WShape (N+1)) := xs.map fun x => x.2.lift (N+1)
    let fsN : List (WShape N) := fs.map (·.lift N)
    have hargsT : ∀ j, xs.getD j .bot ≤ (rargsW.map (·.T)).getD j .bot :=
      getD_map_lift_ge hKN
    refine Spine.realize_head' hcl W hty ha₁' hL (rargs := WShape.ctor' c fsN :: rargsW.reverse)
      ?_ ?_
    · rw [List.reverse_cons, List.reverse_reverse]
      refine List.Forall₂.append_of_left (by simp [rargsW, hxs.length_eq]) |>.2 ⟨?_, .cons ?_ .nil⟩
      · exact forall₂_map_lift hKN hxs
      · have := hfsI.lift (Nat.succ_le_succ hn₀)
        simp only [WShape.T, WShape.lift_ctor' hn₀] at this
        exact this
    refine Const.ruleAB hr hh huv hmaj hci hfp (by simp [rargsW, hxl]) (by simp [fsN, hfsl])
      WShape.LE.rfl ?_
    rw [List.reverse_reverse]
    refine hm₁' _ (hge _ _ hargsT fun i hi => ?_)
    simp only [ruleField, List.length_map, fsN]
    split
    · rename_i hal
      have hk : i + fs.length - nf < fs.length := by omega
      rw [List.getD_of_lt' (by simpa using hk)]
      simp only [List.getElem_map]
      have := (hfal i hi).1 hal
      rw [List.getD_of_lt' hk] at this
      exact this.trans (TShape.lift_eqv hn₀).2
    · rename_i hal
      refine hindex _ hargsT i hi fun hnone => ?_
      rcases (hfal i hi).2 (by omega) with ⟨j, hj⟩ | hb
      · rw [hnone] at hj; cases hj
      · exact hb
  | true =>
    obtain ⟨hD7, hbots⟩ := hC hfp
    let N := K
    let rargsW : List (WShape N) := xs.map fun x => x.2.lift N
    have hargsT : ∀ j, xs.getD j .bot ≤
        ((rargsW ++ [WShape.bot]).map (fun x : WShape N => x.T)).getD j .bot := by
      intro j
      refine (getD_map_lift_ge hK j).trans ?_
      by_cases hj : j < xs.length
      · rw [List.getD_of_lt' (by simpa [rargsW] using hj),
          List.getD_of_lt' (by simp [rargsW]; omega)]
        simp [rargsW, List.getElem_append_left (show j < (xs.map _).length by simpa using hj)]
        exact TShape.LE.rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa [rargsW] using hj)]
        exact TShape.bot_le
    refine Spine.realize_head' hcl W hty ha₁' hL (rargs := WShape.bot :: rargsW.reverse) ?_ ?_
    · rw [List.reverse_cons, List.reverse_reverse]
      refine List.Forall₂.append_of_left (by simp [rargsW, hxs.length_eq]) |>.2
        ⟨?_, .cons .bot .nil⟩
      exact forall₂_map_lift hK hxs
    refine Const.ruleC hr hh huv hmaj hci hfp (fun r' h1 h2 => hD7 r' h1 h2)
      (by simp [rargsW, hxl]) ?_
    rw [List.reverse_cons, List.reverse_reverse]
    exact hm₁' _ (hge _ _ hargsT fun i hi => hindex _ hargsT i hi (hbots i hi))

/-- Validity of a rule with a constructor major at one instance: the two sides are lambda
telescopes over the same domains, and for every valuation fitting the binders the hypotheses of
the body claim hold. -/
theorem majorRule_sound (hcl : ConstClosed env) (hr : SemSig.rules r) (hh : r.head = h)
    (huv : ls.length = r.uvars)
    (hnb : r.nbind = npre + nf) (hrv : r.vars = (vars npre nf ++ idx).map argVar)
    (hmaj : r.major = some ⟨c, lv, (List.range nf).reverse⟩) (hrhs : r.rhs = R)
    (hfil : r.fieldIndex.length = nf)
    (hci : SemSig.ctor c = some ci) (hlen : idx'.length = idx.length)
    {Ds : List VExpr} (hDs : Ds.length = npre + nf) (hRcl : (R.instL ls).ClosedN (npre + nf))
    (hL : StrongSound env [] (VExpr.wrapLams Ds (VExpr.mkApps (h.toExpr ls)
      (vars npre nf ++ idx' ++ [VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)]))) T)
    (hR : StrongSound env [] (VExpr.wrapLams Ds (R.instL ls)) T)
    (hσ : ∀ σ B, KeysFit env .nil Ds σ → Valuation.Fits env [] Ds.reverse σ →
      StrongSound env Ds.reverse (VExpr.mkApps (h.toExpr ls)
        (vars npre nf ++ idx' ++ [VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)])) B →
      FieldReads env σ r (vars npre nf ++ idx') nf ∧
      (SemSig.famProp ci.family (RuleMajor.lvls ⟨c, lv, (List.range nf).reverse⟩ ls) = false →
        ∃ n₀, ∃ fs : List (WShape n₀), fs.length = SemSig.nfields c ∧
          Interp env σ (WShape.ctor' c fs).T (VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)) ∧
          ∀ i < nf, (nf ≤ i + fs.length → σ (nf - 1 - i) ≤ (fs.getD (i + fs.length - nf) .bot).T) ∧
            (i + fs.length < nf → (∃ j, r.fieldIndex[i]? = some (some j)) ∨ σ (nf - 1 - i) ≤ .bot)) ∧
      (SemSig.famProp ci.family (RuleMajor.lvls ⟨c, lv, (List.range nf).reverse⟩ ls) = true →
        (∀ r', SemSig.rules r' → r'.head = h → r'.major.map (·.ctor) = some c) ∧
          ∀ i < nf, r.fieldIndex[i]? = some none → σ (nf - 1 - i) ≤ .bot)) :
    SoundEq env [] (VExpr.wrapLams Ds (VExpr.mkApps (h.toExpr ls)
      (vars npre nf ++ idx' ++ [VExpr.mkApps (.const c lv') (ps' ++ vars nf 0)])))
      (VExpr.wrapLams Ds (R.instL ls)) := by
  refine SoundEq.nil_of (Interp.wrapLams_congr fun σ K m => ?_)
  obtain ⟨B₁, B₂, W, h₁, h₂, hB⟩ := body_records .nil K hL hR fun _ => .rfl
  simp only [List.append_nil] at W h₁ h₂
  obtain ⟨hidx, hAB, hC⟩ := hσ σ B₁ K W h₁
  exact ⟨body_sub hr hh hnb hrv hmaj hrhs hci hlen hidx,
    body_sup hcl hr hh huv hnb hrv hmaj hrhs hfil hci hlen hidx W h₁ h₂ hB hRcl hAB hC⟩

end body

end

end Lean4Lean.ShapeModel
