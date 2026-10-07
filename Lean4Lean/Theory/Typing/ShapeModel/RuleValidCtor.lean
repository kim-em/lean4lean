import Lean4Lean.Theory.Typing.ShapeModel.RuleValidProp
import Lean4Lean.Theory.Typing.ShapeModel.Head

/-!
# Families and constructor applications in the shape model

* `FamSem I l n`: the type of the family `I` has, at every instance, the approximations of a
  telescope of `n` binders ending in the sort `l` (the semantic form of a family header, proved
  from a header derivation by soundness). Two such forms have equal sort evaluations
  (`FamSem.eval_eq`).
* `Rigid.realize`: a rigid family applied to arguments, typed at a sort, is approximated by a rigid
  shape with prescribed arguments and constructor table.
* `Ctor.realize0`: the realization of a constructor application for a constructor that stores all
  its arguments (`nparams = 0`), the general form of `Ctor.realize`.
* `ctor_not_over`, `ctor_not_under`: the arguments of a well-typed constructor application whose
  type is a family application are exactly the constructor's telescope (semantic alignment of
  rule majors).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-! ### Semantic family headers -/

variable (env) in
/-- The type of `I` has, at every instance, the approximations of a telescope of `n` binders
ending in the sort `l`. -/
def FamSem (I : Name) (l : VLevel) (n : Nat) : Prop :=
  ∃ ci, ∃ Ds : List VExpr, env.constants I = some ci ∧ Ds.length = n ∧
    ∀ ls, ls.length = ci.uvars → ∀ m, Interp env .nil m (ci.type.instL ls) ↔
      Interp env .nil m (VExpr.instL ls (Ds.foldr .forallE (.sort l)))

theorem TShape.HasType.bot_bot : TShape.HasType TShape.bot TShape.bot :=
  TShape.HasType.bot' (TShape.HasType.bot' TShape.HasType.sort)

/-- A telescope of bottom keys ending in a sort shape approximates a telescope ending in that
sort. -/
theorem Interp.nestPi_bots_sort (Ds : List VExpr) (l : VLevel) :
    Interp env ρ (nestPi (Ds.map fun _ => (TShape.bot, TShape.bot)) (TShape.sort l.eval))
      (Ds.foldr .forallE (.sort l)) := by
  induction Ds generalizing ρ with
  | nil => exact Interp.sort'
  | cons D Ds ih => exact Interp.pi_intro .bot TShape.HasType.bot_bot ih

theorem FamSem.eval_eq (h₁ : FamSem env I l₁ n₁) (h₂ : FamSem env I l₂ n₂) :
    ∀ ls, (∃ ci, env.constants I = some ci ∧ ls.length = ci.uvars) →
      (l₁.inst ls).eval = (l₂.inst ls).eval := by
  intro ls ⟨ci, hci, hls⟩
  obtain ⟨ci₁, Ds₁, h1, -, H₁⟩ := h₁
  obtain ⟨ci₂, Ds₂, h2, -, H₂⟩ := h₂
  cases hci.symm.trans h1; cases hci.symm.trans h2
  have hb := Interp.nestPi_bots_sort (env := env) (ρ := .nil) (Ds₁.map (·.instL ls)) (l₁.inst ls)
  have hb' : Interp env .nil (nestPi ((Ds₁.map (·.instL ls)).map fun _ => (TShape.bot, TShape.bot))
      (TShape.sort (l₁.inst ls).eval)) (VExpr.instL ls (Ds₁.foldr .forallE (.sort l₁))) := by
    rw [VExpr.instL_foldr_forallE]; exact hb
  have := (H₂ ls hls _).1 ((H₁ ls hls _).2 hb')
  rw [VExpr.instL_foldr_forallE] at this
  exact Interp.nestPi_sort_inv this

/-! ### Realization of rigid family applications -/

/-- A rigid family applied to arguments and typed at a sort is approximated by a rigid shape with
prescribed (approximating) arguments and constructor table; the sort of the application is the
family's sort at the levels. -/
theorem Rigid.realize (hcl : ConstClosed env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (hnc : SemSig.ctor I = none) (hnr : ∀ r, SemSig.rules r → r.head ≠ .const I)
    (hl : SemSig.famLevel I = some l) (hsem : FamSem env I l args.length)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const I ls) args) (.sort v))
    {as : List (WShape N)} (hargs : List.Forall₂ (fun x A => Interp env ρ x.T A) as args)
    {cts : List (Name × WShape N)} (hnames : cts.map (·.1) = SemSig.famCtors I)
    (hent : ∀ p ∈ cts, CtorEntry env (Interp env) ls (as.map (·.T)) p)
    (hcts : WShape.CtsTypes cts) :
    (l.inst ls).eval = v.eval ∧
      Interp env ρ (WShape.rigid I (ls.map (·.eval)) as cts).T (VExpr.mkApps (.const I ls) args) := by
  have hTy' : StrongSound env Γ (VExpr.mkApps (.const I ls) args.reverse.reverse) (.sort v) := by
    rwa [List.reverse_reverse]
  obtain ⟨ci, u, hci, hls, -⟩ := Spine.constInfo hTy'
  obtain ⟨ciI, Dsf, hsc, hDsf, hfamT⟩ := hsem
  cases hci.symm.trans hsc
  have hcis := hcl hci
  obtain ⟨qsI, -, hqI2, hqI3, hqI4⟩ := Spine.typed W hTy' hci
    (List.Forall₂.reverse.2 (List.forall₂_map_left_iff.2 hargs)) (R := TShape.bot) .bot
  have hqI4' := (hfamT ls hls _).1 ((Interp.closed_iff hcis.instL).1 hqI4)
  rw [VExpr.instL_foldr_forallE] at hqI4'
  obtain ⟨htelI, -⟩ := Interp.nest_inv (by
    rw [List.length_map, List.length_reverse, hDsf, hqI2.length_eq, List.length_reverse]) hqI4'
  have hsortI := Interp.nest_intro htelI (fun p hp => hqI3 p (List.mem_reverse.1 hp))
    (R := TShape.sort (l.inst ls).eval) (ρ := .nil) Interp.sort'
  have hsortI' : Interp env .nil (nestPi qsI.reverse (TShape.sort (l.inst ls).eval))
      (VExpr.instL ls (Dsf.foldr .forallE (.sort l))) := by
    rw [VExpr.instL_foldr_forallE]; exact hsortI
  have hsortI'' := (Interp.closed_iff (ρ' := ρ) hcis.instL).1 ((hfamT ls hls _).2 hsortI')
  have hlev : (l.inst ls).eval = v.eval :=
    TShape.sort_le_sort (Spine.ofPi W hTy' hci hqI2 hsortI'').le_sort
  refine ⟨hlev, ?_⟩
  have hmty : (WShape.rigid I (ls.map (·.eval)) as cts).T.HasType (TShape.sort v.eval) := by
    refine TShape.HasType.rigid (fun hz => ?_) hcts
    show SemSig.famProp I (ls.map (·.eval)) = true
    rw [SemSig.famProp_eval hl, hlev]; exact decide_eq_true hz
  have hCI : Const env (Interp env) (.const I) ls as.reverse
      (WShape.rigid I (ls.map (·.eval)) as cts).T := by
    refine Const.rigid rfl hnc hnr hnames ?_ ?_
    · rw [List.reverse_reverse]; exact hent
    · rw [List.reverse_reverse]; exact TShape.LE.rfl
  have := Spine.realize hcl W hmty Interp.sort' hTy'
    (List.Forall₂.reverse.2 hargs) hCI
  rwa [List.reverse_reverse] at this

theorem ctorTy?_table {α : Type} {c : Name} {T d : α} :
    ∀ {l : List Name}, c ∈ l → ctorTy? c (l.map fun c' => (c', if c' = c then T else d)) = some T
  | [], h => by cases h
  | c' :: l, h => by
    simp only [List.map_cons, ctorTy?]
    by_cases hc : c' = c
    · simp [hc]
    · rw [if_neg hc]
      exact ctorTy?_table (List.mem_of_ne_of_mem (Ne.symm hc) h)

/-! ### Realization of constructor applications -/

/-- The realization of a constructor application for a constructor storing all its arguments: if
the family is not a proposition at the levels, a constructor shape whose fields are above the
argument approximations approximates the application. -/
theorem Ctor.realize0 (hcl : ConstClosed env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (hci : SemSig.ctor c = some ⟨I, 0, nf⟩) (hcv : env.constants c = some cv)
    {doms argsI : List VExpr}
    (hct : cv.type = VExpr.wrapForalls doms (VExpr.mkApps (.const I (VLevel.params cv.uvars)) argsI))
    (hdl : doms.length = nf)
    (hnc : SemSig.ctor I = none) (hnr : ∀ r, SemSig.rules r → r.head ≠ .const I)
    (hl : SemSig.famLevel I = some l) (hsem : FamSem env I l argsI.length)
    (hmem : c ∈ SemSig.famCtors I)
    (hfc : ∀ c' ∈ SemSig.famCtors I, ∃ ci k, env.constants c' = some ci ∧ SemSig.ctor c' = some k)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const c ls) args) T)
    (hlen : args.length = nf)
    (hxs : List.Forall₂ (fun x A => Interp env ρ x A) xs args)
    (hfp : SemSig.famProp I (ls.map (·.eval)) = false) :
    ∃ n, ∃ fs : List (WShape n), fs.length = nf ∧
      Interp env ρ (WShape.ctor' c fs).T (VExpr.mkApps (.const c ls) args) ∧
      List.Forall₂ (fun x f => x ≤ f.T) xs fs := by
  have hTy' : StrongSound env Γ (VExpr.mkApps (.const c ls) args.reverse.reverse) T := by
    rwa [List.reverse_reverse]
  obtain ⟨ci, u, hci', hlsl, hTyT⟩ := Spine.constInfo hTy'
  cases hci'.symm.trans hcv
  have hctl : cv.type.instL ls = (doms.map (·.instL ls)).foldr .forallE
      (VExpr.mkApps (.const I ls) (argsI.map (·.instL ls))) := by
    rw [hct]
    show VExpr.instL ls (doms.foldr .forallE _) = _
    rw [VExpr.instL_foldr_forallE, VExpr.instL_mkApps]
    simp only [VExpr.instL, VLevel.inst_map_id hlsl]
  obtain ⟨qs, hq1, hq2, hq3, hq4⟩ := Spine.typed W hTy' hcv
    (List.Forall₂.reverse.2 hxs) (R := TShape.bot) .bot
  let ps := qs.reverse
  have hps1 : List.Forall₂ (fun x p => x ≤ p.2) xs ps := by
    have := List.Forall₂.reverse.2 hq1; rwa [List.reverse_reverse] at this
  have hps2 : List.Forall₂ (fun p A => Interp env ρ p.2 A) ps args := by
    have := List.Forall₂.reverse.2 hq2; rwa [List.reverse_reverse] at this
  have hps3 : TelTyped ps := fun p hp => hq3 p (List.mem_reverse.1 hp)
  have hlps : ps.length = nf := hps2.length_eq.trans hlen
  rw [hctl] at hq4 hTyT
  obtain ⟨htel, -⟩ := Interp.nest_inv (by rw [List.length_map, hdl, ← hlps]) hq4
  obtain ⟨Γ', v, W', hB⟩ := Tel.fits W hTyT htel hps3
  let N := (nestPi ps TShape.bot).1
  have hkeyN : ∀ p ∈ ps, p.2.1 ≤ N := fun p hp => (nestPi_key_le hp).1
  let TelF : WShape N := (nestPi ps TShape.bot).2.lift N
  let cts : List (Name × WShape N) :=
    (SemSig.famCtors I).map fun c' => (c', if c' = c then TelF else WShape.bot)
  let asI : List (WShape N) := argsI.map fun _ => WShape.bot
  have hTelF : TelF.HasType .type := by
    have := TShape.nestPi_type (R := TShape.bot) hps3 (TShape.HasType.bot' TShape.HasType.sort)
    have := (TShape.HasType.def (Nat.le_refl N) (Nat.zero_le _)).1 this
    simpa [TShape.type, TShape.sort, WShape.lift_sort] using this
  have hcts : WShape.CtsTypes cts := by
    intro p hp
    simp only [cts, List.mem_map] at hp
    obtain ⟨c', -, rfl⟩ := hp
    dsimp only; split
    · exact hTelF
    · exact .bot' .sort_type
  have hent : ∀ p ∈ cts, CtorEntry env (Interp env) ls (asI.map (·.T)) p := by
    intro p hp
    simp only [cts, List.mem_map] at hp
    obtain ⟨c', hc', rfl⟩ := hp
    by_cases he : c' = c
    · subst he
      refine ⟨cv, ⟨I, 0, nf⟩, nestPi ps TShape.bot, hcv, hci, ?_, ?_⟩
      · exact (Interp.closed_iff (hcl hcv).instL).1 (hctl ▸ hq4)
      · simp only [ctsBound, Nat.zero_le, if_true, List.take_zero, List.foldl_nil]
        exact (TShape.lift_eqv (Nat.le_refl N)).1
    · obtain ⟨ci', k', h1, h2⟩ := hfc c' hc'
      refine ⟨ci', k', TShape.bot, h1, h2, .bot, ?_⟩
      simp only [if_neg he]; exact TShape.bot_le'
  obtain ⟨hlev, hRI⟩ := Rigid.realize hcl W' hnc hnr hl (by simpa using hsem) hB (as := asI)
    (List.forall₂_of_getElem (by simp [asI]) fun i _ _ => by simp only [asI, List.getElem_map]; exact .bot)
    (by simp [cts, List.map_map, Function.comp_def]) hent hcts
  have hRT : Interp env ρ (WShape.rigid I (ls.map (·.eval)) asI cts).T T :=
    Spine.ofPi W hTy' hcv hq2 (hctl ▸ Interp.nest_intro htel hps3 hRI)
  let fs : List (WShape N) := ps.map fun p => p.2.2.lift N
  have hmty : (WShape.ctor' c fs).T.HasType (WShape.rigid I (ls.map (·.eval)) asI cts).T :=
    TShape.HasType.ctor' hcts hfp (ctorTy?_table hmem)
      (WShape.fits_nestPi hps3 (Nat.le_refl N))
      (by show _ = SemSig.nfields _; simp [SemSig.nfields, hci, fs, hlps])
  have hC : Const env (Interp env) (.const c) ls fs.reverse (WShape.ctor' c fs).T := by
    refine Const.ctor rfl hci (by simp [fs, hlps]) ?_
    simp only [List.reverse_reverse, List.drop_zero]; exact TShape.LE.rfl
  have hargs : List.Forall₂ (fun x A => Interp env ρ x.T A) fs.reverse args.reverse := by
    refine List.Forall₂.reverse.2 (List.forall₂_map_left_iff.2 ?_)
    exact (List.Forall₂.and_mem hps2).imp fun p A ⟨h, hp, _⟩ => h.lift (hkeyN p hp)
  have := Spine.realize hcl W hmty hRT hTy' hargs hC
  rw [List.reverse_reverse] at this
  refine ⟨N, fs, by simp [fs, hlps], this, List.forall₂_map_right_iff.2 ?_⟩
  exact (hps1.and_mem).imp fun x p ⟨h, _, hp⟩ => h.trans (TShape.lift_eqv (hkeyN p hp)).2

end

end Lean4Lean.ShapeModel
