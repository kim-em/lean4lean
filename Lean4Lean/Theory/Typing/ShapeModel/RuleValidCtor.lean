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

/-- A telescope shape ending in a sort that approximates a telescope ending in a sort has the
same number of binders. -/
theorem Interp.nestPi_sort_len {ps : List (TShape × TShape)} {Ds : List VExpr}
    (H : Interp env ρ (nestPi ps (TShape.sort r)) (Ds.foldr .forallE (.sort l))) :
    ps.length = Ds.length := by
  induction ps generalizing ρ Ds with
  | nil =>
    cases Ds with
    | nil => rfl
    | cons D Ds => exact (Interp.sort_not_forallE H).elim
  | cons p ps ih =>
    cases Ds with
    | nil => exact absurd H.le_sort TShape.forallE_not_le_sort
    | cons D Ds => simp [ih (Interp.pi_inv H).2]

/-- A family with a semantic header of `n` binders is applied to `n` arguments in a well-typed
application of sort type. -/
theorem famSem_args_length (hcl : ConstClosed env) (hsem : FamSem env I l n)
    (W : Valuation.Fits env Γ₀ Γ ρ)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const I ls) args) (.sort v)) : args.length = n := by
  have hTy' : StrongSound env Γ (VExpr.mkApps (.const I ls) args.reverse.reverse) (.sort v) := by
    rwa [List.reverse_reverse]
  obtain ⟨ci, u, hci, hls, -⟩ := Spine.constInfo hTy'
  obtain ⟨ciI, Dsf, hsc, hDsf, hfamT⟩ := hsem
  cases hci.symm.trans hsc
  obtain ⟨qs, -, hq2, -, hq4⟩ := Spine.typed W hTy' hci
    (xs := args.reverse.map fun _ => TShape.bot)
    (List.forall₂_of_getElem (by simp) fun i _ _ => by simp only [List.getElem_map]; exact .bot)
    (R := TShape.sort v.eval) Interp.sort'
  have hq4' := (hfamT ls hls _).1 ((Interp.closed_iff (hcl hci).instL).1 hq4)
  rw [VExpr.instL_foldr_forallE] at hq4'
  have hlq := Interp.nestPi_sort_len hq4'
  have h2 := hq2.length_eq
  simp only [List.length_reverse, List.length_map] at hlq h2
  omega

/-! ### Realization of rigid family applications -/

/-- A rigid family applied to arguments and typed at a sort is approximated by a rigid shape with
prescribed (approximating) arguments and constructor table; the sort of the application is the
family's sort at the levels. -/
theorem Rigid.realize (hcl : ConstClosed env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (hnc : SemSig.ctor I = none) (hnr : ∀ r, SemSig.rules r → r.head ≠ .const I)
    (hl : SemSig.famLevel I = some l) (hsem : FamSem env I l n)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const I ls) args) (.sort v))
    {as : List (WShape N)} (hargs : List.Forall₂ (fun x A => Interp env ρ x.T A) as args)
    {cts : List (Name × WShape N)} (hnames : cts.map (·.1) = SemSig.famCtors I)
    (hent : ∀ p ∈ cts, CtorEntry env (Interp env) ls (as.map (·.T)) p)
    (hcts : WShape.CtsTypes cts) :
    (l.inst ls).eval = v.eval ∧
      Interp env ρ (WShape.rigid I (ls.map (·.eval)) as cts).T (VExpr.mkApps (.const I ls) args) := by
  have hn := famSem_args_length hcl hsem W hTy
  subst hn
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
    (hl : SemSig.famLevel I = some l) (hsem : FamSem env I l n)
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
  obtain ⟨hlev, hRI⟩ := Rigid.realize hcl W' hnc hnr hl hsem hB (as := asI)
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

/-! ### Alignment of constructor applications -/

theorem StrongSound.mkApps_head : ∀ {bs : List VExpr} {g : VExpr} {T},
    StrongSound env Γ (VExpr.mkApps g bs) T → ∃ T', StrongSound env Γ g T'
  | [], _, T, h => ⟨T, h⟩
  | b :: bs, g, T, h => by
    obtain ⟨T', h'⟩ := StrongSound.mkApps_head (bs := bs) (g := .app g b) h
    obtain ⟨_, hcore, -⟩ := h'
    obtain ⟨A, B, hf, -, -⟩ := hcore.app_inv
    exact ⟨_, hf⟩

theorem StrongSound.mkApps_prefix {f : VExpr} {as bs : List VExpr} {T}
    (h : StrongSound env Γ (VExpr.mkApps f (as ++ bs)) T) :
    ∃ T', StrongSound env Γ (VExpr.mkApps f as) T' := by
  have : VExpr.mkApps f (as ++ bs) = VExpr.mkApps (VExpr.mkApps f as) bs := by
    simp [VExpr.mkApps, List.foldl_append]
  rw [this] at h
  exact StrongSound.mkApps_head h

theorem piBot_type : TShape.piBot.HasType TShape.type := by
  refine TShape.HasType.sort_r.2 (.forallE (WShape.HasTypePi.def.2 ⟨?_, fun y z hm => ?_⟩))
  · exact WShape.HasDom.bot (.bot' .sort_type)
  · simp [WShapeFun.bot, ShapeFun.bot, WShapeFun.mem_def] at hm
    have : z = WShape.bot := WShape.ext hm.2
    subst this; exact .bot' .sort_type

/-- A Pi shape does not approximate a constant heading no rule applied to arguments. -/
theorem Interp.forallE_not_headless (hr : ∀ r, SemSig.rules r → r.head ≠ .const s)
    {b : WShape n} {f : WShapeFun n}
    (H : Interp env ρ (WShape.forallE b f).T (VExpr.mkApps (.const s ls) args)) : False := by
  rcases Interp.headless_inv hr H with h | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
  · exact TShape.forallE_not_le_bot h
  · exact TShape.forallE_not_le_lam' h
  · exact TShape.forallE_not_le_ctor' h
  · exact TShape.forallE_not_le_rigid h

theorem Interp.nestPi_bots {Ds : List VExpr} {R : TShape} {body : VExpr}
    (hR : ∀ ρ', Interp env ρ' R body) :
    Interp env ρ (nestPi (List.replicate Ds.length (TShape.bot, TShape.bot)) R)
      (Ds.foldr .forallE body) := by
  induction Ds generalizing ρ with
  | nil => exact hR ρ
  | cons D Ds ih => exact Interp.pi_intro .bot TShape.HasType.bot_bot ih

/-- A constructor (whose type is a telescope ending in an application of a constant heading no
rule) is not applied to more arguments than its telescope. -/
theorem ctor_not_over (W : Valuation.Fits env Γ₀ Γ ρ) (hcv : env.constants c = some cv)
    {doms argsI : List VExpr}
    (hct : cv.type = VExpr.wrapForalls doms (VExpr.mkApps (.const I (VLevel.params cv.uvars)) argsI))
    (hnr : ∀ r, SemSig.rules r → r.head ≠ .const I)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const c ls) args) A)
    (hlen : doms.length < args.length) : False := by
  have hsplit : args = args.take doms.length ++ (args[doms.length] :: args.drop (doms.length + 1)) := by
    simp
  rw [hsplit, ← List.singleton_append, ← List.append_assoc] at hTy
  obtain ⟨T', hT'⟩ := StrongSound.mkApps_prefix hTy
  rw [VExpr.mkApps_append_singleton] at hT'
  obtain ⟨_, hcore, -⟩ := hT'
  obtain ⟨A', B', hf, -, -⟩ := hcore.app_inv
  have hf' : StrongSound env Γ (VExpr.mkApps (.const c ls) (args.take doms.length).reverse.reverse)
      (.forallE A' B') := by rwa [List.reverse_reverse]
  obtain ⟨ci, u, hci, hlsl, -⟩ := Spine.constInfo hf'
  cases hci.symm.trans hcv
  obtain ⟨qs, -, hq2, -, hq4⟩ := Spine.typed W hf' hcv
    (xs := (args.take doms.length).reverse.map fun _ => TShape.bot)
    (List.forall₂_of_getElem (by simp) fun i _ _ => by simp only [List.getElem_map]; exact .bot)
    (R := TShape.piBot) Interp.piBot
  have hctl : cv.type.instL ls = (doms.map (·.instL ls)).foldr .forallE
      (VExpr.mkApps (.const I ls) (argsI.map (·.instL ls))) := by
    rw [hct]
    show VExpr.instL ls (doms.foldr .forallE _) = _
    rw [VExpr.instL_foldr_forallE, VExpr.instL_mkApps]
    simp only [VExpr.instL, VLevel.inst_map_id hlsl]
  rw [hctl] at hq4
  have hl : (doms.map (·.instL ls)).length = qs.reverse.length := by
    rw [List.length_map, List.length_reverse, hq2.length_eq]; simp; omega
  obtain ⟨-, hP⟩ := Interp.nest_inv hl hq4
  exact Interp.forallE_not_headless hnr hP

/-- A constructor is not applied to fewer arguments than its telescope at the major position of a
head whose type gives the major a domain that is an application of a constant heading no rule. -/
theorem ctor_not_under {h : Head} (W : Valuation.Fits env Γ₀ Γ ρ)
    (hTh : HeadType env h ls Th)
    {doms₀ rest argsF : List VExpr} {Tb : VExpr}
    (hThs : Th = VExpr.wrapForalls (doms₀ ++ VExpr.mkApps (.const F lvF) argsF :: rest) Tb)
    (hlen0 : doms₀.length = pre.length) (hnrF : ∀ r, SemSig.rules r → r.head ≠ .const F)
    (hTy : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) (pre ++ [VExpr.mkApps (.const c lv) margs])) B)
    (hcv : env.constants c = some cv) {domsc : List VExpr} {bodyc : VExpr}
    (hct : cv.type = VExpr.wrapForalls domsc bodyc) (hlt : margs.length < domsc.length) : False := by
  rw [VExpr.mkApps_append_singleton] at hTy
  obtain ⟨_, hcore, -⟩ := hTy
  obtain ⟨A, Bf, hf, hM, -⟩ := hcore.app_inv
  have hM' : StrongSound env Γ (VExpr.mkApps (.const c lv) margs.reverse.reverse) A := by
    rwa [List.reverse_reverse]
  obtain ⟨ci, u, hci, hlsl, -⟩ := Spine.constInfo hM'
  cases hci.symm.trans hcv
  -- the domain of the major has a Pi approximation
  have hPA : Interp env ρ TShape.piBot A := by
    refine Spine.ofPi W hM' hcv (qs := List.replicate margs.length (TShape.bot, TShape.bot))
      (List.forall₂_of_getElem (by simp) fun i _ _ => by simp only [List.getElem_replicate]; exact .bot)
      ?_
    have hsplit : domsc = domsc.take margs.length ++ domsc.drop margs.length := by simp
    rw [hct]
    show Interp env ρ _ (VExpr.instL lv (domsc.foldr .forallE bodyc))
    rw [VExpr.instL_foldr_forallE, hsplit, List.map_append, List.foldr_append]
    have hd : domsc.drop margs.length = domsc[margs.length] :: domsc.drop (margs.length + 1) := by
      rw [List.drop_eq_getElem_cons (by omega)]
    rw [hd, List.map_cons, List.foldr_cons, List.reverse_replicate]
    have hlt' : ((domsc.take margs.length).map (·.instL lv)).length = margs.length := by
      simp; omega
    have := Interp.nestPi_bots (env := env) (ρ := ρ)
      (Ds := (domsc.take margs.length).map (·.instL lv)) (R := TShape.piBot)
      (body := .forallE (domsc[margs.length].instL lv)
        (((domsc.drop (margs.length + 1)).map (·.instL lv)).foldr .forallE (bodyc.instL lv)))
      fun _ => Interp.piBot
    rwa [hlt'] at this
  have hpi : Interp env ρ (TShape.pi TShape.piBot TShape.bot TShape.bot) (.forallE A Bf) :=
    Interp.pi_intro hPA (TShape.HasType.bot' piBot_type) .bot
  have hf' : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) pre.reverse.reverse) (.forallE A Bf) := by
    rwa [List.reverse_reverse]
  obtain ⟨qs, -, hq2, -, hq4⟩ := Spine.typed_head W hf' hTh
    (xs := pre.reverse.map fun _ => TShape.bot)
    (List.forall₂_of_getElem (by simp) fun i _ _ => by simp only [List.getElem_map]; exact .bot)
    (R := TShape.pi TShape.piBot TShape.bot TShape.bot) hpi
  rw [hThs] at hq4
  show False
  have h4 : Interp env ρ (nestPi qs.reverse (TShape.pi TShape.piBot TShape.bot TShape.bot))
      (doms₀.foldr .forallE (.forallE (VExpr.mkApps (.const F lvF) argsF) (rest.foldr .forallE Tb))) := by
    have := hq4
    simp only [VExpr.wrapForalls, List.foldr_append, List.foldr_cons] at this
    exact this
  obtain ⟨-, hP⟩ := Interp.nest_inv (by rw [List.length_reverse, hq2.length_eq]; simp [hlen0]) h4
  exact Interp.forallE_not_headless hnrF (Interp.pi_inv hP).1

end

end Lean4Lean.ShapeModel
