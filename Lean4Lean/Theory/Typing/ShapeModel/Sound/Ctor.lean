import Lean4Lean.Theory.Typing.ShapeModel.Sound.Spine

/-!
# Soundness of the shape model: structures

The facts about the environment that the soundness proof reads (`SemSig.EnvFactsIn`, with the
structure facts `SemSig.StructFacts` of `Sound/Basic.lean`), the realization of a structure
constructor applied to arguments as a constructor shape (`Ctor.realize`), and the typing of
projections (`Proj.typed`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

/-- The facts about the environment `env` that the soundness proof reads for derivations in an
environment `E ≤ env`, besides the validity of the computation rules (`ExtraValid`,
`ElimValidIn`). Constant types are closed in all of `env`; the eliminator types and the
structure facts are only asked for the eliminators and projections registered in `E`. -/
structure SemSig.EnvFactsIn [S : SemSig] (E env : VEnv) : Prop where
  /-- Constant types are closed. -/
  constClosed : ConstClosed env
  /-- The generic type of an eliminator of `E` is its type in the signature. -/
  elimType : ∀ {b schema owner T}, E.eliminators b schema →
    InductiveSignature.CaseSchema.genericType schema owner = some T → T.Closed →
    S.elimType b owner.val = some T
  /-- Structures registered in `E`. -/
  proj : ∀ {s info}, E.projections s info → S.StructFacts env s info

/-- The facts of `SemSig.EnvFactsIn` for every eliminator and projection of `env` itself. -/
abbrev SemSig.EnvFacts [SemSig] (env : VEnv) : Prop := SemSig.EnvFactsIn env env

theorem SemSig.EnvFactsIn.mono [SemSig] {E E' env : VEnv} (hle : E ≤ E')
    (h : SemSig.EnvFactsIn E' env) : SemSig.EnvFactsIn E env where
  constClosed := h.constClosed
  elimType hb := h.elimType (hle.eliminators hb)
  proj hp := h.proj (hle.projections hp)

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-! ### Auxiliary lemmas -/

theorem Valuation.pushes_length_add (ρ : Valuation) (xs : List TShape) (i : Nat) :
    (ρ.pushes xs) (xs.length + i) = ρ i := by
  induction xs generalizing ρ i with
  | nil => simp [Valuation.pushes]
  | cons x xs ih =>
    simp only [Valuation.pushes, List.length_cons]
    rw [show xs.length + 1 + i = xs.length + (i + 1) by omega]
    exact ih (ρ.push x) (i + 1)

theorem Valuation.pushes_getElem (ρ : Valuation) (xs : List TShape) (j : Nat) (hj : j < xs.length) :
    (ρ.pushes xs) (xs.length - 1 - j) = xs[j] := by
  induction xs generalizing ρ j with
  | nil => cases hj
  | cons x xs ih =>
    simp only [Valuation.pushes, List.length_cons]
    cases j with
    | zero => exact Valuation.pushes_length_add (ρ.push x) xs 0
    | succ j =>
      simp only [List.getElem_cons_succ]
      rw [show xs.length + 1 - 1 - (j + 1) = xs.length - 1 - j by omega]
      exact ih _ j (by simpa using hj)

theorem VExpr.instL_foldr_forallE (Ds : List VExpr) (b : VExpr) :
    (Ds.foldr .forallE b).instL ls = (Ds.map (·.instL ls)).foldr .forallE (b.instL ls) := by
  induction Ds with
  | nil => rfl
  | cons D Ds ih => simp [VExpr.instL, ih]

theorem nestPi_append {ps qs : List (TShape × TShape)} :
    nestPi (ps ++ qs) R = nestPi ps (nestPi qs R) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [nestPi, ih]

theorem TShape.sort_le_sort {a b : SLvl} (h : TShape.sort a ≤ TShape.sort b) : a = b := by
  have := (TShape.LE.def (m := 0) (Nat.le_refl _) (Nat.le_refl _)).1 h
  simp only [TShape.sort, WShape.lift_self] at this
  have := WShape.sort_le.1 this
  cases congrArg (·.1) this; rfl

/-- The record of the head constant of a spine. -/
theorem Spine.constInfo {rev : List VExpr} (hTy : StrongSound env Γ (VExpr.mkApps (.const c ls) rev.reverse) T) :
    ∃ ci u, env.constants c = some ci ∧ ls.length = ci.uvars ∧
      StrongSound env Γ (ci.type.instL ls) (.sort u) := by
  induction rev generalizing T with
  | nil =>
    obtain ⟨_, hcore, -⟩ := hTy
    obtain ⟨ci, u, h1, h2, h3, -⟩ := hcore.const_inv
    exact ⟨ci, u, h1, h2, h3⟩
  | cons a rev ih =>
    rw [List.reverse_cons, VExpr.mkApps_append_singleton] at hTy
    obtain ⟨_, hcore, -⟩ := hTy
    obtain ⟨_, _, hf, -⟩ := hcore.app_inv
    exact ih hf

/-- A valuation extended along a telescope whose keys are typed at approximations of its
domains fits the extended context. -/
theorem Tel.fits (W : Valuation.Fits env Γ₀ Γ ρ)
    (hTy : StrongSound env Γ (Ds.foldr .forallE body) (.sort u))
    (H1 : TelInterp env ρ Ds ps) (H2 : TelTyped ps) :
    ∃ Γ' v, Valuation.Fits env Γ₀ Γ' (ρ.pushes (ps.map (·.2))) ∧
      StrongSound env Γ' body (.sort v) := by
  induction H1 generalizing Γ u with
  | nil => exact ⟨_, _, W, hTy⟩
  | cons hd _ ih =>
    have ⟨hx, H2⟩ := List.forall_mem_cons.1 H2
    obtain ⟨u1, v1, hD, hB⟩ := hTy.forallE_inv
    exact ih (.cons W (InterpTyped.hsort (hD.sound W)) hd hx) hB H2

/-- The approximations of a rigid former applied to arguments. -/
theorem Interp.fam_inv (hnc : SemSig.ctor s = none) (hr : ∀ r, SemSig.rules r → r.head ≠ .const s)
    (H : Interp env ρ m (VExpr.mkApps (.const s ls) args)) :
    m ≤ .bot ∨ (∃ n, ∃ g : WShapeFun n, m ≤ (WShape.lam' g).T) ∨
    ∃ n, ∃ rargs : List (WShape n), ∃ cts : List (Name × WShape n),
      (∀ p ∈ cts, CtorEntry env (Interp env) ls (rargs.reverse.map (·.T)) p) ∧
      cts.map (·.1) = SemSig.famCtors s ∧
      m ≤ (WShape.rigid s (ls.map (·.eval)) rargs.reverse cts).T ∧
      List.Forall₂ (fun x A => Interp env ρ x.T A) rargs.reverse args := by
  rcases Interp.mkApps_const_inv hr H with h | ⟨n, rargs, y, hC, hy, hargs⟩
  · exact .inl h
  cases hC with
  | bot => exact .inl (hy.trans TShape.bot_eqv.1)
  | lam _ h2 => exact .inr (.inl ⟨_, _, hy.trans h2⟩)
  | ctor h1 h2 => cases h1; rw [hnc] at h2; cases h2
  | rigid h1 _ _ h4 h5 h6 => cases h1; exact .inr (.inr ⟨_, _, _, h5, h4, hy.trans h6, hargs⟩)
  | rule h1 h2 => cases hr _ h1 h2
  | ruleAB h1 h2 => cases hr _ h1 h2
  | ruleC h1 h2 => cases hr _ h1 h2

/-- A Pi shape does not approximate a rigid former applied to arguments. -/
theorem Interp.forallE_not_fam (hnc : SemSig.ctor s = none)
    (hr : ∀ r, SemSig.rules r → r.head ≠ .const s) {b : WShape n} {f : WShapeFun n}
    (H : Interp env ρ (WShape.forallE b f).T (VExpr.mkApps (.const s ls) args)) : False := by
  rcases Interp.fam_inv hnc hr H with h | ⟨_, _, h⟩ | ⟨_, _, _, -, -, h, -⟩
  · have := TShape.le_bot.1 h; cases congrArg (·.1) this
  · exact TShape.forallE_not_le_lam' h
  · exact TShape.forallE_not_le_rigid h

/-- The keys of a telescope shape fit (as constructor fields) the telescope itself. -/
theorem WShape.fits_nestPi {ps : List (TShape × TShape)} (H : TelTyped ps)
    (hN : (nestPi ps R).1 ≤ N) :
    WShape.Fits (ps.map fun p => p.2.2.lift N) ((nestPi ps R).2.lift N) := by
  induction ps generalizing N with
  | nil => exact .nil
  | cons p ps ih =>
    obtain ⟨d, x⟩ := p
    have ⟨hx, H⟩ := List.forall_mem_cons.1 H
    obtain ⟨k, h1, h2, h3, e⟩ := TShape.pi_def (d := d) (x := x) (R := nestPi ps R)
    simp only [nestPi] at hN ⊢; rw [e] at hN ⊢
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    have hk : k ≤ N := Nat.le_of_succ_le_succ hN
    simp only [List.map_cons]
    have l1 := WShape.lift_lift (s := d.2) (n₂ := k) (n₃ := N) (.inl h1)
    have l2 := WShape.lift_lift (s := d.2) (n₂ := N) (n₃ := N+1) (.inl (Nat.le_trans h1 hk))
    have l3 := WShape.lift_lift (s := x.2) (n₂ := k) (n₃ := N) (.inl h2)
    have l4 := WShape.lift_lift (s := x.2) (n₂ := N) (n₃ := N+1) (.inl (Nat.le_trans h2 hk))
    have l5 := WShape.lift_lift (s := (nestPi ps R).2) (n₂ := k) (n₃ := N) (.inl h3)
    have l6 := WShape.lift_lift (s := (nestPi ps R).2) (n₂ := N) (n₃ := N+1)
      (.inl (Nat.le_trans h3 hk))
    rw [WShape.lift_forallE hk, WShapeFun.lift_single hk, WShape.Fits.forallE_iff,
      WShapeFun.lift_single (Nat.le_succ N)]
    simp only [l1, l2, l3, l4, l5, l6, Nat.succ_eq_add_one]
    rw [WShapeFun.single_app, if_pos WShape.LE.rfl]
    exact ⟨(TShape.HasType.def (Nat.le_trans h2 (Nat.le_succ_of_le hk))
      (Nat.le_trans h1 (Nat.le_succ_of_le hk))).1 hx, ih H (Nat.le_trans h3 (Nat.le_succ_of_le hk))⟩

theorem SemSig.famProp_eval {l : VLevel} (h : SemSig.famLevel s = some l) (ls : List VLevel) :
    SemSig.famProp s (ls.map (·.eval)) = decide (SLvl.IsZero (l.inst ls).eval) := by
  simp only [SemSig.famProp, h]
  congr 2; funext ns
  simp only [VLevel.eval_inst, List.map_map]; rfl

theorem TShape.pi_depth {d x R : TShape} :
    d.1 < (TShape.pi d x R).1 ∧ x.1 < (TShape.pi d x R).1 ∧ R.1 < (TShape.pi d x R).1 := by
  obtain ⟨k, h1, h2, h3, e⟩ := TShape.pi_def (d := d) (x := x) (R := R)
  rw [e]; exact ⟨Nat.lt_succ_of_le h1, Nat.lt_succ_of_le h2, Nat.lt_succ_of_le h3⟩

theorem nestPi_key_le {ps : List (TShape × TShape)} (h : p ∈ ps) :
    p.2.1 ≤ (nestPi ps R).1 ∧ p.1.1 ≤ (nestPi ps R).1 := by
  induction ps with
  | nil => cases h
  | cons q ps ih =>
    have := TShape.pi_depth (d := q.1) (x := q.2) (R := nestPi ps R)
    simp only [nestPi]
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨Nat.le_of_lt this.2.1, Nat.le_of_lt this.1⟩
    · have := ih h; omega

theorem nestPi_tail_le {ps qs : List (TShape × TShape)} :
    (nestPi qs R).1 ≤ (nestPi (ps ++ qs) R).1 := by
  induction ps with
  | nil => exact Nat.le_refl _
  | cons q ps ih =>
    have := TShape.pi_depth (d := q.1) (x := q.2) (R := nestPi (ps ++ qs) R)
    simp only [List.cons_append, nestPi]; omega

omit [SemSig] [SemSig.Coherent] in
theorem List.forall₂_of_getElem {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length →
      (∀ i (h : i < l.length) (h' : i < l'.length), R l[i] l'[i]) → List.Forall₂ R l l'
  | [], [], _, _ => .nil
  | a :: l, b :: l', hl, H =>
    .cons (H 0 (by simp) (by simp)) (List.forall₂_of_getElem (Nat.succ.inj hl)
      fun i h h' => H (i+1) (by simpa using h) (by simpa using h'))

/-! ### Realization of structure constructor applications -/

/-- A structure constructor applied to arguments approximated by `xs`: some rigid shape of the
structure at the constructor's levels approximates the type of the application, and if the
structure is not a proposition at these levels, a constructor shape whose fields are above the
field approximations approximates the application. -/
theorem Ctor.realize (hcl : ConstClosed env) (hF : SemSig.StructFacts env s info)
    (W : Valuation.Fits env Γ₀ Γ ρ)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const info.ctorName ls) args) T)
    (hlen : args.length = info.nparams + info.numFields)
    (hxs : List.Forall₂ (fun x A => Interp env ρ x A) xs args) :
    (∃ n, ∃ l : List (WShape n), ∃ t, Interp env ρ (WShape.rigid s (ls.map (·.eval)) l t).T T) ∧
    (SemSig.famProp s (ls.map (·.eval)) = false → ∃ n, ∃ fs : List (WShape n),
      Interp env ρ (WShape.ctor' info.ctorName fs).T
        (VExpr.mkApps (.const info.ctorName ls) args) ∧
      List.Forall₂ (fun x f => x ≤ f.T) (xs.drop info.nparams) fs) := by
  have hTy' : StrongSound env Γ (VExpr.mkApps (.const info.ctorName ls) args.reverse.reverse) T := by
    rwa [List.reverse_reverse]
  obtain ⟨ci, u, hci, hlsl, hTyT⟩ := Spine.constInfo hTy'
  cases hci.symm.trans hF.ctorConst
  obtain ⟨Ds, idx, hDs, hidx, hct⟩ := hF.ctorType
  -- the constructor type at the levels
  let pbv : List VExpr :=
    (List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j))
  let idxl := idx.map (·.instL ls)
  let Dsl := Ds.map (·.instL ls)
  let bodyl := VExpr.mkApps (.const s ls) (pbv ++ idxl)
  have hctl : info.ctorType.instL ls = Dsl.foldr .forallE bodyl := by
    rw [hct, VExpr.instL_foldr_forallE, VExpr.instL_mkApps]
    simp only [VExpr.instL, VLevel.inst_map_id hlsl, List.map_append, List.map_map, bodyl, pbv,
      idxl, Dsl, Function.comp_def]
  -- phase 1: typed keys
  obtain ⟨qs, hq1, hq2, hq3, hq4⟩ := Spine.typed W hTy' hci
    (List.Forall₂.reverse.2 hxs) (R := TShape.bot) .bot
  let ps := qs.reverse
  let keys := ps.map (·.2)
  have hps1 : List.Forall₂ (fun x p => x ≤ p.2) xs ps := by
    have := List.Forall₂.reverse.2 hq1; rwa [List.reverse_reverse] at this
  have hps2 : List.Forall₂ (fun p A => Interp env ρ p.2 A) ps args := by
    have := List.Forall₂.reverse.2 hq2; rwa [List.reverse_reverse] at this
  have hps3 : TelTyped ps := fun p hp => hq3 p (List.mem_reverse.1 hp)
  have hlps : ps.length = info.nparams + info.numFields := hps2.length_eq.trans hlen
  rw [hctl] at hq4 hTyT
  obtain ⟨htel, -⟩ := Interp.nest_inv (by rw [List.length_map, hDs, ← hlps]) hq4
  obtain ⟨Γ', v, W', hB⟩ := Tel.fits W hTyT htel hps3
  let ρ' := ρ.pushes keys
  have hkeys : keys.length = info.nparams + info.numFields := by simp [keys, hlps]
  -- approximations of the arguments of the structure in the constructor's result type
  have hpbv : ∀ (ys : List TShape), List.Forall₂ (fun y x => y ≤ x) ys (keys.take info.nparams) →
      List.Forall₂ (fun x A => Interp env ρ' x A) ys pbv := by
    intro ys hys
    have hl : ys.length = info.nparams := by
      rw [hys.length_eq, List.length_take, hkeys]; omega
    refine List.forall₂_of_getElem (by simp [pbv, hl]) fun i h h' => ?_
    have hi : i < info.nparams := by simpa [pbv] using h'
    simp only [pbv, List.getElem_map, List.getElem_range]
    refine .bvar ((forall₂_getElem hys h).trans ?_)
    rw [show info.nparams + info.numFields - 1 - i = keys.length - 1 - i by rw [hkeys]]
    have := Valuation.pushes_getElem ρ keys i (by omega)
    simp only [ρ', this, List.getElem_take]; exact .rfl
  have hbots : List.Forall₂ (fun x A => Interp env ρ' x A)
      (List.replicate info.nindices TShape.bot) idxl :=
    List.forall₂_of_getElem (by simp [idxl, hidx]) fun _ _ _ => by simp; exact .bot
  have hpbvl : pbv.length = info.nparams := by simp [pbv]
  have hidxl : idxl.length = info.nindices := by simp [idxl, hidx]
  -- the sort of the structure at the levels is the sort of the constructor's result type
  obtain ⟨cis, Dsf, hsc, -, hDsf, hfamT⟩ := hF.famTypeSem
  have hcis := hcl hsc
  have hBr : StrongSound env Γ' (VExpr.mkApps (.const s ls) (pbv ++ idxl).reverse.reverse)
      (.sort v) := by rwa [List.reverse_reverse]
  let xsI := keys.take info.nparams ++ List.replicate info.nindices TShape.bot
  have hxsI : List.Forall₂ (fun x A => Interp env ρ' x A) xsI (pbv ++ idxl) :=
    (List.Forall₂.append_of_left (by simp [hpbvl, hkeys])).2
      ⟨hpbv _ (List.Forall₂.rfl fun _ _ => .rfl), hbots⟩
  obtain ⟨qsI, -, hqI2, hqI3, hqI4⟩ := Spine.typed W' hBr hsc
    (List.Forall₂.reverse.2 hxsI) (R := TShape.bot) .bot
  have hstl : VExpr.instL ls (Dsf.foldr .forallE (.sort info.resultLevel)) =
      (Dsf.map (·.instL ls)).foldr .forallE (.sort (info.resultLevel.inst ls)) := by
    rw [VExpr.instL_foldr_forallE]; rfl
  -- move to the semantic telescope of the structure's type (at the base valuation)
  have hqI4' := (hfamT ls hlsl _).1 ((Interp.closed_iff hcis.instL).1 hqI4)
  simp only [hstl] at hqI4'
  obtain ⟨htelI, -⟩ := Interp.nest_inv (by
    rw [List.length_map, List.length_reverse, hDsf, hqI2.length_eq, List.length_reverse,
      List.length_append, hpbvl, hidxl]) hqI4'
  have hsortI := Interp.nest_intro htelI (fun p hp => hqI3 p (List.mem_reverse.1 hp))
    (R := TShape.sort (info.resultLevel.inst ls).eval) (ρ := .nil) Interp.sort'
  rw [← hstl] at hsortI
  have hsortI := (Interp.closed_iff (ρ' := ρ') hcis.instL).1 ((hfamT ls hlsl _).2 hsortI)
  have hlev : (info.resultLevel.inst ls).eval = v.eval :=
    TShape.sort_le_sort (Spine.ofPi W' hBr hsc hqI2 hsortI).le_sort
  -- the rigid shape of the structure, with the constructor entry built from the keys
  let N := (nestPi ps TShape.bot).1
  let psP := ps.take info.nparams
  let psF := ps.drop info.nparams
  have hpsPF : ps = psP ++ psF := (List.take_append_drop ..).symm
  have hkeyN : ∀ p ∈ ps, p.2.1 ≤ N := fun p hp => (nestPi_key_le hp).1
  have hFN : (nestPi psF TShape.bot).1 ≤ N := by
    show _ ≤ (nestPi ps TShape.bot).1
    rw [hpsPF]; exact nestPi_tail_le
  let TelF : WShape N := (nestPi psF TShape.bot).2.lift N
  let cts : List (Name × WShape N) := [(info.ctorName, TelF)]
  let argsI : List (WShape N) :=
    psP.map (fun p => p.2.2.lift N) ++ List.replicate info.nindices WShape.bot
  let Rfinal : WShape (N+1) := WShape.rigid s (ls.map (·.eval)) argsI cts
  have hcts : WShape.CtsTypes cts := by
    intro p hp; simp only [cts, List.mem_singleton] at hp; subst hp
    have := TShape.nestPi_type (R := TShape.bot) (ps := psF)
      (fun p hp => hps3 p (List.mem_of_mem_drop hp)) (TShape.HasType.bot' TShape.HasType.sort)
    have := (TShape.HasType.def hFN (Nat.zero_le _)).1 this
    simpa [TShape.type, TShape.sort, WShape.lift_sort] using this
  have hmtyI : Rfinal.T.HasType (TShape.sort v.eval) := by
    refine TShape.HasType.rigid (fun hz => ?_) hcts
    show SemSig.famProp s (ls.map (·.eval)) = true
    rw [SemSig.famProp_eval hF.famLevel, hlev]; exact decide_eq_true hz
  have hle : TelF.T ≤ ctsBound (nestPi ps TShape.bot) (argsI.reverse.reverse.map (·.T))
      info.nparams := by
    have hpl : psP.length = info.nparams := by simp [psP, hlps]
    simp only [ctsBound, List.reverse_reverse, argsI, List.map_append, List.length_append,
      List.length_map, hpl]
    rw [if_pos (Nat.le_add_right _ _), List.take_left' (by simp [hpl])]
    refine (TShape.lift_eqv hFN).1.trans ?_
    rw [hpsPF, nestPi_append]
    refine TShape.le_foldl_piApp_nestPi (List.forall₂_map_right_iff.2 ?_)
    refine List.forall₂_map_right_iff.2 (List.Forall₂.rfl fun p hp => ?_)
    exact (TShape.lift_eqv (hkeyN p (List.mem_of_mem_take hp))).2
  have hCI : Const env (Interp env) (.const s) ls argsI.reverse Rfinal.T := by
    refine Const.rigid (cts := cts) rfl hF.famNotCtor hF.famNoRule (by simp [cts, hF.famCtors]) ?_ ?_
    · intro p hp; simp only [cts, List.mem_singleton] at hp; subst hp
      exact ⟨_, _, _, hF.ctorConst, hF.ctor,
        (Interp.closed_iff (hcl hF.ctorConst).instL).1 (hctl ▸ hq4), hle⟩
    · simp only [List.reverse_reverse]; exact TShape.LE.rfl
  have hargsI : List.Forall₂ (fun x A => Interp env ρ' x.T A) argsI.reverse
      (pbv ++ idxl).reverse := by
    refine List.Forall₂.reverse.2 ((List.Forall₂.append_of_left (by simp [psP, hlps, hpbvl])).2
      ⟨?_, ?_⟩)
    · have := hpbv (psP.map fun p => (p.2.2.lift N).T) ?_
      · exact List.forall₂_map_left_iff.1 (by simpa [List.map_map, Function.comp_def] using this)
      · simp only [keys, psP, List.map_take]
        refine forall₂_take (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)) _
        refine List.Forall₂.rfl fun p hp => ?_
        exact (TShape.lift_eqv (hkeyN p hp)).1
    · refine List.forall₂_of_getElem (by simp [idxl, hidx]) fun _ _ _ => ?_
      simp only [List.getElem_replicate]; exact .bot
  have hRI : Interp env ρ' Rfinal.T bodyl := by
    have := Spine.realize hcl W' hmtyI Interp.sort' hBr hargsI hCI
    rwa [List.reverse_reverse] at this
  have hRT : Interp env ρ Rfinal.T T :=
    Spine.ofPi W hTy' hci hq2 (hctl ▸ Interp.nest_intro htel hps3 hRI)
  refine ⟨⟨_, _, _, hRT⟩, fun hfp => ?_⟩
  -- the constructor shape
  let keysN : List (WShape N) := ps.map fun p => p.2.2.lift N
  let fs : List (WShape N) := psF.map fun p => p.2.2.lift N
  have hmty : (WShape.ctor' info.ctorName fs).T.HasType Rfinal.T :=
    TShape.HasType.ctor' hcts hfp (by simp [cts, ctorTy?]; rfl)
      (WShape.fits_nestPi (fun p hp => hps3 p (List.mem_of_mem_drop hp)) hFN)
      (by
        show _ = SemSig.nfields _
        simp [SemSig.nfields, hF.ctor, fs, psF, hlps])
  have hC : Const env (Interp env) (.const info.ctorName) ls keysN.reverse
      (WShape.ctor' info.ctorName fs).T := by
    refine Const.ctor rfl hF.ctor (by simp [keysN, hlps]) ?_
    simp only [List.reverse_reverse, keysN, fs, psF, List.map_drop]; exact TShape.LE.rfl
  have hargs : List.Forall₂ (fun x A => Interp env ρ x.T A) keysN.reverse args.reverse := by
    refine List.Forall₂.reverse.2 (List.forall₂_map_left_iff.2 ?_)
    exact (List.Forall₂.and_mem hps2).imp fun p A ⟨h, hp, _⟩ => h.lift (hkeyN p hp)
  have := Spine.realize hcl W hmty hRT hTy' hargs hC
  rw [List.reverse_reverse] at this
  refine ⟨_, fs, this, List.forall₂_map_right_iff.2 ?_⟩
  exact ((forall₂_drop hps1 info.nparams).and_mem).imp fun x p ⟨h, _, hp⟩ =>
    h.trans (TShape.lift_eqv (hkeyN p (List.mem_of_mem_drop hp))).2

end
