import Lean4Lean.Theory.Typing.ShapeModel.Sound.Proj

/-!
# Soundness of the shape model: the structure rules

Pointwise soundness of the projection computation rule (`projIota`), structure eta
(`structEta`) and the unit-like rule (`unitLike`) under a valuation fitting the context.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-- The approximations of a constructor applied to arguments. -/
theorem Interp.ctor_inv (hc : SemSig.ctor c = some ci)
    (H : Interp env ρ m (VExpr.mkApps (.const c ls) args)) :
    m ≤ .bot ∨ (∃ n, ∃ g : WShapeFun n, m ≤ (WShape.lam' g).T) ∨
    ∃ n, ∃ rargs : List (WShape n), rargs.length = ci.nparams + ci.nfields ∧
      m ≤ (WShape.ctor' c (rargs.reverse.drop ci.nparams)).T ∧
      List.Forall₂ (fun x A => Interp env ρ x.T A) rargs.reverse args := by
  rcases Interp.mkApps_const_inv (fun r h1 h2 => SemSig.Coherent.ctor_no_rule hc h1 h2) H with
    h | ⟨n, rargs, y, hC, hy, hargs⟩
  · exact .inl h
  cases hC with
  | bot => exact .inl (hy.trans TShape.bot_eqv.1)
  | lam _ h2 => exact .inr (.inl ⟨_, _, hy.trans h2⟩)
  | ctor h1 h2 h3 h4 =>
    cases h1; cases hc.symm.trans h2; exact .inr (.inr ⟨_, _, h3, hy.trans h4, hargs⟩)
  | rigid h1 h2 => cases h1; rw [hc] at h2; cases h2
  | rule h1 h2 => cases SemSig.Coherent.ctor_no_rule hc h1 h2
  | ruleAB h1 h2 => cases SemSig.Coherent.ctor_no_rule hc h1 h2
  | ruleC h1 h2 => cases SemSig.Coherent.ctor_no_rule hc h1 h2

theorem SemSig.StructFacts.ctorType_instL (hF : SemSig.StructFacts env s info)
    (hls : ls.length = info.uvars) :
    ∃ Dsl : List VExpr, ∃ idxl : List VExpr, Dsl.length = info.nparams + info.numFields ∧
      idxl.length = info.nindices ∧
      info.ctorType.instL ls = Dsl.foldr .forallE (VExpr.mkApps (.const s ls)
        ((List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j)) ++
          idxl)) := by
  obtain ⟨Ds, idx, hDs, hidx, hct⟩ := hF.ctorType
  refine ⟨Ds.map (·.instL ls), idx.map (·.instL ls), by simp [hDs], by simp [hidx], ?_⟩
  rw [hct, VExpr.instL_foldr_forallE, VExpr.instL_mkApps]
  simp only [VExpr.instL, VLevel.inst_map_id hls, List.map_append, List.map_map,
    Function.comp_def]

/-- The Pi shape with bottom domain and bottom codomain table. -/
def TShape.piBot : TShape := WShape.T (n := 1) (.forallE .bot .bot)

theorem Interp.piBot : Interp env ρ TShape.piBot (.forallE A B) :=
  .forallE' .bot .bot (WShape.HasDom.bot (.bot' .sort_type))
    fun x _ => by rw [WShapeFun.bot_app]; exact .bot

/-- A structure constructor application typed at the structure has exactly the constructor's
number of arguments. -/
theorem Ctor.length (hF : SemSig.StructFacts env s info) (W : Valuation.Fits env Γ₀ Γ ρ)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const info.ctorName ls) args)
      (VExpr.mkApps (.const s lsT) argsT)) :
    args.length = info.nparams + info.numFields := by
  have hTy' : StrongSound env Γ (VExpr.mkApps (.const info.ctorName ls) args.reverse.reverse)
      (VExpr.mkApps (.const s lsT) argsT) := by rwa [List.reverse_reverse]
  obtain ⟨ci, u, hci, hlsl, -⟩ := Spine.constInfo hTy'
  cases hci.symm.trans hF.ctorConst
  obtain ⟨Dsl, idxl, hDsl, -, hctl⟩ := hF.ctorType_instL hlsl
  have hxs : List.Forall₂ (fun x A => Interp env ρ x A)
      (List.replicate args.length TShape.bot).reverse args.reverse :=
    List.Forall₂.reverse.2 (List.forall₂_of_getElem (by simp) fun _ _ _ => by simp; exact .bot)
  obtain ⟨qs, -, hq2, hq3, hq4⟩ := Spine.typed W hTy' hci hxs (R := TShape.bot) .bot
  have hlq : qs.length = args.length := by simp [hq2.length_eq]
  have hq3' : TelTyped qs.reverse := fun p hp => hq3 p (List.mem_reverse.1 hp)
  rw [hctl] at hq4
  rcases Nat.lt_trichotomy args.length (info.nparams + info.numFields) with h | h | h
  · exfalso
    rw [← List.take_append_drop args.length Dsl, List.foldr_append] at hq4
    obtain ⟨htel, -⟩ := Interp.nest_inv (by simp [hlq]; omega) hq4
    have hne : Dsl.drop args.length ≠ [] := by simp [hDsl]; omega
    obtain ⟨D, rest, hD⟩ := List.exists_cons_of_ne_nil hne
    have := Interp.nest_intro (body := (Dsl.drop args.length).foldr .forallE
      (VExpr.mkApps (.const s ls) ((List.range info.nparams).map
        (fun j => .bvar (info.nparams + info.numFields - 1 - j)) ++ idxl))) htel hq3'
      (R := TShape.piBot) (by rw [hD]; exact Interp.piBot)
    rw [← List.foldr_append, List.take_append_drop, ← hctl] at this
    exact Interp.forallE_not_fam hF.famNotCtor hF.famNoRule (Spine.ofPi W hTy' hci hq2 this)
  · exact h
  · exfalso
    have e : qs.reverse = qs.reverse.take Dsl.length ++ qs.reverse.drop Dsl.length :=
      (List.take_append_drop ..).symm
    rw [e, nestPi_append] at hq4
    obtain ⟨-, h2⟩ := Interp.nest_inv (by simp [hlq]; omega) hq4
    have hne : qs.reverse.drop Dsl.length ≠ [] := by simp [hDsl, hlq]; omega
    obtain ⟨p, rest, hp⟩ := List.exists_cons_of_ne_nil hne
    rw [hp] at h2
    obtain ⟨k, -, -, -, e'⟩ := TShape.pi_def (d := p.1) (x := p.2) (R := nestPi rest TShape.bot)
    simp only [nestPi] at h2; rw [e'] at h2
    exact Interp.forallE_not_fam hF.famNotCtor hF.famNoRule h2

/-- A non-bottom typed approximation of an element of a structure type is (up to lifting) a
constructor shape with the declared number of fields. -/
theorem Struct.typedCtor (hF : SemSig.StructFacts env s info)
    (H : InterpTyped env ρ m e (VExpr.mkApps (.const s levels) args)) (hm : ¬m ≤ .bot) :
    ∃ M, ∃ fs₀ : List (WShape M), ∃ wf, ∃ m₁ : TShape, m ≤ m₁ ∧ Interp env ρ m₁ e ∧
      m₁ ≤ (WShape.ctor info.ctorName fs₀ wf).T ∧ (WShape.ctor info.ctorName fs₀ wf).T ≤ m₁ ∧
      fs₀.length = info.numFields ∧ SemSig.famProp s (levels.map (·.eval)) = false := by
  obtain ⟨n', m₁, a, -, le1, hm₁, ha, hty⟩ := H.out
  have hnb : ¬m₁.T ≤ .bot := fun h => hm (le1.trans h)
  rcases Interp.fam_inv hF.famNotCtor hF.famNoRule ha with
    hb | ⟨_, g, hg⟩ | ⟨K, rargs, cts, -, hcts, hle, -⟩
  · exact absurd (TShape.HasType.bot_r' hb hty.T) hnb
  · exact absurd (WShape.typed_le_lam' hty hg) hnb
  obtain ⟨M, hn, -, c₀, fs₀, wf, T₀, T₁, he, hfp, -, hlen, -, hmem⟩ :=
    WShape.typed_le_rigid hty hle hnb
  have hc₀ : c₀ = info.ctorName := by
    have : c₀ ∈ cts.map (·.1) := List.mem_map.2 ⟨_, hmem, rfl⟩
    rw [hcts, hF.famCtors] at this; simpa using this
  subst hc₀
  refine ⟨M, fs₀, wf, m₁.T, le1, hm₁, ?_, ?_, ?_, hfp⟩
  · rw [← he]; exact (TShape.lift_eqv (a := m₁.T) hn).2
  · rw [← he]; exact (TShape.lift_eqv (a := m₁.T) hn).1
  · rw [hlen]; simp [SemSig.nfields, hF.ctor]

/-- A constructor shape of a structure approximating an element of the structure type has the
declared number of fields. -/
theorem Struct.ctor_len (hF : SemSig.StructFacts env s info)
    (hTe : ∀ {m}, Interp env ρ m e → InterpTyped env ρ m e (VExpr.mkApps (.const s levels) args))
    {fs : List (WShape n)} (H : Interp env ρ (WShape.ctor' info.ctorName fs).T e)
    (hi : i < fs.length) (hfi : ¬fs[i].T ≤ .bot) : fs.length = info.numFields := by
  have hnb : ¬(WShape.ctor' info.ctorName fs).T ≤ .bot :=
    fun h => hfi (WShape.ctor'_le_bot_field h hi)
  obtain ⟨M, fs₀, wf, m₁, le1, -, hle, -, hlen, -⟩ := Struct.typedCtor hF (hTe H) hnb
  exact (TShape.ctor'_le_ctor (le1.trans hle) hi hfi).2.1.trans hlen

theorem WShape.ctor'_replicate_bot (hs : SemSig.isStruct c = true) :
    WShape.ctor' c (List.replicate k (WShape.bot : WShape n)) = .bot := by
  unfold WShape.ctor'; rw [dif_neg]; intro h
  obtain ⟨x, hx, hn⟩ := h hs
  rw [List.eq_of_mem_replicate hx] at hn; exact hn Shape.LE.rfl

/-- Constructor fields approximating the projections of `e` are the fields of a constructor
shape approximating `e` (structure eta, from left to right). -/
theorem Struct.etaJoin (hF : SemSig.StructFacts env s info) (h0 : info.nindices = 0)
    (hTe : ∀ {m}, Interp env ρ m e → InterpTyped env ρ m e (VExpr.mkApps (.const s levels) args))
    {F : List (WShape n)} (hlen : F.length = info.numFields)
    (hFj : ∀ j (h : j < F.length), Interp env ρ F[j].T (.proj s j e)) :
    Interp env ρ (WShape.ctor' info.ctorName F).T e := by
  have key : ∀ k ≤ F.length, ∃ D, ∃ E : List (WShape D), E.length = F.length ∧
      Interp env ρ (WShape.ctor' info.ctorName E).T e ∧
      ∀ j (_ : j < k) (h1 : j < F.length) (h2 : j < E.length), F[j].T ≤ E[j].T := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨0, List.replicate F.length WShape.bot, by simp, ?_,
        fun j h => absurd h (Nat.not_lt_zero _)⟩
      rw [WShape.ctor'_replicate_bot (hF.isStruct h0)]; exact .bot
    | succ k ih =>
      obtain ⟨D, E, hEl, hE, hEF⟩ := ih (Nat.le_of_succ_le hk)
      have hk' : k < F.length := hk
      by_cases hb : F[k].T ≤ .bot
      · refine ⟨D, E, hEl, hE, fun j h h1 h2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
        · exact hEF j h h1 h2
        · exact hb.trans TShape.bot_le
      have hk_int := hFj k hk'
      generalize hx : F[k].T = x at hk_int hb
      cases hk_int with
      | bot => exact absurd TShape.bot_eqv.1 hb
      | @proj nk _ _ _ _ _ _ fsk h1 h2 hi h3 =>
        rw [hF.structCtor] at h1; cases h1
        have hfk : ¬fsk[k].T ≤ .bot := fun h => hb (h3.trans h)
        have hlk := Struct.ctor_len hF hTe h2 hi hfk
        obtain ⟨D', hD, hnk⟩ : ∃ D', D ≤ D' ∧ nk ≤ D' :=
          ⟨max D nk, Nat.le_max_left .., Nat.le_max_right ..⟩
        have hE' := hE.lift (n := D'+1) (Nat.succ_le_succ hD)
        have hG' := h2.lift (n := D'+1) (Nat.succ_le_succ hnk)
        simp only [WShape.T] at hE' hG'
        rw [WShape.lift_ctor' hD] at hE'; rw [WShape.lift_ctor' hnk] at hG'
        have hc := WShape.ctor'_compat_fields (by simp [hEl, hlk, hlen])
          (WShape.Compat.T_iff.2 (hE'.compat hG'))
        have hJ := hE'.join' hG'
        rw [WShape.T_join, WShape.ctor'_join hc] at hJ
        refine ⟨D', _, by simp [hEl, hlk, hlen], hJ, fun j h h1 h2' => ?_⟩
        have ⟨l1, l2⟩ := WShape.le_zipWith_join hc
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
        · have := forall₂_getElem l1 (i := j) (by simp; omega)
          simp only [List.getElem_map] at this
          exact (hEF j h h1 (by omega)).trans
            ((TShape.lift_eqv (a := E[j].T) hD).2.trans this.T)
        · have := forall₂_getElem l2 (i := j) (by simp; omega)
          simp only [List.getElem_map] at this
          rw [hx]
          exact h3.trans ((TShape.lift_eqv (a := fsk[j].T) hnk).2.trans this.T)
  obtain ⟨D, E, hEl, hE, hEF⟩ := key F.length (Nat.le_refl _)
  refine hE.mono ?_
  obtain ⟨P, hn, hD⟩ : ∃ P, n ≤ P ∧ D ≤ P := ⟨max n D, Nat.le_max_left .., Nat.le_max_right ..⟩
  rw [TShape.LE.def (m := P+1) (Nat.succ_le_succ hn) (Nat.succ_le_succ hD)]
  simp only [WShape.T]
  rw [WShape.lift_ctor' hn, WShape.lift_ctor' hD]
  apply WShape.ctor'_le_ctor'
  refine List.forall₂_of_getElem (by simp [hEl]) fun j h1 h2 => ?_
  simp only [List.getElem_map]
  exact (TShape.LE.def hn hD).1 (hEF j (by simpa using h1) (by simpa using h1) (by simpa using h2))

/-- Constructor shapes are monotone in their fields (across depths). -/
theorem TShape.ctor'_mono {fs : List (WShape n)} {fs' : List (WShape n')}
    (hl : fs.length = fs'.length)
    (h : ∀ j (h1 : j < fs.length) (h2 : j < fs'.length), fs[j].T ≤ fs'[j].T) :
    (WShape.ctor' c fs).T ≤ (WShape.ctor' c fs').T := by
  obtain ⟨P, hn, hD⟩ : ∃ P, n ≤ P ∧ n' ≤ P := ⟨max n n', Nat.le_max_left .., Nat.le_max_right ..⟩
  rw [TShape.LE.def (m := P+1) (Nat.succ_le_succ hn) (Nat.succ_le_succ hD)]
  simp only [WShape.T]
  rw [WShape.lift_ctor' hn, WShape.lift_ctor' hD]
  apply WShape.ctor'_le_ctor'
  refine List.forall₂_of_getElem (by simp [hl]) fun j h1 h2 => ?_
  simp only [List.getElem_map]
  exact (TShape.LE.def hn hD).1 (h j (by simpa using h1) (by simpa using h2))

theorem TShape.ctor'_le_ctor'_inv {fs : List (WShape n)} {fs₀ : List (WShape M)}
    (h : (WShape.ctor' c fs).T ≤ (WShape.ctor' c₀ fs₀).T) (hi : i < fs.length)
    (hfi : ¬fs[i].T ≤ .bot) :
    c = c₀ ∧ fs.length = fs₀.length ∧ ∀ j (h : j < fs.length) (h' : j < fs₀.length),
      fs[j].T ≤ fs₀[j].T := by
  by_cases hz : IsStruct c₀ → WShape.ListNonZero fs₀
  · rw [← WShape.ctor_eq_ctor' (h := hz)] at h
    exact TShape.ctor'_le_ctor h hi hfi
  · refine absurd (WShape.ctor'_le_bot_field (h.trans ?_) hi) hfi
    rw [WShape.ctor', dif_neg hz]; exact TShape.bot_eqv.1

theorem TShape.ctor'_not_le_lam' {fs : List (WShape n)} {g : WShapeFun k}
    (hi : i < fs.length) (hfi : ¬fs[i].T ≤ .bot) :
    ¬(WShape.ctor' c fs).T ≤ (WShape.lam' g).T := by
  intro h
  by_cases hz : IsStruct c → WShape.ListNonZero fs
  · rw [← WShape.ctor_eq_ctor' (h := hz)] at h
    exact TShape.ctor_not_le_lam' h
  · refine hfi (WShape.ctor'_le_bot_field (c := c) ?_ hi)
    rw [WShape.ctor', dif_neg hz]; exact TShape.bot_eqv.1

/-- Proof irrelevance: approximations of proofs are bottom. -/
theorem InterpTyped.proofIrrel (H : InterpTyped env ρ m M A)
    (hA : ∀ {a}, Interp env ρ a A → InterpTyped env ρ a A (.sort l)) (hl : SLvl.IsZero l.eval) :
    m ≤ .bot := by
  obtain ⟨_, _, a1, -, a3, a4⟩ := H
  obtain ⟨_, _, b1, -, b3, b4⟩ := hA a3
  have b4' := TShape.HasType.mono_r b3.le_sort .sort b4
  exact a1.trans (b4'.proofIrrel hl (b4'.mono_r b1 a4))

theorem StrongSoundCore.proj_inv (H : StrongSoundCore env Γ (.proj s i e) T) :
    ∃ info levels params indexArgs fieldLevel, env.projections s info ∧
      StrongSound env Γ e (VExpr.mkApps (.const s levels) (params ++ indexArgs)) ∧
      StrongSound env Γ T (.sort fieldLevel) ∧
      ((info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) := by
  cases H with | proj h1 h2 h3 h4 => exact ⟨_, _, _, _, _, h1, h2, h3, h4⟩

theorem List.getElem_append_range_proj {params : List VExpr} {j : Nat}
    (hp : params.length = np) (h : j < nf)
    (h' : np + j < (params ++ (List.range nf).map fun index => VExpr.proj s index e).length) :
    (params ++ (List.range nf).map fun index => VExpr.proj s index e)[np + j] = .proj s j e := by
  subst hp; rw [List.getElem_append_right (by omega)]; simp

/-- Structure eta, pointwise. -/
theorem Struct.eta (hcl : ConstClosed env) (hF : SemSig.StructFacts env s info)
    (h0 : info.nindices = 0) (hparams : params.length = info.nparams)
    (W : Valuation.Fits env Γ₀ Γ ρ)
    (he : StrongSound env Γ e (VExpr.mkApps (.const s levels) params))
    (hl : StrongSound env Γ (VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj s index e))
      (VExpr.mkApps (.const s levels) params)) :
    Interp env ρ m (VExpr.mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj s index e)) ↔
      Interp env ρ m e := by
  have hTe : ∀ {m}, Interp env ρ m e →
      InterpTyped env ρ m e (VExpr.mkApps (.const s levels) params) := he.sound W
  constructor
  · intro H
    by_cases hm : m ≤ .bot; · exact .mono hm .bot
    obtain ⟨M, fs₀, wf, m₁, le1, hm₁, hle, hge, hlen, -⟩ := Struct.typedCtor hF (hl.sound W H) hm
    have hnb : ¬(WShape.ctor info.ctorName fs₀ wf).T ≤ .bot := fun h =>
      hm (le1.trans (hle.trans h))
    rcases Interp.ctor_inv hF.ctor hm₁ with h | ⟨_, g, hg⟩ | ⟨n, rargs, hrl, hrle, hargs⟩
    · exact absurd (hge.trans h) hnb
    · exact absurd (hge.trans hg) TShape.ctor_not_le_lam'
    refine (Struct.etaJoin hF h0 hTe (F := rargs.reverse.drop info.nparams)
      (by simp [hrl]) fun j hj => ?_).mono (le1.trans hrle)
    have hj' : j < info.numFields := by simp [hrl] at hj; omega
    have := forall₂_getElem hargs (i := info.nparams + j) (by simp [hrl]; omega)
    simp only [List.getElem_drop]
    rwa [List.getElem_append_range_proj hparams hj'] at this
  · intro H
    by_cases hm : m ≤ .bot; · exact .mono hm .bot
    obtain ⟨M, fs₀, wf, m₁, le1, hm₁, hle, hge, hlen, hfp⟩ := Struct.typedCtor hF (hTe H) hm
    have hint : Interp env ρ (WShape.ctor' info.ctorName fs₀).T e := by
      rw [← WShape.ctor_eq_ctor' (h := wf)]; exact hm₁.mono hge
    let xs := List.replicate info.nparams TShape.bot ++ fs₀.map (·.T)
    have hxs : List.Forall₂ (fun x A => Interp env ρ x A) xs
        (params ++ (List.range info.numFields).map fun index => .proj s index e) := by
      refine (List.Forall₂.append_of_left (by simp [hparams])).2 ⟨?_, ?_⟩
      · exact List.forall₂_of_getElem (by simp [hparams]) fun _ _ _ => by simp; exact .bot
      · refine List.forall₂_of_getElem (by simp [hlen]) fun j h1 h2 => ?_
        simp only [List.getElem_map, List.getElem_range]
        exact .proj hF.structCtor hint (by simpa using h1) .rfl
    obtain ⟨-, hreal⟩ := Ctor.realize hcl hF W hl (by simp [hparams]) hxs
    obtain ⟨n, fs, hint', hfs⟩ := hreal hfp
    have hd : xs.drop info.nparams = fs₀.map (·.T) := by
      simp [xs, List.drop_append_of_le_length]
    rw [hd] at hfs
    refine hint'.mono (le1.trans (hle.trans ?_))
    rw [WShape.ctor_eq_ctor']
    refine TShape.ctor'_mono (by simpa using hfs.length_eq) fun j h1 h2 => ?_
    have := forall₂_getElem hfs (i := j) (by simpa using h1)
    simpa using this

/-- The unit-like rule, pointwise: elements of a structure without fields have only bottom
approximations. -/
theorem Struct.unit (hF : SemSig.StructFacts env s info) (h0 : info.nindices = 0)
    (hnf : info.numFields = 0)
    (hTe : ∀ {m}, Interp env ρ m e → InterpTyped env ρ m e (VExpr.mkApps (.const s levels) args))
    (H : Interp env ρ m e) : m ≤ .bot := by
  refine Classical.byContradiction fun hm => ?_
  obtain ⟨M, fs₀, wf, -, -, -, -, -, hlen, -⟩ := Struct.typedCtor hF (hTe H) hm
  rw [hnf, List.length_eq_zero_iff] at hlen; subst hlen
  obtain ⟨_, h, _⟩ := wf (hF.isStruct h0); cases h

/-- The projection computation rule, pointwise. -/
theorem Struct.iota (hEF : SemSig.EnvFacts env) (hproj : env.projections s info)
    (W : Valuation.Fits env Γ₀ Γ ρ)
    (hL : StrongSound env Γ (.proj s i (VExpr.mkApps (.const info.ctorName ls) args)) A)
    (hf : StrongSound env Γ field A) (hfield : args[info.nparams + i]? = some field) :
    Interp env ρ m (.proj s i (VExpr.mkApps (.const info.ctorName ls) args)) ↔
      Interp env ρ m field := by
  have hF := hEF.proj hproj
  have hcl : ConstClosed env := fun h => hEF.constClosed h
  obtain ⟨hai, hfe⟩ := List.getElem?_eq_some_iff.1 hfield
  constructor
  · intro H
    by_cases hm : m ≤ .bot; · exact .mono hm .bot
    cases H with
    | bot => exact absurd TShape.bot_eqv.1 hm
    | @proj n _ c _ _ _ _ fs h1 h2 hi h3 =>
    rw [hF.structCtor] at h1; cases h1
    have hfi : ¬fs[i].T ≤ .bot := fun h => hm (h3.trans h)
    rcases Interp.ctor_inv hF.ctor h2 with h | ⟨_, g, hg⟩ | ⟨n', rargs, hrl, hle, hargs⟩
    · exact absurd (WShape.ctor'_le_bot_field h hi) hfi
    · exact absurd hg (TShape.ctor'_not_le_lam' hi hfi)
    obtain ⟨-, hlen, hpw⟩ := TShape.ctor'_le_ctor'_inv hle hi hfi
    have hi' : i < (rargs.reverse.drop info.nparams).length := hlen ▸ hi
    dsimp only at hrl hi'
    have := forall₂_getElem hargs (i := info.nparams + i) (by
      simp only [List.length_reverse, hrl]; simp only [List.length_drop, List.length_reverse] at hi'
      omega)
    simp only [hfe] at this
    refine this.mono (h3.trans ((hpw i hi hi').trans ?_))
    simp only [List.getElem_drop]; exact .rfl
  · intro H
    by_cases hm : m ≤ .bot; · exact .mono hm .bot
    obtain ⟨_, coreL, hA'⟩ := hL
    obtain ⟨info', levels', params', idx', fl, hproj', hM, hA'fl, hguard⟩ := coreL.proj_inv
    have hF' := hEF.proj hproj'
    have hcn : info'.ctorName = info.ctorName :=
      Option.some.inj (hF'.structCtor.symm.trans hF.structCtor)
    have hrl : info'.resultLevel = info.resultLevel :=
      Option.some.inj (hF'.famLevel.symm.trans hF.famLevel)
    have hlen := Ctor.length hF W hM
    have hinf : i < info.numFields := by omega
    let xs := (List.range args.length).map fun j =>
      if j = info.nparams + i then m else TShape.bot
    have hxs : List.Forall₂ (fun x A => Interp env ρ x A) xs args := by
      refine List.forall₂_of_getElem (by simp [xs]) fun j h1 h2 => ?_
      simp only [xs, List.getElem_map, List.getElem_range]
      split
      · rename_i hj; subst hj; rw [hfe]; exact H
      · exact .bot
    obtain ⟨⟨n, l, t, hRT⟩, hreal⟩ := Ctor.realize hcl hF W hM hlen hxs
    cases hfp : SemSig.famProp s (ls.map (·.eval)) with
    | false =>
      obtain ⟨n, fs, hint, hfs⟩ := hreal hfp
      have hfl : i < fs.length := by rw [← hfs.length_eq]; simp [xs]; omega
      refine .proj hF.structCtor hint hfl ?_
      have := forall₂_getElem hfs (i := i) (by simp [xs]; omega)
      simpa [xs] using this
    | true =>
      exfalso; apply hm
      rcases hguard with hnz | hz
      · have hlv : ls.map (·.eval) = levels'.map (·.eval) := by
          rcases Interp.fam_inv hF.famNotCtor hF.famNoRule hRT with
            h | ⟨_, g, hg⟩ | ⟨_, _, _, -, -, h, -⟩
          · have := TShape.le_bot.1 h; cases congrArg (·.1) this
          · exact absurd hg TShape.rigid_not_le_lam'
          · exact (TShape.LE.rigid_inv h).2
        rw [hlv, SemSig.famProp_eval hF.famLevel] at hfp
        rw [hrl] at hnz
        exact absurd (of_decide_eq_true hfp []) (hnz [])
      · refine InterpTyped.proofIrrel (hf.sound W H) (l := fl) (fun ha => ?_) ?_
        · have ⟨_, _, a1, a2, a3, a4⟩ := hA'fl.sound W ((hA' W).2 ha)
          exact ⟨_, _, a1, (hA' W).1 a2, a3, a4⟩
        · intro ns; have := congrFun (VLevel.equiv_def'.1 hz) ns; simpa [VLevel.eval] using this

end
