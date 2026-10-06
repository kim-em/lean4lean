import Lean4Lean.Theory.Typing.ShapeModel.Sound.Ctor

/-!
# Soundness of the shape model: typing of projections

An approximation of `proj s i e` is a field of a constructor shape approximating `e`; that
shape is below one typed at an approximation of the structure applied to parameters, i.e. at a
rigid shape whose constructor entry is below the constructor type instantiated at the
parameters, and the fields are typed along that entry. Walking the projection's field type
(`VProjectionInfo.fieldType`) along the entry shows that the `i`-th field is typed at an
approximation of the field type (`Proj.typed`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-- A non-bottom shape typed at a shape below a rigid shape is a constructor shape whose fields
fit a telescope below an entry of the rigid shape's constructor table (at a common depth). -/
theorem WShape.typed_le_rigid {m a : WShape n} {l : List (WShape K)} {t : List (Name × WShape K)}
    (h1 : m.HasType a) (h2 : a.T ≤ (WShape.rigid s lvls l t).T) (h3 : ¬m.T ≤ .bot) :
    ∃ M, n ≤ M + 1 ∧ K ≤ M ∧ ∃ c₀, ∃ fs₀ : List (WShape M), ∃ wf, ∃ T₀ : WShape M, ∃ T₁,
      m.lift (M+1) = WShape.ctor c₀ fs₀ wf ∧ SemSig.famProp s lvls = false ∧
      WShape.Fits fs₀ T₀ ∧ T₀.T ≤ T₁.T ∧ (c₀, T₁) ∈ t := by
  obtain ⟨M, hn, hK⟩ : ∃ M, n ≤ M + 1 ∧ K ≤ M := ⟨max n K, by omega, Nat.le_max_right ..⟩
  have h1' := (WShape.HasType.lift hn).2 h1
  have h2' := (TShape.LE.def (m := M + 1) hn (Nat.succ_le_succ hK)).1 h2
  simp only [WShape.T] at h2'
  rw [WShape.lift_rigid hK] at h2'
  rcases WShape.le_rigid.1 h2' with e | ⟨l', t', e, -, ht⟩
  · rw [e] at h1'
    have := WShape.HasType.bot_r h1'
    exact absurd ((TShape.LE.def (m := M+1) hn (Nat.zero_le _)).2
      (by rw [this]; simp [TShape.bot])) h3
  rw [e] at h1'
  obtain ⟨-, hb | ⟨c₀, fs₀, wf, T₀, e', hp, hc, hfit⟩⟩ := WShape.HasType.rigid_inv h1'
  · exact absurd ((TShape.LE.def (m := M+1) hn (Nat.zero_le _)).2
      (by rw [hb]; simp [TShape.bot])) h3
  obtain ⟨T₁', hc', hle⟩ := ctorTy?_rel ht hc
  rw [ctorTy?_ctsMap] at hc'
  obtain ⟨T₁, hc₁, rfl⟩ := Option.map_eq_some_iff.1 hc'
  exact ⟨M, hn, hK, c₀, fs₀, wf, T₀, T₁, e', hp, hfit,
    hle.T.trans (TShape.lift_eqv (a := T₁.T) hK).1, ctorTy?_mem hc₁⟩

/-- Applying an approximation of a Pi type to an approximation of an argument approximates the
instantiated codomain. -/
theorem Interp.piApp {T x : TShape} (H : Interp env ρ T (.forallE D B))
    (hx : Interp env ρ x X) : Interp env ρ (T.piApp x) (B.inst X) := by
  have hk := Nat.max_le.1 (Nat.le_refl (max (T.1 - 1) x.1))
  have H' := H.lift (n := max (T.1 - 1) x.1 + 1) (by omega)
  have hx' := hx.lift hk.2
  show Interp env ρ (WShape.T ((T.2.lift _).piApp (x.2.lift _))) _
  generalize T.2.lift (max (T.1 - 1) x.1 + 1) = T' at H' ⊢
  cases T' using WShape.casesOn' with
  | forallE b f => exact H'.forallE_inv.2 hx'
  | _ => rw [WShape.piApp_of_ne (by intro _ _ h; cases congrArg (·.1) h)]; exact .bot

theorem Interp.instParams {T : TShape} (H : Interp env ρ T E)
    (hxs : List.Forall₂ (fun x P => Interp env ρ x P) xs Ps)
    (he : VProjectionInfo.instantiateProjectionParameters E Ps = some E') :
    Interp env ρ (xs.foldl TShape.piApp T) E' := by
  induction hxs generalizing T E with
  | nil => cases E <;> cases he <;> exact H
  | cons hx _ ih =>
    cases E with
    | forallE D B => exact ih (H.piApp hx) he
    | _ => cases he

/-- Walking the fields of a projection type along a telescope that the fields fit. -/
theorem Interp.instFields {s : Name} {e : VExpr} {i : Nat} {fs : List (WShape K)} :
    ∀ fuel current (T₀ : WShape K) E D, Interp env ρ T₀.T E →
      WShape.Fits (fs.drop current) T₀ →
      (∀ j (hj : j < fs.length), current ≤ j → Interp env ρ fs[j].T (.proj s j e)) →
      VProjectionInfo.instantiateProjectionFields s e i current fuel E = some D →
      (hi : i < fs.length) → current ≤ i →
      ∃ a, Interp env ρ a D ∧ fs[i].T.HasType a
  | 0, _, _, _, _, _, _, _, he, _, _ => by cases he
  | fuel+1, current, T₀, E, D, H, hfit, hfs, he, hi, hci => by
    cases E with
    | forallE Dom B =>
      have hcur : current < fs.length := Nat.lt_of_le_of_lt hci hi
      rw [List.drop_eq_getElem_cons hcur] at hfit
      cases K with
      | zero => exact absurd hfit WShape.Fits.cons_zero
      | succ K =>
      obtain ⟨a, b, rfl, hfa, hfit'⟩ := WShape.Fits.cons_inv hfit
      simp only [VProjectionInfo.instantiateProjectionFields] at he
      split at he
      · cases he; rename_i heq; subst heq
        refine ⟨(a.lift (K+1)).T, ?_, hfa.T⟩
        exact (H.forallE_inv.1).lift (Nat.le_succ K)
      · have H' := H.lift (n := K + 2) (Nat.le_succ (K + 1))
        simp only [WShape.lift_forallE (Nat.le_succ K)] at H'
        have := H'.forallE_inv.2 (hfs current hcur (Nat.le_refl _))
        exact Interp.instFields fuel (current + 1) _ _ _ this hfit'
          (fun j hj h => hfs j hj (Nat.le_of_succ_le h)) he hi
          (Nat.lt_of_le_of_ne hci (Ne.symm ‹_›))
    | _ => cases he

/-- A shape typed at a shape below a lambda table is bottom. -/
theorem WShape.typed_le_lam' {m a : WShape n} {g : WShapeFun k} (h1 : m.HasType a)
    (h2 : a.T ≤ (WShape.lam' g).T) : m.T ≤ .bot := by
  obtain ⟨P, hn, hk⟩ : ∃ P, n ≤ P + 1 ∧ k ≤ P := ⟨max n k, by omega, Nat.le_max_right ..⟩
  have h1' := (WShape.HasType.lift hn).2 h1
  have h2' := (TShape.LE.def (m := P + 1) hn (Nat.succ_le_succ hk)).1 h2
  simp only [WShape.T] at h2'
  rw [WShape.lift_lam' hk] at h2'
  obtain ⟨f', e⟩ := WShape.LE.le_lam' h2'
  rw [e] at h1'
  suffices m.lift (P+1) = .bot from
    (TShape.LE.def (m := P+1) hn (Nat.zero_le _)).2 (by rw [this]; simp [TShape.bot])
  unfold WShape.lam' at h1'; split at h1'
  · apply WShape.ext
    have := Shape.HasType.unfold (show Shape.HasType (m.lift (P+1)).1 (.lam f'.1) from h1')
    generalize (m.lift (P+1)).1 = x at this
    cases this; rfl
  · exact WShape.HasType.bot_r h1'

/-- A constructor shape below another: same constructor, fields below. -/
theorem TShape.ctor'_le_ctor {fs : List (WShape n)} {fs₀ : List (WShape M)} {wf}
    (h : (WShape.ctor' c fs).T ≤ (WShape.ctor c₀ fs₀ wf).T) (hi : i < fs.length)
    (hfi : ¬fs[i].T ≤ .bot) :
    c = c₀ ∧ fs.length = fs₀.length ∧ ∀ j (h : j < fs.length) (h' : j < fs₀.length),
      fs[j].T ≤ fs₀[j].T := by
  obtain ⟨P, hn, hM⟩ : ∃ P, n ≤ P ∧ M ≤ P := ⟨max n M, Nat.le_max_left .., Nat.le_max_right ..⟩
  have h' := (TShape.LE.def (m := P + 1) (Nat.succ_le_succ hn) (Nat.succ_le_succ hM)).1 h
  simp only [WShape.T] at h'
  rw [WShape.lift_ctor' hn, WShape.lift_ctor hM] at h'
  obtain ⟨l', h'', e, hl⟩ := WShape.ctor'_le.1 h' fun _ => ⟨_, List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩,
    fun hb => hfi ((TShape.LE.def (m := P) hn (Nat.zero_le _)).2 (by
      have : (fs[i].lift P).1 ≤ Shape.bot := hb
      simp only [TShape.bot, WShape.lift_bot]; exact this))⟩
  obtain ⟨rfl, rfl⟩ := WShape.ctor.inj.1 e.symm
  refine ⟨rfl, by simpa using hl.length_eq, fun j h1 h2 => ?_⟩
  have := forall₂_getElem hl (by simpa using h1)
  simp only [List.getElem_map] at this
  exact (TShape.LE.def hn hM).2 this

theorem WShape.ctor'_le_bot_field {fs : List (WShape n)} (h : (WShape.ctor' c fs).T ≤ .bot)
    (hi : i < fs.length) : fs[i].T ≤ .bot := by
  unfold WShape.ctor' at h; split at h
  · have := TShape.le_bot.1 h; cases congrArg (·.1) this
  · rename_i hn
    refine Classical.byContradiction fun hb => hn fun _ => ⟨_, List.getElem_mem hi, fun hb' => hb ?_⟩
    exact TShape.le_bot.2 (WShape.le_bot.1 hb')

/-- The typing of projections. -/
theorem Proj.typed (hcl : ConstClosed env) (hF : SemSig.StructFacts env s info)
    (hfield : info.fieldType s levels params i e₀ = some fieldType)
    (hlevels : levels.length = info.uvars) (hparams : params.length = info.nparams)
    (hmaj : ∀ {m}, Interp env ρ m e →
      InterpTyped env ρ m e (VExpr.mkApps (.const s levels) (params ++ idx)))
    (hsrc : ∀ {m}, Interp env ρ m e → Interp env ρ m e₀)
    (H : Interp env ρ m (.proj s i e)) : InterpTyped env ρ m (.proj s i e) fieldType := by
  by_cases hm : m ≤ .bot; · exact .of_le_bot hm
  cases H with
  | bot => exact .bot
  | @proj n _ c _ _ _ _ fs h1 h2 hi h3 =>
  rw [hF.structCtor] at h1; cases h1
  have hfi : ¬fs[i].T ≤ .bot := fun h => hm (h3.trans h)
  obtain ⟨n', m₁, a, -, le1, hm₁, ha, hty⟩ := (hmaj h2).out
  have hnb : ¬m₁.T ≤ .bot := fun h => hfi (WShape.ctor'_le_bot_field (le1.trans h) hi)
  rcases Interp.fam_inv hF.famNotCtor hF.famNoRule ha with
    hb | ⟨_, g, hg⟩ | ⟨K, rargs, cts, hents, -, hle, hargs⟩
  · exact absurd (TShape.HasType.bot_r' hb hty.T) hnb
  · exact absurd (WShape.typed_le_lam' hty hg) hnb
  obtain ⟨M, hn, hK, c₀, fs₀, wf, T₀, T₁, he, -, hfit, hT01, hmem⟩ :=
    WShape.typed_le_rigid hty hle hnb
  have hm₁' : (WShape.ctor c₀ fs₀ wf).T ≤ m₁.T ∧ m₁.T ≤ (WShape.ctor c₀ fs₀ wf).T := by
    rw [← he]; exact ⟨(TShape.lift_eqv (a := m₁.T) hn).1, (TShape.lift_eqv (a := m₁.T) hn).2⟩
  obtain ⟨rfl, hlen, hfs⟩ := TShape.ctor'_le_ctor (le1.trans hm₁'.2) hi hfi
  have hint : Interp env ρ (WShape.ctor' info.ctorName fs₀).T e := by
    rw [← WShape.ctor_eq_ctor' (h := wf)]; exact hm₁.mono hm₁'.1
  have hi₀ : i < fs₀.length := hlen ▸ hi
  -- the constructor entry
  obtain ⟨ci, k, T', hci, hk, hT', hbound⟩ := hents _ hmem
  cases hci.symm.trans hF.ctorConst
  cases hk.symm.trans hF.ctor
  have hT'ρ := (Interp.closed_iff (ρ' := ρ) (hcl hF.ctorConst).instL).1 hT'
  -- the projection type
  unfold VProjectionInfo.fieldType at hfield
  rw [if_neg (by simp [hparams, hlevels])] at hfield
  cases htail : VProjectionInfo.instantiateProjectionParameters
      (info.ctorType.instL levels) params with
  | none => simp [htail] at hfield
  | some tail =>
  simp only [htail, Option.bind_eq_bind, Option.bind_some] at hfield
  have hlr : info.nparams ≤ (rargs.reverse.map (·.T)).length := by
    have := hargs.length_eq; simp only [List.length_reverse, List.length_append] at this
    simp only [List.length_map, List.length_reverse]; omega
  have hpar : List.Forall₂ (fun x P => Interp env ρ x P)
      ((rargs.reverse.map (·.T)).take info.nparams) params := by
    have := forall₂_take (List.forall₂_map_left_iff.2 hargs) info.nparams
    rwa [List.take_left' hparams] at this
  have hP := Interp.instParams hT'ρ hpar htail
  have hT₀ : Interp env ρ T₀.T tail := by
    refine hP.mono (hT01.trans (hbound.trans ?_))
    simp only [ctsBound, if_pos hlr]; exact .rfl
  obtain ⟨a', ha', hty'⟩ := Interp.instFields (fs := fs₀) (i + 1) 0 T₀ tail fieldType hT₀
    (by simpa using hfit) (fun j hj _ => .proj hF.structCtor (hsrc hint) hj .rfl) hfield hi₀
    (Nat.zero_le _)
  exact ⟨_, _, h3.trans (hfs i hi hi₀), .proj hF.structCtor hint hi₀ .rfl, ha', hty'⟩

end
