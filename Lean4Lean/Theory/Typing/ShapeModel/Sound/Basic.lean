import Lean4Lean.Theory.Typing.ShapeModel.Interp

/-!
# Soundness of the shape model: valuations fitting a context, and the structural cases

Port of `Valuation.Fits`, `InterpTyped`, `sound_bot`, `sound_app`, `sound_lam`, `sound_forallE`
from Mario Carneiro's prototype (`Lean4Lean/Experimental/ShapeLogRel.lean`) to the
interpretation of `Interp.lean`.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-- `Fits Γ₀ Γ ρ`: the valuation `ρ` assigns to each variable of `Γ` beyond the base context
`Γ₀` a shape typed at an approximation of its type (variables of `Γ₀` are bottom). -/
inductive Valuation.Fits (env : VEnv) [SemSig] : (Γ Δ : List VExpr) → Valuation → Prop
  | nil : Valuation.Fits env Γ Γ .nil
  | cons : Valuation.Fits env Γ Δ ρ →
    (∀ {a}, Interp env ρ a A → ∃ a', a ≤ a' ∧ Interp env ρ a' A ∧ a'.HasType .type) →
    Interp env ρ a A → x.HasType a →
    Valuation.Fits env Γ (A::Δ) (ρ.push x)

/-- `m` is below an approximation of `M` typed at an approximation of `A`. -/
def InterpTyped (env : VEnv) [SemSig] (ρ : Valuation) (m : TShape) (M A : VExpr) :=
  ∃ m' a, m ≤ m' ∧ Interp env ρ m' M ∧ Interp env ρ a A ∧ m'.HasType a

theorem TShape.HasType.toType {x : TShape} (H : x.HasType (.sort r)) : x.HasType .type := by
  have h := (TShape.HasType.def (Nat.le_refl x.1) (Nat.zero_le _)).1 H
  simp only [TShape.sort, WShape.lift_sort] at h
  refine (TShape.HasType.def (Nat.le_refl x.1) (Nat.zero_le _)).2 ?_
  simpa [TShape.type, TShape.sort, WShape.lift_sort] using h.toType

theorem WShape.HasType.sort_congr {r r' : SLvl} (h : r'.IsZero → r.IsZero) :
    ∀ {n} {x : WShape n}, x.HasType (.sort r) → x.HasType (.sort r') := by
  intro n; induction n with
  | zero => intro x H; cases H.unfold with
    | bot => exact .bot' .sort_type
    | sort h' => exact .sort (mt h h')
  | succ n ih => intro x H; cases H.unfold with
    | bot => exact .bot' .sort_type
    | sort h' => exact .sort (mt h h')
    | forallE hp =>
      have ⟨h1, h2⟩ := WShape.HasTypePi.iff'.1 hp
      exact .forallE (WShape.HasTypePi.iff'.2 ⟨h1, fun x => ih (h2 x)⟩)
    | rigid h1 h2 => exact .rigid (h1 ∘ h) h2

theorem TShape.HasType.sort_congr {r r' : SLvl} (h : r'.IsZero → r.IsZero) {x : TShape}
    (H : x.HasType (.sort r)) : x.HasType (.sort r') := by
  have h1 := (TShape.HasType.def (Nat.le_refl x.1) (Nat.zero_le _)).1 H
  simp only [TShape.sort, WShape.lift_sort] at h1
  refine (TShape.HasType.def (Nat.le_refl x.1) (Nat.zero_le _)).2 ?_
  simpa [TShape.sort, WShape.lift_sort] using h1.sort_congr h

theorem InterpTyped.bot : InterpTyped env ρ (WShape.T (n := n) .bot) M A := by
  refine ⟨WShape.T (n := n) .bot, WShape.T (n := n) .bot, .rfl, .bot, .bot, ?_⟩
  exact WShape.HasType.T_iff.2 <| .bot' <| .bot' .sort_type

theorem InterpTyped.of_le_bot (h : m ≤ .bot) : InterpTyped env ρ m M A :=
  TShape.le_bot'.1 h ▸ .bot

theorem InterpTyped.mk (le : m ≤ m') (h_m : Interp env ρ m' M) (h_a : Interp env ρ a A)
    (h_type : m'.HasType a) : InterpTyped env ρ m M A := ⟨_, _, le, h_m, h_a, h_type⟩

theorem InterpTyped.mono (le : m ≤ m') (H : InterpTyped env ρ m' M A) : InterpTyped env ρ m M A :=
  let ⟨_, _, a1, a2, a3, a4⟩ := H; ⟨_, _, le.trans a1, a2, a3, a4⟩

theorem InterpTyped.out (H : InterpTyped env ρ m M A) :
    ∃ n', ∃ m' : WShape n', ∃ a : WShape n', m.1 ≤ n' ∧ m ≤ m'.T ∧
      Interp env ρ m'.T M ∧ Interp env ρ a.T A ∧ m'.HasType a := by
  obtain ⟨m', a, hle, hm, ha, hty⟩ := H
  let k := max m.1 (max m'.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  refine ⟨k, m'.2.lift k, a.2.lift k, hk.1, ?_, hm.lift hk.2.1, ha.lift hk.2.2, ?_⟩
  · exact hle.trans (TShape.lift_eqv hk.2.1).2
  · exact (TShape.HasType.def hk.2.1 hk.2.2).1 hty

theorem InterpTyped.hsort' {ρ A U}
    (H : ∀ {a}, Interp env ρ a A → InterpTyped env ρ a A (.sort U))
    {a} (h : Interp env ρ a A) :
    ∃ a', a ≤ a' ∧ Interp env ρ a' A ∧ a'.HasType (.sort U.eval) :=
  have ⟨_, _, h1, h2, h3, h4⟩ := H h; ⟨_, h1, h2, .mono_r h3.le_sort .sort h4⟩

theorem InterpTyped.hsort {ρ A U}
    (H : ∀ {a}, Interp env ρ a A → InterpTyped env ρ a A (.sort U))
    {a} (h : Interp env ρ a A) : ∃ a', a ≤ a' ∧ Interp env ρ a' A ∧ a'.HasType .type :=
  have ⟨a', h1, h2, h3⟩ := hsort' H h; ⟨a', h1, h2, h3.toType⟩

theorem Interp.sound_bot :
    (Interp env ρ (WShape.T (n := n) .bot) M ↔ Interp env ρ (WShape.T (n := n) .bot) N) ∧
    (Interp env ρ (WShape.T (n := n) .bot) M → InterpTyped env ρ (WShape.T (n := n) .bot) M A) :=
  ⟨⟨fun _ => .bot, fun _ => .bot⟩, fun _ => .bot⟩

theorem Interp.sound_app
    (H1 : ∀ {m}, Interp env ρ m F → InterpTyped env ρ m F (.forallE A B))
    (H2 : ∀ {b}, Interp env ρ b (B.inst X) →
      ∃ b', b ≤ b' ∧ Interp env ρ b' (B.inst X) ∧ b'.HasType .type)
    (h1 : Interp env ρ m (F.app X)) : InterpTyped env ρ m (F.app X) (B.inst X) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => exact .bot | app h1 h2 h3
  rename_i nf f_shape a_sh
  have ⟨f_ts, s_ts, le_f, a2, a3, a4⟩ := H1 h1
  have hf : ¬f_ts ≤ .bot := fun h => by
    rw [show f_shape = .bot from TShape.le_bot.1 (le_f.trans h), WShape.bot_app] at h3
    exact hm (h3.trans TShape.bot_le')
  have hs : ¬s_ts ≤ .bot := fun h => hf (a4.bot_r' h)
  cases a3 with | bot => cases hs TShape.bot_le' | forallE b1 b2 b3 b4 b5
  rename_i npi b_pi b_pi' f_pi
  cases b5.le_forall with | bot b5 => cases hs b5 | @forallE m _ _ _ _ b5 b6
  obtain c1 | ⟨n₂, g_lam, rfl, c1⟩ := a4.ty_forallE_inv; · cases hf (c1 ▸ .rfl)
  let k := max (max n₂ m) (max npi nf)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have a3' := Interp.forallE b1 b2 b3 b4 (TShape.lift_eqv (Nat.succ_le_succ hk.2.1)).1
  rw [WShape.lift_forallE hk.2.1] at a3'
  have h_Binst := a3'.forallE_inv.2 (h2.lift hk.2.2)
  have ⟨a', le', g1, g2⟩ := H2 h_Binst
  have c1 := (TShape.HasTypeLam.def hk.1.1 hk.1.2).1 c1
  have c1_d := WShape.HasDom.iff.1 c1.2.1
  have c1_f := (WShape.HasTypeLam.iff.1 c1).2.2
  have ⟨_, e1, e2, e3⟩ := c1_d (a_sh.lift k)
  refine ⟨_, a', ?_, .app' (a2.lift (Nat.succ_le_succ hk.1.1)) (h2.lift hk.2.2), g1, ?_⟩
  · refine h3.trans <| TShape.app_mono ?_ (TShape.lift_eqv hk.2.2).2
    exact le_f.trans (TShape.lift_eqv (Nat.succ_le_succ hk.1.1)).2
  · have b6 := (TShapeFun.LE.def hk.1.2 hk.2.1).1 b6
    rw [WShape.lift_lam' hk.1.1, WShape.lam'_app]
    refine g2.mono_r ((WShapeFun.app_mono_l b6 _).trans (WShapeFun.app_mono_r e1) |>.T.trans le') ?_
    exact (WShape.HasTypeLam.iff.1 c1).2.2 _ e2 |>.mono_l (WShapeFun.app_mono_r e1) e3 |>.T

theorem Interp.sound_lam
    (H1 : ∀ {m}, Interp env ρ m A →
      ∃ a', m ≤ a' ∧ Interp env ρ a' A ∧ a'.HasType .type)
    (H2 : ∀ {a x}, Interp env ρ a A → x.HasType a →
      ∀ {e}, Interp env (ρ.push x) e F → InterpTyped env (ρ.push x) e F B)
    (h1 : Interp env ρ m (A.lam F)) : InterpTyped env ρ m (A.lam F) (A.forallE B) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @lam n _ _ _ _ a f h1 h2 h3 h4
  have ⟨a', a1, a2, a3⟩ := H1 h1
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ Interp env (ρ.push p.1.T) p.2.T F) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' b : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (a.lift k) ∧ WShape.HasDom b (a.lift k) ∧
        (∀ x, x.HasType (a.lift k) → Interp env (ρ.push x.T) (f'.app x).T F) ∧
        (∀ x, x.HasType (a.lift k) → Interp env (ρ.push x.T) (b.app x).T B) ∧
        (∀ x, x.HasType (a.lift k) → (f'.app x).HasType (b.app x)) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h2 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h3 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', b, hsingle, hd1, hd2, hi1, hi2, hi3⟩ := H _ (Nat.le_refl _)
    have h1' := h1.lift le
    refine ⟨_, _, ?_, .lam' h1' hd1 hi1, .forallE' h1' h1' hd2 hi2, ?_⟩
    · refine h4.trans <| (TShape.LE.lift_l (Nat.succ_le_succ le)).2 (WShape.lift_lam' le ▸ ?_)
      refine WShape.lam'_le_lam'.2 <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 (hsingle _ (WShapeFun.mem_elems.2 h₀))
    · exact WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff.2
        ⟨WShape.HasTypePi.iff.2 ⟨hd2, fun x h => (hi3 x h).isType⟩, hd1, hi3⟩
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    have ha : (a.lift k).HasType .type :=
      WShape.lift_type.symm ▸ (WShape.HasType.lift hk).2 h2.isType
    refine ⟨.bot, .bot, nofun, .bot ha, .bot ha, fun x h => ?_, fun x h => ?_, fun x h => ?_⟩
    · exact WShapeFun.bot_app ▸ .bot
    · exact WShapeFun.bot_app ▸ .bot
    · simp [WShapeFun.bot_app]; exact .bot' (.bot' .sort_type)
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h2 p.1
    have ⟨e', b', le_e, he', hb', heb'⟩ := H2 h1 (WShape.HasType.T hx') (h3 x' hx')
    let m' := max e'.1 b'.1; have ⟨lf, lb⟩ := Nat.max_le.1 (Nat.le_refl m')
    refine ⟨k₁.max m', Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk : n ≤ k := Nat.le_trans le1 le₁
    have le_ek := Nat.le_trans lf le₂; have le_bk := Nat.le_trans lb le₂
    have ⟨f₁, b₁, hsingle₁, hd1₁, hd2₁, hi1₁, hi2₁, hi3₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (e'.2.lift k)
    let sb := WShapeFun.single (x'.lift k) (b'.2.lift k)
    have hi1_any z : Interp env (ρ.push z.T) (f₁.app z).T F :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have hi2_any z : Interp env (ρ.push z.T) (b₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd2₁ z
      (hi2₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have he'_at_x' : Interp env (ρ.push (x'.lift k).T) (e'.2.lift k).T F :=
      (he'.lift le_ek).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hb'_at_x' : Interp env (ρ.push (x'.lift k).T) (b'.2.lift k).T B :=
      (hb'.lift le_bk).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = e'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have hcb : b₁.Compat sb := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sb_app : sb.app z = b'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sb_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi2_any z).compat (sb_app ▸ hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    have jb := WShapeFun.Join.mk hcb
    refine ⟨f₁.join sf, b₁.join sb, ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le_ek).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine hd2₁.join' ?_ jb (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine Interp.join (jb.app_l x).T (hi2_any x) (WShapeFun.single_app ▸ ?_); split
      · exact hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · have hT1 := hi3₁ x hx
      have hT2 : (sf.app x).HasType (sb.app x) := by
        rw [WShapeFun.single_app, WShapeFun.single_app]; split
        · exact (TShape.HasType.def le_ek le_bk).1 heb'
        · exact .bot' (.bot' .sort_type)
      have jb_x := jb.app_l x
      have := hT1.isType.join' jb_x hT2.isType
      exact (this.mono_r jb_x.le.1 hT1).join' (jf.app_l x) (this.mono_r jb_x.le.2 hT2)

theorem Interp.sound_forallE
    (H1 : ∀ {m}, Interp env ρ m A →
      ∃ a', m ≤ a' ∧ Interp env ρ a' A ∧ a'.HasType (.sort u.eval))
    (H2 : ∀ {a x}, Interp env ρ a A → x.HasType a →
      ∀ {e}, Interp env (ρ.push x) e B → InterpTyped env (ρ.push x) e B (.sort v))
    (h1 : Interp env ρ m (A.forallE B)) :
    InterpTyped env ρ m (A.forallE B) (.sort (.imax u v)) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @forallE n _ _ _ _ b₀ b f h1 h2 h3 h4 h5
  have ⟨a', a1, a2, a3⟩ := H1 h2
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ Interp env (ρ.push p.1.T) p.2.T B) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (b.lift k) ∧
        (∀ x, x.HasType (b.lift k) → Interp env (ρ.push x.T) (f'.app x).T B) ∧
        (∀ x, x.HasType (b.lift k) → (f'.app x).HasType (.sort v.eval)) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h3 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h4 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', hsingle, hd1, hi1, hi2⟩ := H _ (Nat.le_refl _)
    have hJ := WShape.Join.mk <| WShape.Compat.T_iff.2 <| h1.compat h2
    have ⟨b₂, c1, c2, c3⟩ := H1 (h1.join hJ.T h2)
    let k := max n' b₂.1; have ⟨le₂, le₁⟩ := Nat.max_le.1 (Nat.le_refl k)
    have b2' := (WShape.HasDom.lift le₂).2 hd1
    refine ⟨((b₂.2.lift k).forallE (f'.lift k)).T, _, h5.trans ?_, ?_, .sort .rfl, ?_⟩
    · rw [TShape.LE.lift_l (Nat.succ_le_succ (Nat.le_trans le le₂)),
        WShape.lift_forallE (Nat.le_trans le le₂)]
      refine WShape.forallE_le_forallE.2 ⟨?_, WShapeFun.lift_lift (.inl le) ▸ ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.1.T.trans c1)
      refine WShapeFun.lift_mono le₂ <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 <| hsingle _ (WShapeFun.mem_elems.2 h₀)
    · refine .forallE' (c2.lift le₁) ((h2.lift le).lift le₂) b2' fun x h => ?_
      have ⟨x', d1, dmem⟩ := (f'.lift k).app_eq x
      refine .mono (WShapeFun.app_of_mem dmem).2.T ?_
      obtain ⟨z₀, -, -, rfl, -⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1 z₀
      refine WShapeFun.lift_app le₂ ▸ .lift (m := (f'.app _).T) le₂ ?_
      refine hi1 _ z'ht |>.mono z'app.T |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
      exact z'le.T.trans <| (TShape.LE.lift_l le₂).2 d1
    · apply (TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _)).2
      simp only [WShape.lift_self, TShape.sort, WShape.lift_sort]
      have b2' := WShape.lift_lift (.inl le) ▸ b2'
      have := (TShape.HasType.def le₁ (Nat.zero_le k)).1 c3
      refine .forallE <| WShape.HasTypePi.iff.2 ⟨b2'.mono_r ?_ this, fun x hx => ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.2.T.trans c1)
      have ⟨x', _, dmem⟩ := (f'.lift k).app_eq x
      obtain ⟨x', y', e1, rfl, eq⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨e2, e3⟩ := WShapeFun.app_of_mem e1
      refine eq ▸ WShape.lift_sort.symm ▸ (WShape.HasType.lift le₂).2 (.mono_l e2 e3 ?_)
      have ⟨y, d1, d2, d3⟩ := WShape.HasDom.iff.1 hd1 x'
      refine (hi2 _ d2).mono_l (WShapeFun.app_mono_r d1) d3 |>.sort_congr fun hz ns => ?_
      have := hz ns; simp only [VLevel.eval, Lean.Nat.imax] at this ⊢
      split at this <;> [assumption; exact Nat.eq_zero_of_le_zero (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq this))]
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    refine ⟨.bot, nofun, .bot ?_, fun x h => WShapeFun.bot_app ▸ .bot, fun x h => ?_⟩
    · simpa [WShape.lift_sort] using (WShape.HasType.lift hk).2 h3.isType
    · simp [WShapeFun.bot_app]; exact .bot' .sort_type
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h3 p.1
    have ⟨f'x, _, le_e, he', hb', heb'⟩ := H2 h2 hx'.T (h4 x' hx')
    replace heb' : f'x.HasType (.sort v.eval) := .mono_r hb'.le_sort .sort heb'
    refine ⟨k₁.max f'x.1, Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk := Nat.le_trans le1 le₁
    have ⟨f₁, hsingle₁, hd1₁, hi1₁, hi2₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (f'x.2.lift k)
    have hi1_any z : Interp env (ρ.push z.T) (f₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T z'le⟩)
    have he'_at_x' : Interp env (ρ.push (x'.lift k).T) (f'x.2.lift k).T B :=
      (he'.lift le₂).mono_l <| Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = f'x.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    refine ⟨f₁.join sf, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le₂).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine (hi2₁ x hx).join' (jf.app_l x) (WShapeFun.single_app ▸ ?_); split
      · exact (TShape.HasType.def le₂ (Nat.zero_le k)).1 heb'
      · exact .bot' .sort_type

/-! ### Structure facts -/

/-- The facts linking a structure `s` with projection data `info` to the semantic signature and
to the environment `env`. -/
structure SemSig.StructFacts [S : SemSig] (env : VEnv) (s : Name) (info : VProjectionInfo) :
    Prop where
  /-- `proj s i` reads the fields of the structure constructor. -/
  structCtor : S.structCtor s = some info.ctorName
  /-- The structure constructor builds `s`, with the declared numbers of parameters and fields. -/
  ctor : S.ctor info.ctorName = some ⟨s, info.nparams, info.numFields⟩
  /-- The structure constructor is the only constructor of `s`. -/
  famCtors : S.famCtors s = [info.ctorName]
  /-- A structure without indices has eta (its constructor collapses). -/
  isStruct : info.nindices = 0 → S.isStruct info.ctorName = true
  /-- The structure constructor is declared with the type recorded in the projection data. -/
  ctorConst : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩
  /-- The constructor type is a telescope over the parameters and fields ending in `s` applied
  to the parameters (as bound variables) and to index expressions. -/
  ctorType : ∃ (Ds idx : List VExpr), Ds.length = info.nparams + info.numFields ∧ idx.length = info.nindices ∧
    info.ctorType = Ds.foldr .forallE (VExpr.mkApps (.const s (VLevel.params info.uvars))
      ((List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j)) ++
        idx))
  /-- `s` is not a constructor. -/
  famNotCtor : S.ctor s = none
  /-- `s` heads no computation rule. -/
  famNoRule : ∀ r, S.rules r → r.head ≠ .const s
  /-- The sort level of `s`. -/
  famLevel : S.famLevel s = some info.resultLevel
  /-- The type of `s` has, at every instance of its universe parameters, the approximations of
  a telescope over the parameters and indices ending in its sort. (A real environment only
  guarantees that the declared type is *definitionally* such a telescope, e.g.
  `def T : Type 1 := Type` followed by a structure `S : T`; this semantic form follows from such
  a derivation by soundness.) -/
  famTypeSem : ∃ ci, ∃ Ds : List VExpr, env.constants s = some ci ∧ ci.uvars = info.uvars ∧
    Ds.length = info.nparams + info.nindices ∧
    ∀ ls, ls.length = info.uvars → ∀ m, Interp env .nil m (ci.type.instL ls) ↔
      Interp env .nil m (VExpr.instL ls (Ds.foldr VExpr.forallE (VExpr.sort info.resultLevel)))

/-! ### Semantic judgments -/

variable (env) in
/-- `M` and `N` have the same approximations under every valuation fitting `Γ`. -/
def SoundEq (Γ : List VExpr) (M N : VExpr) : Prop :=
  ∀ {{Γ₀ ρ}}, Valuation.Fits env Γ₀ Γ ρ → ∀ {m}, Interp env ρ m M ↔ Interp env ρ m N

variable (env) in
/-- Every approximation of `M` under a valuation fitting `Γ` is below one typed at an
approximation of `A`. -/
def SoundTy (Γ : List VExpr) (M A : VExpr) : Prop :=
  ∀ {{Γ₀ ρ}}, Valuation.Fits env Γ₀ Γ ρ → ∀ {m}, Interp env ρ m M → InterpTyped env ρ m M A

variable (env) in
mutual
/-- The semantic record of a typing `Γ ⊢ M : A`: `M` is semantically typed at `A`, and it has
a structural record (`StrongSoundCore`) at a type with the same approximations as `A`. -/
inductive StrongSound : List VExpr → VExpr → VExpr → Prop where
  | mk : SoundTy env Γ M A → StrongSoundCore Γ M A' → SoundEq env Γ A' A → StrongSound Γ M A

/-- The structural part of a semantic typing record: for applications, constants, eliminators,
Pi types, lambdas and projections it records the semantic typing of the immediate subterms (for
an eliminator, its generic type), as used by the realization of constructor applications
(`Spine.lean`) and by the validity of computation rules (`RuleValid*.lean`, which inverts the
lambda telescopes of rules). The projection case records the
structure facts of the projected structure (rather than its registration in `env`), so that
soundness only needs these facts for the projections of the derivation environment. -/
inductive StrongSoundCore : List VExpr → VExpr → VExpr → Prop where
  | bvar : StrongSoundCore Γ (.bvar i) A
  | sort : StrongSoundCore Γ (.sort l) A
  | const : env.constants c = some ci → ls.length = ci.uvars →
    StrongSound Γ (ci.type.instL ls) (.sort u) →
    StrongSoundCore Γ (.const c ls) (ci.type.instL ls)
  | elim : SemSig.elimType b o = some T → T.Closed → StrongSound Γ (T.instL ls) (.sort u) →
    StrongSoundCore Γ (.elim b o ls) (T.instL ls)
  | app : StrongSound Γ f (.forallE A B) → StrongSound Γ a A →
    StrongSoundCore Γ (.app f a) (B.inst a)
  | proj : SemSig.StructFacts env s info →
    StrongSound Γ e (VExpr.mkApps (.const s levels) (params ++ indexArgs)) →
    StrongSound Γ fieldType (.sort fieldLevel) →
    ((info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero) →
    StrongSoundCore Γ (.proj s i e) fieldType
  | lam : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) → StrongSound (A::Γ) e B →
    StrongSoundCore Γ (.lam A e) (.forallE A B)
  | forallE : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.forallE A B) (.sort (.imax u v))
end

variable (env) in
/-- The semantic record of `Γ ⊢ M ≡ N : A`. -/
structure StrongSoundEq (Γ : List VExpr) (M N A : VExpr) : Prop where
  sound : SoundEq env Γ M N
  left : StrongSound env Γ M A
  right : StrongSound env Γ N A

protected theorem SoundEq.rfl : SoundEq env Γ M M := fun _ _ _ _ => .rfl
theorem SoundEq.symm : SoundEq env Γ M N → SoundEq env Γ N M := fun H _ _ W _ => (H W).symm
theorem SoundEq.trans (H1 : SoundEq env Γ M N) (H2 : SoundEq env Γ N P) : SoundEq env Γ M P :=
  fun _ _ W _ => (H1 W).trans (H2 W)

theorem StrongSound.sound : StrongSound env Γ M A → SoundTy env Γ M A
  | ⟨h, _, _⟩ => h

theorem StrongSoundEq.symm : StrongSoundEq env Γ M N A → StrongSoundEq env Γ N M A
  | ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩
theorem StrongSoundEq.rfl (H : StrongSound env Γ M A) : StrongSoundEq env Γ M M A :=
  ⟨.rfl, H, H⟩
theorem StrongSoundEq.trans :
    StrongSoundEq env Γ M N A → StrongSoundEq env Γ N P A → StrongSoundEq env Γ M P A
  | ⟨a1, a2, _⟩, ⟨b1, _, b3⟩ => ⟨a1.trans b1, a2, b3⟩

theorem SoundTy.defeq_l (H1 : SoundEq env Γ M N) (H : SoundTy env Γ M A) : SoundTy env Γ N A :=
  fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W ((H1 W).2 h); ⟨_, _, a1, (H1 W).1 a2, a3, a4⟩
theorem SoundTy.defeq_r (H1 : SoundEq env Γ A B) (H : SoundTy env Γ M A) : SoundTy env Γ M B :=
  fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W h; ⟨_, _, a1, a2, (H1 W).1 a3, a4⟩

theorem StrongSound.defeq_l (H1 : SoundEq env Γ M N) (H : StrongSound env Γ M A)
    (core : StrongSoundCore env Γ N A') (h : SoundEq env Γ A' A) : StrongSound env Γ N A :=
  ⟨H.sound.defeq_l H1, core, h⟩

theorem StrongSound.defeq_r (H1 : SoundEq env Γ A B) : StrongSound env Γ M A → StrongSound env Γ M B
  | ⟨a, b, c⟩ => ⟨a.defeq_r H1, b, c.trans H1⟩

/-- Assemble a `StrongSoundEq` from the cores of both sides and the pointwise facts. -/
theorem StrongSoundEq.mk'
    (h2 : StrongSoundCore env Γ M A₁) (h2' : SoundEq env Γ A₁ A)
    (h3 : StrongSoundCore env Γ N A₂) (h3' : SoundEq env Γ A₂ A)
    (h4 : ∀ {{Γ₀ ρ}}, Valuation.Fits env Γ₀ Γ ρ → ∀ {m},
      (Interp env ρ m M ↔ Interp env ρ m N) ∧ (Interp env ρ m M → InterpTyped env ρ m M A)) :
    StrongSoundEq env Γ M N A := by
  refine have ha := ?_; have ht := ?_
    ⟨ha, ⟨ht, h2, h2'⟩, ⟨ht.defeq_l ha, h3, h3'⟩⟩
  · exact fun _ _ W _ => (h4 W).1
  · exact fun _ _ W _ => (h4 W).2

end
