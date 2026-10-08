import Lean4Lean.Theory.Typing.ShapeModel.Sound.Basic

/-!
# Soundness of the shape model: constant spines

Telescope shapes (`TShape.pi`, `nestPi`), the inversion of the approximations of a constant
applied to arguments, and the realization of constant spines from typed approximations of
their arguments (the port of `apps_realize` from the prototype), together with the typed
approximation of the head's type that such a realization produces (`Spine.typed`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-! ### Single Pi shapes with one entry -/

/-- The Pi shape with domain `d` whose codomain table maps `x` (and everything above it) to
`R`, at the common depth of its components. -/
def TShape.pi (d x R : TShape) : TShape :=
  WShape.T (n := max d.1 (max x.1 R.1) + 1)
    (.forallE (d.2.lift _) (WShapeFun.single (x.2.lift _) (R.2.lift _)))

theorem TShape.pi_def {d x R : TShape} :
    ∃ k, d.1 ≤ k ∧ x.1 ≤ k ∧ R.1 ≤ k ∧ TShape.pi d x R =
      WShape.T (n := k+1) (.forallE (d.2.lift k) (WShapeFun.single (x.2.lift k) (R.2.lift k))) := by
  have := Nat.max_le.1 (Nat.le_refl (max d.1 (max x.1 R.1))); rw [Nat.max_le] at this
  exact ⟨_, this.1, this.2.1, this.2.2, rfl⟩

theorem Interp.pi_intro {d x R : TShape} (hd : Interp env ρ d D) (hx : x.HasType d)
    (hR : Interp env (ρ.push x) R B) : Interp env ρ (TShape.pi d x R) (.forallE D B) := by
  obtain ⟨k, h1, h2, h3, e⟩ := TShape.pi_def (d := d) (x := x) (R := R); rw [e]
  have hd' := hd.lift h1
  refine .forallE' hd' hd' (WShape.HasDom.single.2 (.inl ((TShape.HasType.def h2 h1).1 hx)))
    fun x' _ => ?_
  rw [WShapeFun.single_app]; split <;> rename_i hle
  · refine (hR.lift h3).mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
    exact (TShape.lift_eqv h2).2.trans hle.T
  · exact .bot

theorem Interp.pi_inv {d x R : TShape} (H : Interp env ρ (TShape.pi d x R) (.forallE D B)) :
    Interp env ρ d D ∧ Interp env (ρ.push x) R B := by
  obtain ⟨k, h1, h2, h3, e⟩ := TShape.pi_def (d := d) (x := x) (R := R); rw [e] at H
  have ⟨a1, a2⟩ := H.forallE_inv'
  refine ⟨a1.unlift h1, ?_⟩
  have := a2 (x.2.lift k)
  rw [WShapeFun.single_app, if_pos WShape.LE.rfl] at this
  exact (this.unlift h3).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.lift_eqv h2).1⟩)

theorem TShape.pi_type {d x R : TShape} (hx : x.HasType d) (hR : R.HasType .type) :
    (TShape.pi d x R).HasType .type := by
  obtain ⟨k, h1, h2, h3, e⟩ := TShape.pi_def (d := d) (x := x) (R := R); rw [e]
  refine TShape.HasType.sort_r.2 (.forallE (WShape.HasTypePi.def.2 ⟨?_, fun y z hm => ?_⟩))
  · exact WShape.HasDom.single.2 (.inl ((TShape.HasType.def h2 h1).1 hx))
  · obtain ⟨⟨⟩⟩ | ⟨_, ⟨⟩⟩ := WShapeFun.mem_single.1 hm
    · have := (TShape.HasType.def h3 (Nat.zero_le _)).1 hR
      simpa [TShape.type, TShape.sort, WShape.lift_sort] using this
    · exact .bot' .sort_type

theorem TShape.le_piApp_pi {d x R y : TShape} (hxy : x ≤ y) :
    R ≤ (TShape.pi d x R).piApp y := by
  obtain ⟨k, h1, h2, h3, e⟩ := TShape.pi_def (d := d) (x := x) (R := R)
  have hK := Nat.max_le.1 (Nat.le_refl (max k y.1))
  have ⟨a1, a2⟩ := TShape.piApp_lift (T := TShape.pi d x R) (x := y) (k := max k y.1)
    (by rw [e]; exact Nat.succ_le_succ hK.1) hK.2
  rw [TShape.LE.def (Nat.le_trans h3 hK.1) a1, a2, e]
  dsimp only
  rw [WShape.lift_forallE hK.1, WShape.piApp_forallE, WShapeFun.lift_single hK.1,
    WShapeFun.single_app, if_pos]
  · rw [WShape.lift_lift (.inl h3)]; exact WShape.LE.rfl
  · rw [WShape.lift_lift (.inl h2)]
    exact (TShape.LE.def (Nat.le_trans h2 hK.1) hK.2).1 hxy

/-! ### Telescopes -/

/-- Push a list of shapes onto a valuation, the first one first (so the last one is
variable `0`). -/
def Valuation.pushes (ρ : Valuation) : List TShape → Valuation
  | [] => ρ
  | x :: xs => (ρ.push x).pushes xs

/-- A Pi telescope shape: domain/key pairs, then the final codomain. -/
def nestPi : List (TShape × TShape) → TShape → TShape
  | [], R => R
  | p :: ps, R => TShape.pi p.1 p.2 (nestPi ps R)

variable (env) in
/-- The domains of a telescope shape approximate the domains of a telescope of expressions,
each under the valuation extended by the keys of the earlier entries. -/
inductive TelInterp : Valuation → List VExpr → List (TShape × TShape) → Prop
  | nil : TelInterp ρ [] []
  | cons : Interp env ρ d D → TelInterp (ρ.push x) Ds ps → TelInterp ρ (D :: Ds) ((d, x) :: ps)

/-- Each key of a telescope shape is typed at its domain. -/
def TelTyped (ps : List (TShape × TShape)) : Prop := ∀ p ∈ ps, p.2.HasType p.1

theorem TelInterp.length_eq (H : TelInterp env ρ Ds ps) : Ds.length = ps.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Interp.nest_intro (H1 : TelInterp env ρ Ds ps) (H2 : TelTyped ps)
    (H3 : Interp env (ρ.pushes (ps.map (·.2))) R body) :
    Interp env ρ (nestPi ps R) (Ds.foldr .forallE body) := by
  induction H1 with
  | nil => exact H3
  | cons hd _ ih =>
    have ⟨h1, h2⟩ := List.forall_mem_cons.1 H2
    exact .pi_intro hd h1 (ih h2 H3)

theorem Interp.nest_inv (hl : Ds.length = ps.length)
    (H : Interp env ρ (nestPi ps R) (Ds.foldr .forallE body)) :
    TelInterp env ρ Ds ps ∧ Interp env (ρ.pushes (ps.map (·.2))) R body := by
  induction ps generalizing ρ Ds with
  | nil => cases Ds <;> [exact ⟨.nil, H⟩; cases hl]
  | cons p ps ih =>
    cases Ds with | nil => cases hl | cons D Ds
    have ⟨h1, h2⟩ := Interp.pi_inv H
    have ⟨h3, h4⟩ := ih (Nat.succ.inj hl) h2
    exact ⟨.cons h1 h3, h4⟩

theorem TShape.nestPi_type (H : TelTyped ps) (hR : R.HasType .type) :
    (nestPi ps R).HasType .type := by
  induction ps with
  | nil => exact hR
  | cons p ps ih =>
    have ⟨h1, h2⟩ := List.forall_mem_cons.1 H
    exact TShape.pi_type h1 (ih h2)

theorem TShape.le_foldl_piApp_nestPi {ps : List (TShape × TShape)} {ys : List TShape}
    (h : List.Forall₂ (fun p y => p.2 ≤ y) ps ys) :
    R ≤ ys.foldl TShape.piApp (nestPi ps R) := by
  induction h generalizing R with
  | nil => exact .rfl
  | cons h1 _ ih =>
    simp only [nestPi, List.foldl]
    exact ih.trans (foldl_piApp_mono (TShape.le_piApp_pi h1) (List.Forall₂.rfl fun _ _ => .rfl))

/-! ### Inversion of constant spines -/

theorem WShape.app_of_ne_lam {g : WShape (n+1)} (h : ∀ f hf, g ≠ .lam f hf) (x : WShape n) :
    g.app x = .bot := by
  obtain ⟨⟨⟩, wf⟩ := g <;> try rfl
  exact absurd rfl (h ⟨_, wf.1⟩ wf.2)

theorem WShape.ctor'_ne_lam {l : List (WShape n)} : ∀ f hf, WShape.ctor' c l ≠ .lam f hf := by
  intro f hf h; unfold WShape.ctor' at h; split at h <;> cases congrArg (·.1) h

theorem WShape.rigid_ne_lam {l : List (WShape n)} {t} :
    ∀ f hf, WShape.rigid c ls l t ≠ .lam f hf := by
  intro f hf h; cases congrArg (·.1) h

theorem TShape.app_le_bot_of_le {f : WShape (n+1)} {g : WShape (k+1)} (hg : ∀ f hf, g ≠ .lam f hf)
    (le : f.T ≤ g.T) (a : WShape n) : (f.app a).T ≤ .bot := by
  have hK := Nat.max_le.1 (Nat.le_refl (max n k))
  have := TShape.app_mono (a' := a.lift (max n k)) (le.trans (TShape.lift_eqv (a := g.T)
    (Nat.succ_le_succ hK.2)).2) (TShape.lift_eqv hK.1).2
  refine this.trans ?_
  rw [WShape.app_of_ne_lam]; · exact TShape.bot_eqv.1
  intro f' hf' e
  cases g using WShape.casesOn' with
  | lam g' hg' => exact hg _ _ rfl
  | _ =>
    first
    | (rw [WShape.lift_bot] at e; cases congrArg (·.1) e)
    | (rw [WShape.lift_sort] at e; cases congrArg (·.1) e)
    | (rw [WShape.lift_forallE (Nat.le_trans (Nat.le_refl _) hK.2)] at e; cases congrArg (·.1) e)
    | (rw [WShape.lift_ctor hK.2] at e; cases congrArg (·.1) e)
    | (rw [WShape.lift_rigid hK.2] at e; cases congrArg (·.1) e)

theorem VExpr.mkApps_append_singleton (f : VExpr) (as : List VExpr) (a : VExpr) :
    VExpr.mkApps f (as ++ [a]) = .app (VExpr.mkApps f as) a := by
  simp [VExpr.mkApps, List.foldl_append]

/-- The approximations of a constant `c` (heading no rule) applied to arguments are below a
table of the spine machine at argument shapes approximating the arguments (version with the
arguments given in reverse order). -/
theorem Interp.mkApps_const_inv_rev (hr : ∀ r, SemSig.rules r → r.head ≠ .const c)
    (H : Interp env ρ m (VExpr.mkApps (.const c ls) rev.reverse)) :
    m ≤ .bot ∨ ∃ n, ∃ rargs : List (WShape n), ∃ y,
      Const env (Interp env) (.const c) ls rargs y ∧ m ≤ y ∧
      List.Forall₂ (fun x A => Interp env ρ x.T A) rargs rev := by
  induction rev generalizing m with
  | nil =>
    cases H with
    | bot => exact .inl TShape.bot_eqv.1
    | @const _ _ _ m' _ _ k _ R _ _ h3 _ _ h6 h7 =>
      exact .inr ⟨k, [], m', h6.imp (h7 _ _ _), h3, .nil⟩
  | cons a as ih =>
    rw [List.reverse_cons, VExpr.mkApps_append_singleton] at H
    cases H with
    | bot => exact .inl TShape.bot_eqv.1
    | @app n _ _ _ _ f a' hf ha hle =>
    rcases ih hf with hb | ⟨k, rargs, y, hC, hfy, hargs⟩
    · refine .inl (hle.trans ?_)
      have : f = .bot := TShape.le_bot.1 hb
      subst this; rw [WShape.bot_app]; exact TShape.bot_eqv.1
    obtain ⟨K, hk, hn⟩ : ∃ K, k ≤ K ∧ n ≤ K := ⟨_, Nat.le_max_left k n, Nat.le_max_right k n⟩
    have hC' := hC.lift Interp.relMono hk
    have hargs' : List.Forall₂ (fun x A => Interp env ρ x.T A)
        (rargs.map (WShape.lift K)) as :=
      List.forall₂_map_left_iff.2 <| hargs.imp fun x _ h => Interp.lift (m := x.T) hk h
    clear hC
    generalize rargs.map (WShape.lift K) = rargs' at hC' hargs'
    cases hC' with
    | bot =>
      refine .inl (hle.trans ?_)
      have : f = .bot := TShape.le_bot.1 (hfy.trans TShape.bot_eqv.1)
      subst this; rw [WShape.bot_app]; exact TShape.bot_eqv.1
    | @lam _ _ _ f' hrec hy =>
      obtain ⟨x', hx'1, hx'2⟩ := WShapeFun.app_eq f' (a'.lift K)
      refine .inr ⟨_, x' :: _, _, hrec _ _ hx'2, hle.trans ?_, .cons ?_ hargs'⟩
      · have := TShape.app_mono (a := a') (a' := a'.lift K) (hfy.trans hy)
          (TShape.lift_eqv (a := a'.T) hn).2
        rwa [WShape.lam'_app] at this
      · exact ha.mono (hx'1.T.trans (TShape.lift_eqv (a := a'.T) hn).1)
    | ctor _ _ _ hy =>
      exact .inl (hle.trans (TShape.app_le_bot_of_le WShape.ctor'_ne_lam (hfy.trans hy) _))
    | rigid _ _ _ _ _ hy =>
      exact .inl (hle.trans (TShape.app_le_bot_of_le WShape.rigid_ne_lam (hfy.trans hy) _))
    | rule h1 h2 => cases hr _ h1 h2
    | ruleAB h1 h2 => cases hr _ h1 h2
    | ruleC h1 h2 => cases hr _ h1 h2

/-- The approximations of a constant `c` (heading no rule) applied to arguments are below a
table of the spine machine at argument shapes approximating the arguments. -/
theorem Interp.mkApps_const_inv (hr : ∀ r, SemSig.rules r → r.head ≠ .const c)
    (H : Interp env ρ m (VExpr.mkApps (.const c ls) args)) :
    m ≤ .bot ∨ ∃ n, ∃ rargs : List (WShape n), ∃ y,
      Const env (Interp env) (.const c) ls rargs y ∧ m ≤ y ∧
      List.Forall₂ (fun x A => Interp env ρ x.T A) rargs.reverse args := by
  rw [← List.reverse_reverse args] at H
  rcases Interp.mkApps_const_inv_rev hr H with h | ⟨n, rargs, y, a1, a2, a3⟩
  · exact .inl h
  · refine .inr ⟨n, rargs, y, a1, a2, ?_⟩
    have := List.Forall₂.reverse.2 a3
    rwa [List.reverse_reverse] at this

/-! ### Inversion of structural records -/

theorem StrongSoundCore.app_inv (H : StrongSoundCore env Γ (.app f a) T) :
    ∃ A B, StrongSound env Γ f (.forallE A B) ∧ StrongSound env Γ a A ∧ T = B.inst a := by
  cases H with | app h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

theorem StrongSoundCore.const_inv (H : StrongSoundCore env Γ (.const c ls) T) :
    ∃ ci u, env.constants c = some ci ∧ ls.length = ci.uvars ∧
      StrongSound env Γ (ci.type.instL ls) (.sort u) ∧ T = ci.type.instL ls := by
  cases H with | const h1 h2 h3 => exact ⟨_, _, h1, h2, h3, rfl⟩

theorem StrongSoundCore.forallE_inv (H : StrongSoundCore env Γ (.forallE A B) T) :
    ∃ u v, StrongSound env Γ A (.sort u) ∧ StrongSound env (A::Γ) B (.sort v) := by
  cases H with | forallE h1 h2 => exact ⟨_, _, h1, h2⟩

theorem StrongSound.forallE_inv (H : StrongSound env Γ (.forallE A B) T) :
    ∃ u v, StrongSound env Γ A (.sort u) ∧ StrongSound env (A::Γ) B (.sort v) :=
  let ⟨_, h, _⟩ := H; h.forallE_inv

/-! ### Realization of constant spines -/

/-- Constant types are closed. -/
def ConstClosed (env : VEnv) : Prop := ∀ {c ci}, env.constants c = some ci → ci.type.Closed

theorem nestPi_append_singleton {ps : List (TShape × TShape)} :
    nestPi (ps ++ [q]) R = nestPi ps (TShape.pi q.1 q.2 R) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [nestPi, ih]

/-- If a telescope shape whose keys approximate the arguments of a constant spine approximates
the constant's type, its final codomain approximates the type of the spine. -/
theorem Spine.ofPi (W : Valuation.Fits env Γ₀ Γ ρ)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const c ls) rev.reverse) T)
    (hci : env.constants c = some ci)
    (hps : List.Forall₂ (fun p A => Interp env ρ p.2 A) qs rev)
    (H : Interp env ρ (nestPi qs.reverse R) (ci.type.instL ls)) : Interp env ρ R T := by
  induction hps generalizing R T with
  | nil =>
    obtain ⟨_, hcore, hT⟩ := hTy
    obtain ⟨ci', u, h1, h2, -, rfl⟩ := hcore.const_inv
    cases h1.symm.trans hci
    exact (hT W).1 H
  | @cons q a qs rev hq _ ih =>
    rw [List.reverse_cons, VExpr.mkApps_append_singleton] at hTy
    rw [List.reverse_cons, nestPi_append_singleton] at H
    obtain ⟨_, hcore, hT⟩ := hTy
    obtain ⟨A, B, hf, -, rfl⟩ := hcore.app_inv
    have ⟨_, h2⟩ := Interp.pi_inv (ih hf H)
    exact (hT W).1 (Interp.inst.2 ⟨_, h2, hq⟩)

/-- Typed approximations of the arguments of a constant spine, and the approximation of the
constant's type that they produce, from an approximation `R` of the type of the spine. -/
theorem Spine.typed (W : Valuation.Fits env Γ₀ Γ ρ)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const c ls) rev.reverse) T)
    (hci : env.constants c = some ci)
    (hxs : List.Forall₂ (fun x A => Interp env ρ x A) xs rev) (hR : Interp env ρ R T) :
    ∃ qs, List.Forall₂ (fun x p => x ≤ p.2) xs qs ∧
      List.Forall₂ (fun p A => Interp env ρ p.2 A) qs rev ∧ TelTyped qs ∧
      Interp env ρ (nestPi qs.reverse R) (ci.type.instL ls) := by
  induction hxs generalizing R T with
  | nil =>
    obtain ⟨_, hcore, hT⟩ := hTy
    obtain ⟨ci', u, h1, h2, -, rfl⟩ := hcore.const_inv
    cases h1.symm.trans hci
    exact ⟨[], .nil, .nil, nofun, (hT W).2 hR⟩
  | @cons x a xs rev hx _ ih =>
    rw [List.reverse_cons, VExpr.mkApps_append_singleton] at hTy
    obtain ⟨_, hcore, hT⟩ := hTy
    obtain ⟨A, B, hf, ha, rfl⟩ := hcore.app_inv
    obtain ⟨y, hyB, hya⟩ := Interp.inst.1 ((hT W).2 hR)
    have hj := hx.join' hya
    have hJ := TShape.Join.mk (hx.compat hya)
    obtain ⟨x', d, a1, a2, a3, a4⟩ := ha.sound W hj
    have hpi : Interp env ρ (TShape.pi d x' R) (.forallE A B) :=
      .pi_intro a3 a4 (hyB.mono_l (Valuation.LE.push.2 ⟨.rfl, hJ.le.2.trans a1⟩))
    obtain ⟨qs, b1, b2, b3, b4⟩ := ih hf hpi
    refine ⟨(d, x') :: qs, .cons (hJ.le.1.trans a1) b1, .cons a2 b2, ?_, ?_⟩
    · exact List.forall_mem_cons.2 ⟨a4, b3⟩
    · rw [List.reverse_cons, nestPi_append_singleton]; exact b4

/-- Realization of a constant spine (the prototype's `apps_realize`): a table of the spine
machine at argument shapes approximating the arguments, typed at an approximation of the type of
the spine, approximates the spine. -/
theorem Spine.realize (hcl : ConstClosed env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : Interp env ρ a T)
    (hTy : StrongSound env Γ (VExpr.mkApps (.const c ls) rev.reverse) T)
    {rargs : List (WShape n)}
    (hargs : List.Forall₂ (fun x A => Interp env ρ x.T A) rargs rev)
    (hC : Const env (Interp env) (.const c) ls rargs m') :
    Interp env ρ m' (VExpr.mkApps (.const c ls) rev.reverse) := by
  induction rev generalizing m' a T rargs n with
  | nil =>
    cases hargs
    obtain ⟨_, hcore, hT⟩ := hTy
    obtain ⟨ci, u, h1, h2, -, rfl⟩ := hcore.const_inv
    exact .const h1 h2 .rfl mty ((Interp.closed_iff (hcl h1).instL).1 ((hT W).2 ha)) hC
      fun _ _ _ h => h
  | cons A rest ih =>
    let .cons (a := arg) (l₁ := rest_r) h_arg h_rest := hargs
    rw [List.reverse_cons, VExpr.mkApps_append_singleton] at hTy ⊢
    obtain ⟨_, hcore, hC_inst⟩ := hTy
    obtain ⟨A', B, hMf, hMa, rfl⟩ := hcore.app_inv
    obtain ⟨y, hya, hy⟩ := Interp.inst.1 ((hC_inst W).2 ha)
    obtain ⟨n', arg', aT, _, jle, h_LE, ha', harg'⟩ := (hMa.sound W (h_arg.join' hy)).out
    let k := max (max n m'.1) (max n' a.1)
    have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
    let arg'' := arg'.lift k; let m'' := m'.2.lift k
    let m2 : WShape (k+1) := .lam' (.single arg'' m'')
    suffices Interp env ρ m2.T (VExpr.mkApps (.const c ls) rest.reverse) by
      have h_arg'_T : Interp env ρ arg''.T A := h_LE.lift hk.2.1
      have h_app := this.app' h_arg'_T
      simp only [m2, WShape.lam'_app, WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte] at h_app
      exact h_app.mono (TShape.lift_eqv hk.1.2).2
    have hJ := TShape.Join.mk (h_arg.compat hy)
    let aT' := aT.lift k; let a' := a.2.lift k
    let a2 : WShape (k+1) := .forallE aT' (.single arg'' a')
    have h_argw_typed : arg''.HasType aT' := (WShape.HasType.lift hk.2.1).2 harg'
    refine ih (a := a2.T) (rargs := rest_r.map (WShape.lift k)) ?_ ?_ hMf ?_ ?_
    · have h_m_typed := (TShape.HasType.def hk.1.2 hk.2.2).1 mty
      refine WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
      · refine WShape.HasTypePi.def.2
          ⟨WShape.HasDom.single.2 (.inl h_argw_typed), fun x y h => ?_⟩
        obtain ⟨⟨⟩⟩ | ⟨_, ⟨⟩⟩ := WShapeFun.mem_single.1 h
        · exact h_m_typed.isType
        · exact .bot' .sort_type
      · exact WShape.HasDom.single.2 (.inl h_argw_typed)
      · simp only [WShapeFun.single_app]
        split <;> [exact h_m_typed; exact .bot' (.bot' .sort_type)]
    · refine .forallE' (ha'.lift hk.2.1) (ha'.lift hk.2.1)
        (WShape.HasDom.single.2 (.inl h_argw_typed)) fun x _ => ?_
      rw [WShapeFun.single_app]; split <;> [rename_i h1; exact .bot]
      refine .lift hk.2.2 <| hya.mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
      exact (hJ.le.2.trans jle).trans (TShape.lift_eqv hk.2.1).2 |>.trans h1.T
    · exact List.forall₂_map_left_iff.2 <|
        h_rest.imp fun _ _ h => h.mono (TShape.lift_eqv hk.1.1).1
    · refine Const.lam (fun x y hmem => ?_) .rfl
      obtain ⟨⟨⟩⟩ | ⟨_, ⟨⟩⟩ := WShapeFun.mem_single.1 hmem <;> [skip; exact .bot]
      refine (hC.lift Interp.relMono hk.1.1).mono_l Interp.relMono ?_
        |>.mono (TShape.lift_eqv hk.1.2).1 (fun le h => h.mono le)
      exact .cons ((TShape.LE.def hk.1.1 hk.2.1).1 (hJ.le.1.trans jle)) <|
        .rfl fun _ _ => WShape.LE.rfl

end
