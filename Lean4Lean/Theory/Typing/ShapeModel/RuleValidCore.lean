import Lean4Lean.Theory.Typing.ShapeModel.Sound

/-!
# Validity of computation rules: the semantic framework

A computation rule is `fun Ds => head args ≡ fun Ds => R`: both sides are lambda telescopes over
the same domains `Ds`. This file provides the generic semantic tools for proving such rules valid
in the shape model (`ExtraValid`, `ElimValidIn`):

* `KeysFit ρ Ds σ`: `σ` extends `ρ` by keys typed along the telescope `Ds` (each key typed at an
  approximation of its domain under the earlier keys), exactly the valuations that the `lam`
  clause of `Interp` quantifies over;
* telescope extensionality (`Interp.wrapLams_congr`): two lambda telescopes over the same domains
  have the same approximations as soon as their bodies have the same approximations under every
  such valuation;
* inversion of the semantic records of lambda telescopes (`body_records`): from the records of
  both sides at types with the same approximations, the valuation fits the extended context, the
  bodies have records, and their types have the same approximations under the keys (semantic
  injectivity of Pi types at typed keys, `Interp.forallE_inj`);
* inversion of the approximations of a head (constant or eliminator) applied to at most as many
  arguments as its rules take (`Interp.mkApps_head_inv`), and realization of such spines from a
  table of the spine machine (`Spine.realize_head`, the head-generic form of `Spine.realize`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-- `SoundEq` in the empty context is equality of the approximations at the base valuation. -/
theorem SoundEq.nil_of (H : ∀ m, Interp env .nil m M ↔ Interp env .nil m N) :
    SoundEq env [] M N := by
  intro Γ₀ ρ W m
  cases W with
  | nil => exact H m

theorem Valuation.Fits.nil_inv (W : Valuation.Fits env Γ₀ [] ρ) : Γ₀ = [] ∧ ρ = .nil := by
  cases W with
  | nil => exact ⟨rfl, rfl⟩

/-! ### Keys along a lambda telescope -/

variable (env) in
/-- `σ` extends `ρ` by keys typed along the telescope `Ds` (outermost domain first): each key is
typed at an approximation of its domain under the valuation extended by the earlier keys. -/
inductive KeysFit : Valuation → List VExpr → Valuation → Prop
  | nil : KeysFit ρ [] ρ
  | cons {ρ : Valuation} {D : VExpr} {Ds : List VExpr} {σ : Valuation} {a x : TShape} :
    Interp env ρ a D → x.HasType a → KeysFit (ρ.push x) Ds σ → KeysFit ρ (D :: Ds) σ

theorem VExpr.wrapLams_cons (D : VExpr) (Ds : List VExpr) (b : VExpr) :
    VExpr.wrapLams (D :: Ds) b = .lam D (VExpr.wrapLams Ds b) := rfl

theorem VExpr.wrapForalls_cons (D : VExpr) (Ds : List VExpr) (b : VExpr) :
    VExpr.wrapForalls (D :: Ds) b = .forallE D (VExpr.wrapForalls Ds b) := rfl

/-- Telescope extensionality: lambda telescopes over the same domains have the same
approximations if their bodies have the same approximations under every valuation extending the
current one by keys typed along the telescope. -/
theorem Interp.wrapLams_congr {Ds : List VExpr} {b₁ b₂ : VExpr} {ρ : Valuation}
    (H : ∀ σ, KeysFit env ρ Ds σ → ∀ m, Interp env σ m b₁ ↔ Interp env σ m b₂) :
    ∀ m, Interp env ρ m (VExpr.wrapLams Ds b₁) ↔ Interp env ρ m (VExpr.wrapLams Ds b₂) := by
  induction Ds generalizing ρ with
  | nil => exact H ρ .nil
  | cons D Ds ih =>
    have key : ∀ {a x : TShape}, Interp env ρ a D → x.HasType a → ∀ m,
        Interp env (ρ.push x) m (VExpr.wrapLams Ds b₁) ↔
          Interp env (ρ.push x) m (VExpr.wrapLams Ds b₂) :=
      fun ha hx => ih fun σ hσ => H σ (.cons ha hx hσ)
    intro m
    simp only [VExpr.wrapLams_cons]
    constructor <;> intro h <;> cases h with
    | bot => exact .bot
    | lam h1 h2 h3 h4 =>
      first
      | exact .lam h1 h2 (fun x hx => (key h1 hx.T _).1 (h3 x hx)) h4
      | exact .lam h1 h2 (fun x hx => (key h1 hx.T _).2 (h3 x hx)) h4

/-! ### Records of lambda telescopes -/

theorem StrongSound.lam_inv (H : StrongSound env Γ (.lam A e) T) :
    ∃ u v B, StrongSound env Γ A (.sort u) ∧ StrongSound env (A::Γ) B (.sort v) ∧
      StrongSound env (A::Γ) e B ∧ SoundEq env Γ (.forallE A B) T := by
  obtain ⟨_, core, heq⟩ := H
  cases core with | lam h1 h2 h3 => exact ⟨_, _, _, h1, h2, h3, heq⟩

/-- Semantic injectivity of Pi types at typed keys. -/
theorem Interp.forallE_inj {ρ : Valuation} {D B₁ B₂ : VExpr} {a x : TShape}
    (H : ∀ m, Interp env ρ m (.forallE D B₁) → Interp env ρ m (.forallE D B₂))
    (ha : Interp env ρ a D) (hx : x.HasType a) :
    ∀ m, Interp env (ρ.push x) m B₁ → Interp env (ρ.push x) m B₂ :=
  fun _ h => (Interp.pi_inv (H _ (Interp.pi_intro ha hx h))).2

theorem Valuation.Fits.of_record (W : Valuation.Fits env Γ₀ Γ ρ)
    (hA : StrongSound env Γ A (.sort u)) (ha : Interp env ρ a A) (hx : x.HasType a) :
    Valuation.Fits env Γ₀ (A :: Γ) (ρ.push x) :=
  W.cons (InterpTyped.hsort (hA.sound W)) ha hx

/-- Inversion of the records of two lambda telescopes over the same domains, at types with the
same approximations: under keys typed along the telescope, the valuation fits the extended
context, the bodies have records, and their types have the same approximations; moreover, if the
type is (semantically) a Pi telescope over the same domains, the type of the first body is its
codomain. -/
theorem body_records {Ds : List VExpr} {b₁ b₂ : VExpr} {ρ σ : Valuation}
    (W : Valuation.Fits env Γ₀ Γ ρ) (K : KeysFit env ρ Ds σ)
    (H₁ : StrongSound env Γ (VExpr.wrapLams Ds b₁) T₁)
    (H₂ : StrongSound env Γ (VExpr.wrapLams Ds b₂) T₂)
    (hT : ∀ m, Interp env ρ m T₁ ↔ Interp env ρ m T₂) :
    ∃ B₁ B₂, Valuation.Fits env Γ₀ (Ds.reverse ++ Γ) σ ∧
      StrongSound env (Ds.reverse ++ Γ) b₁ B₁ ∧ StrongSound env (Ds.reverse ++ Γ) b₂ B₂ ∧
      (∀ m, Interp env σ m B₁ ↔ Interp env σ m B₂) ∧
      ∀ Tb, (∀ m, Interp env ρ m T₁ ↔ Interp env ρ m (VExpr.wrapForalls Ds Tb)) →
        ∀ m, Interp env σ m B₁ ↔ Interp env σ m Tb := by
  induction K generalizing Γ T₁ T₂ with
  | nil => exact ⟨T₁, T₂, W, H₁, H₂, hT, fun Tb h => h⟩
  | @cons ρ D Ds σ a x ha hx _ ih =>
    rw [VExpr.wrapLams_cons] at H₁ H₂
    obtain ⟨u₁, v₁, C₁, hA₁, -, hb₁, he₁⟩ := H₁.lam_inv
    obtain ⟨u₂, v₂, C₂, -, -, hb₂, he₂⟩ := H₂.lam_inv
    have hpi : ∀ m, Interp env ρ m (.forallE D C₁) ↔ Interp env ρ m (.forallE D C₂) := fun m =>
      ((he₁ W).trans ((hT m).trans (he₂ W).symm))
    have hC : ∀ m, Interp env (ρ.push x) m C₁ ↔ Interp env (ρ.push x) m C₂ := fun m =>
      ⟨Interp.forallE_inj (fun m => (hpi m).1) ha hx m,
        Interp.forallE_inj (fun m => (hpi m).2) ha hx m⟩
    obtain ⟨B₁, B₂, W', r₁, r₂, hB, hTb⟩ := ih (W.of_record hA₁ ha hx) hb₁ hb₂ hC
    refine ⟨B₁, B₂, ?_, ?_, ?_, hB, fun Tb hTb' => hTb Tb fun m => ?_⟩
    · simpa using W'
    · simpa using r₁
    · simpa using r₂
    · have hpi' : ∀ m, Interp env ρ m (.forallE D C₁) ↔
          Interp env ρ m (.forallE D (VExpr.wrapForalls Ds Tb)) := fun m =>
        (he₁ W).trans (hTb' m)
      exact ⟨Interp.forallE_inj (fun m => (hpi' m).1) ha hx m,
        Interp.forallE_inj (fun m => (hpi' m).2) ha hx m⟩

/-! ### Heads -/

/-- The expression of a head at universe levels `ls`. -/
def Head.toExpr : Head → List VLevel → VExpr
  | .const c, ls => .const c ls
  | .elim b o, ls => .elim b o ls

theorem Interp.head_inv {h : Head} (H : Interp env ρ m (h.toExpr ls)) :
    m ≤ .bot ∨ ∃ k, ∃ m' : TShape, Const env (Interp env) h ls (n := k) [] m' ∧ m ≤ m' := by
  cases h with
  | const c =>
    cases H with
    | bot => exact .inl TShape.bot_eqv.1
    | @const _ _ _ m' _ _ k _ R _ _ h3 _ _ h6 h7 => exact .inr ⟨k, m', h6.imp (h7 _ _ _), h3⟩
  | elim b o =>
    cases H with
    | bot => exact .inl TShape.bot_eqv.1
    | elim _ h3 _ _ h6 h7 => exact .inr ⟨_, _, h6.imp (h7 _ _ _), h3⟩

/-- The approximations of a head applied to at most as many arguments as each of its rules
takes are below a table of the spine machine at argument shapes approximating the arguments
(arguments given in reverse order). -/
theorem Interp.mkApps_head_inv_rev {h : Head}
    (hr : ∀ r, SemSig.rules r → r.head = h → rev.length ≤ r.arity)
    (H : Interp env ρ m (VExpr.mkApps (h.toExpr ls) rev.reverse)) :
    m ≤ .bot ∨ ∃ n, ∃ rargs : List (WShape n), ∃ y,
      Const env (Interp env) h ls rargs y ∧ m ≤ y ∧
      List.Forall₂ (fun x A => Interp env ρ x.T A) rargs rev := by
  induction rev generalizing m with
  | nil =>
    rcases Interp.head_inv H with h | ⟨k, m', hC, hle⟩
    · exact .inl h
    · exact .inr ⟨k, [], m', hC, hle, .nil⟩
  | cons a as ih =>
    rw [List.reverse_cons, VExpr.mkApps_append_singleton] at H
    have hr' : ∀ r, SemSig.rules r → r.head = h → as.length ≤ r.arity := fun r h1 h2 =>
      Nat.le_of_succ_le (hr r h1 h2)
    cases H with
    | bot => exact .inl TShape.bot_eqv.1
    | @app n _ _ _ _ f a' hf ha hle =>
    rcases ih hr' hf with hb | ⟨k, rargs, y, hC, hfy, hargs⟩
    · refine .inl (hle.trans ?_)
      have : f = .bot := TShape.le_bot.1 hb
      subst this; rw [WShape.bot_app]; exact TShape.bot_eqv.1
    obtain ⟨K, hk, hn⟩ : ∃ K, k ≤ K ∧ n ≤ K := ⟨_, Nat.le_max_left k n, Nat.le_max_right k n⟩
    have hC' := hC.lift Interp.relMono hk
    have hargs' : List.Forall₂ (fun x A => Interp env ρ x.T A)
        (rargs.map (WShape.lift K)) as :=
      List.forall₂_map_left_iff.2 <| hargs.imp fun x _ h => Interp.lift (m := x.T) hk h
    clear hC
    have hlen := hargs'.length_eq
    generalize rargs.map (WShape.lift K) = rargs' at hC' hargs' hlen
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
    | rule h1 h2 _ h4 h5 =>
      have := hr _ h1 h2
      simp [Rule.arity, h4] at this; omega
    | ruleAB h1 h2 _ h4 _ _ h7 =>
      have := hr _ h1 h2
      simp [Rule.arity, h4] at this hlen; omega
    | ruleC h1 h2 _ h4 _ _ _ h8 =>
      have := hr _ h1 h2
      simp [Rule.arity, h4] at this; omega

theorem Interp.mkApps_head_inv {h : Head}
    (hr : ∀ r, SemSig.rules r → r.head = h → args.length ≤ r.arity)
    (H : Interp env ρ m (VExpr.mkApps (h.toExpr ls) args)) :
    m ≤ .bot ∨ ∃ n, ∃ rargs : List (WShape n), ∃ y,
      Const env (Interp env) h ls rargs y ∧ m ≤ y ∧
      List.Forall₂ (fun x A => Interp env ρ x.T A) rargs.reverse args := by
  rw [← List.reverse_reverse args] at H
  rcases Interp.mkApps_head_inv_rev (rev := args.reverse) (by simpa using hr) H with
    h | ⟨n, rargs, y, a1, a2, a3⟩
  · exact .inl h
  · refine .inr ⟨n, rargs, y, a1, a2, ?_⟩
    have := List.Forall₂.reverse.2 a3
    rwa [List.reverse_reverse] at this

/-! ### Realization of head spines -/

theorem Head.realize_nil {h : Head} (hcl : ConstClosed env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : Interp env ρ a T) (hTy : StrongSound env Γ (h.toExpr ls) T)
    (hC : Const env (Interp env) h ls (n := k) [] m') : Interp env ρ m' (h.toExpr ls) := by
  obtain ⟨_, hcore, hT⟩ := hTy
  cases h with
  | const c =>
    obtain ⟨ci, u, h1, h2, -, rfl⟩ := hcore.const_inv
    exact .const h1 h2 .rfl mty ((Interp.closed_iff (hcl h1).instL).1 ((hT W).2 ha)) hC
      fun _ _ _ h => h
  | elim b o =>
    cases hcore with
    | elim h1 h2 _ =>
      exact .elim h1 .rfl mty ((Interp.closed_iff h2.instL).1 ((hT W).2 ha)) hC fun _ _ _ h => h

/-- Realization of a head spine (`Spine.realize` for constant and eliminator heads): a table of
the spine machine at argument shapes approximating the arguments, typed at an approximation of
the type of the spine, approximates the spine. -/
theorem Spine.realize_head {h : Head} (hcl : ConstClosed env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : Interp env ρ a T)
    (hTy : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) rev.reverse) T)
    {rargs : List (WShape n)}
    (hargs : List.Forall₂ (fun x A => Interp env ρ x.T A) rargs rev)
    (hC : Const env (Interp env) h ls rargs m') :
    Interp env ρ m' (VExpr.mkApps (h.toExpr ls) rev.reverse) := by
  induction rev generalizing m' a T rargs n with
  | nil =>
    cases hargs
    exact Head.realize_nil hcl W mty ha hTy hC
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
    suffices Interp env ρ m2.T (VExpr.mkApps (h.toExpr ls) rest.reverse) by
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

theorem Spine.realize_head' {h : Head} (hcl : ConstClosed env) (W : Valuation.Fits env Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : Interp env ρ a T)
    (hTy : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) args) T)
    {rargs : List (WShape n)}
    (hargs : List.Forall₂ (fun x A => Interp env ρ x.T A) rargs.reverse args)
    (hC : Const env (Interp env) h ls rargs m') :
    Interp env ρ m' (VExpr.mkApps (h.toExpr ls) args) := by
  rw [← List.reverse_reverse args] at hTy ⊢
  refine Spine.realize_head hcl W mty ha hTy ?_ hC
  have := List.Forall₂.reverse.2 hargs
  rwa [List.reverse_reverse] at this

/-! ### Head types along spines -/

variable (env) in
/-- `Th` is the type of the head `h` at levels `ls` (the type of its structural record). -/
def HeadType : Head → List VLevel → VExpr → Prop
  | .const c, ls, Th => ∃ ci, env.constants c = some ci ∧ Th = ci.type.instL ls
  | .elim b o, ls, Th => ∃ T, SemSig.elimType b o = some T ∧ Th = T.instL ls

theorem HeadType.core_eq {h : Head} (hTh : HeadType env h ls Th)
    (H : StrongSoundCore env Γ (h.toExpr ls) T) : T = Th := by
  cases h with
  | const c =>
    obtain ⟨ci, h1, rfl⟩ := hTh
    obtain ⟨ci', u, h1', -, -, rfl⟩ := H.const_inv
    cases h1.symm.trans h1'; rfl
  | elim b o =>
    obtain ⟨T', h1, rfl⟩ := hTh
    cases H with | elim h1' _ _ => cases h1.symm.trans h1'; rfl

/-- `Spine.ofPi` for constant and eliminator heads. -/
theorem Spine.ofPi_head {h : Head} (W : Valuation.Fits env Γ₀ Γ ρ)
    (hTy : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) rev.reverse) T)
    (hTh : HeadType env h ls Th)
    (hps : List.Forall₂ (fun p A => Interp env ρ p.2 A) qs rev)
    (H : Interp env ρ (nestPi qs.reverse R) Th) : Interp env ρ R T := by
  induction hps generalizing R T with
  | nil =>
    obtain ⟨_, hcore, hT⟩ := hTy
    cases hTh.core_eq hcore
    exact (hT W).1 H
  | @cons q a qs rev hq _ ih =>
    rw [List.reverse_cons, VExpr.mkApps_append_singleton] at hTy
    rw [List.reverse_cons, nestPi_append_singleton] at H
    obtain ⟨_, hcore, hT⟩ := hTy
    obtain ⟨A, B, hf, -, rfl⟩ := hcore.app_inv
    have ⟨_, h2⟩ := Interp.pi_inv (ih hf H)
    exact (hT W).1 (Interp.inst.2 ⟨_, h2, hq⟩)

/-- `Spine.typed` for constant and eliminator heads. -/
theorem Spine.typed_head {h : Head} (W : Valuation.Fits env Γ₀ Γ ρ)
    (hTy : StrongSound env Γ (VExpr.mkApps (h.toExpr ls) rev.reverse) T)
    (hTh : HeadType env h ls Th)
    (hxs : List.Forall₂ (fun x A => Interp env ρ x A) xs rev) (hR : Interp env ρ R T) :
    ∃ qs, List.Forall₂ (fun x p => x ≤ p.2) xs qs ∧
      List.Forall₂ (fun p A => Interp env ρ p.2 A) qs rev ∧ TelTyped qs ∧
      Interp env ρ (nestPi qs.reverse R) Th := by
  induction hxs generalizing R T with
  | nil =>
    obtain ⟨_, hcore, hT⟩ := hTy
    cases hTh.core_eq hcore
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

end

end Lean4Lean.ShapeModel
