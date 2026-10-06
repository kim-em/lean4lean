import Lean4Lean.Theory.Typing.HeadInversion
import Lean4Lean.Theory.Typing.Pattern

/-! # Unique typing and its consequences.

Uniqueness of types is derived from the base obligation `VEnv.WF.headInversion`, without
height stratification: first up to a `TypeChain` (`HasTypeStrong.uniq_chain`), by plain
induction on the first typing, and then collapsed to a single definitional equality
(`TypeChain.collapse`). -/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env U Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq env U Γ e1 e2 A

/-- The type assigned by a strong typing is itself a type. -/
theorem HasTypeStrong.isType (H : env.HasTypeStrong U Γ e A b) : env.IsType U Γ A := by
  induction H with
  | bvar _ _ h => exact ⟨_, h.hasType⟩
  | sort' _ h2 _ => exact ⟨_, .sort h2⟩
  | const _ _ _ _ _ h => exact ⟨_, h.hasType⟩
  | elim _ _ _ _ _ h => exact ⟨_, h.hasType⟩
  | app _ _ _ _ _ _ _ h => exact ⟨_, h.hasType⟩
  | proj _ _ _ _ _ _ _ h => exact ⟨_, h.hasType⟩
  | lam _ _ _ _ _ h => exact ⟨_, h.hasType⟩
  | forallE h1 h2 _ _ => exact ⟨_, .sort (l := .imax _ _) ⟨h1, h2⟩⟩
  | base _ ih => exact ih
  | defeq _ _ _ h _ => exact ⟨_, h.hasType⟩

/-- To relate a type to every type of `e`, it suffices to relate it to the
syntax-directed ones: conversions on the second typing are appended as links. -/
theorem HasTypeStrong.chain_peel
    (H : ∀ {B}, env.HasTypeStrong U Γ e B false → env.TypeChain U Γ A B)
    (h2 : env.HasTypeStrong U Γ e B b) : env.TypeChain U Γ A B := by
  cases b with
  | false => exact H h2
  | true =>
    generalize hb : true = b at h2
    induction h2 with
    | base h => exact H h
    | defeq _ h1 _ _ _ _ _ ih => exact (ih H rfl).tail h1.defeq
    | _ => cases hb

/-- Uniqueness of types up to a chain of sort-typed definitional equalities. The proof is
a plain induction on the first typing; the head inversions of `HeadInversion` replace the
stratified inversion lemmas. -/
theorem HasTypeStrong.uniq_chain (henv : env.WF) (hinv : env.HeadInversion)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.HasTypeStrong U Γ e A b₁) (h2 : env.HasTypeStrong U Γ e B b₂) :
    env.TypeChain U Γ A B := by
  induction h1 generalizing B b₂ with
  | base _ ih => exact ih hΓ h2
  | defeq _ hAB _ _ _ _ _ ih => exact TypeChain.head hAB.defeq.symm (ih hΓ h2)
  | bvar a1 _ a3 =>
    refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
    cases h2 with
    | bvar b1 _ _ => cases a1.uniq b1; exact .refl a3.hasType
  | sort' _ a2 a3 =>
    refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
    cases h2 with
    | sort' _ b2 b3 => exact .single (.sortDF a2 b2 (VLevel.succ_congr (a3.symm.trans b3)))
  | const a1 _ _ _ _ a6 =>
    refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
    cases h2 with
    | const b1 _ _ _ _ _ => cases a1.symm.trans b1; exact .refl a6.hasType
  | @elim block type levels target Γ typeLevel schema owner a1 a2 _ _ _ a6 =>
    refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
    generalize he : VExpr.elim block owner.val (target :: levels) = expression at h2
    cases h2 with
    | @elim block' type' levels' target' _ _ schema' owner' b1 b2 _ _ _ _ =>
      obtain ⟨hblock, howner, hlevels⟩ := VExpr.elim.inj he
      subst block'
      cases henv.eliminators_unique a1 b1
      cases Fin.ext howner
      obtain ⟨rfl, rfl⟩ := List.cons.inj hlevels
      cases Option.some.inj (a2.symm.trans b2)
      exact .refl a6.hasType
    | bvar | sort' | const | app | proj | lam | forallE => cases he
  | app _ _ _ _ _ _ a7 _ _ _ _ ih6 _ _ =>
    refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
    cases h2 with
    | app _ _ _ _ _ b6 _ _ =>
      have ⟨_, _, hB⟩ := hinv.forallE_forallE hΓ (ih6 hΓ b6)
      exact .single (hB.instN henv.ordered a7.hasType .zero)
  | lam _ _ a3 _ _ _ _ _ ih5 _ =>
    refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
    cases h2 with
    | lam _ _ _ _ b5 _ =>
      exact (ih5 ⟨hΓ, _, a3.hasType⟩ b5).map (f := VExpr.forallE _)
        fun h => ⟨_, .forallEDF a3.hasType h⟩
  | forallE a1 a2 a3 _ ih3 ih4 =>
    refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
    cases h2 with
    | forallE b1 b2 b3 b4 =>
      have e1 := hinv.sort_sort hΓ (ih3 hΓ b3)
      have hΓ' : OnCtx (_ :: _) (env.IsType U) := ⟨hΓ, _, a3.hasType⟩
      have e2 := hinv.sort_sort hΓ' (ih4 hΓ' b4)
      exact .single (.sortDF (l := .imax _ _) (l' := .imax _ _) ⟨a1, a2⟩ ⟨b1, b2⟩
        (VLevel.imax_congr e1 e2))
  | proj a1 a2 a3 a4 a5 a6 _ a8 a9 _ a11 a12 _ ih10 =>
    refine HasTypeStrong.chain_peel (fun h2 => ?_) h2
    cases h2 with
    | proj b1 b2 b3 b4 b5 b6 _ b8 b9 b10 _ b12 =>
      cases henv.ordered.projections_unique a1 b1
      have hmajor := ih10 hΓ b10
      have hsource := a9.defeq.trans (hmajor.symm.defeqDF b9.defeq).symm
      exact hinv.proj_fieldType hΓ a1 a11 a2 a3 a4 a5 a6 a8.hasType a12
        b2 b3 b4 b5 b6 b8.hasType b12 hsource hmajor

/-- A chain starting at a type of sort `u` collapses to one definitional equality at
`sort u`: each link is retyped at `sort u` using `uniq_chain` on its left endpoint and
`sort_sort`. -/
theorem TypeChain.collapse (henv : env.WF) (hinv : env.HeadInversion)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.TypeChain U Γ A B)
    (hA : env.HasType U Γ A (.sort u)) : env.IsDefEq U Γ A B (.sort u) := by
  have retype {X Y w} (hX : env.HasType U Γ X (.sort u))
      (h : env.IsDefEq U Γ X Y (.sort w)) : env.IsDefEq U Γ X Y (.sort u) := by
    have s1 := (hX.strong henv.ordered hΓ).hasType'.1
    have s2 := (h.strong henv.ordered hΓ).hasType'.1
    have e := hinv.sort_sort hΓ (s2.uniq_chain henv hinv hΓ s1)
    exact .defeqDF (.sortDF (h.sort_r henv.ordered hΓ) (hX.sort_r henv.ordered hΓ) e) h
  induction H with
  | single h => let ⟨_, h⟩ := h; exact retype hA h
  | tail _ h ih => let ⟨_, h⟩ := h; exact ih.trans (retype ih.hasType.2 h)

theorem IsDefEq.uniq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : Γ ⊢ e₁ ≡ e₂ : A) (h2 : Γ ⊢ e₂ ≡ e₃ : B) : ∃ u, Γ ⊢ A ≡ B : .sort u := by
  have hinv := henv.headInversion
  have H := HasTypeStrong.uniq_chain henv hinv hΓ
    (h1.strong henv.ordered hΓ).hasType'.2 (h2.strong henv.ordered hΓ).hasType'.1
  have ⟨_, hA⟩ := h1.isType henv.ordered hΓ
  exact ⟨_, H.collapse henv hinv hΓ hA⟩

theorem IsDefEq.uniqU (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEq U Γ e₁ e₂ A) (h2 : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEqU U Γ A B := let ⟨_, h⟩ := h1.uniq henv hΓ h2; ⟨_, h⟩

theorem isDefEq_iff (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    env.IsDefEq U Γ e₁ e₂ A ↔
    env.HasType U Γ e₁ A ∧ env.HasType U Γ e₂ A ∧ env.IsDefEqU U Γ e₁ e₂ := by
  refine ⟨fun h => ⟨h.hasType.1, h.hasType.2, _, h⟩, fun ⟨_, h2, _, h3⟩ => ?_⟩
  have ⟨_, h⟩ := h3.uniq henv hΓ h2
  exact h.defeqDF h3

theorem IsDefEq.trans_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEq U Γ e₁ e₂ A) (h₂ : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEq U Γ e₁ e₃ B := have ⟨_, h⟩ := h₁.uniq henv hΓ h₂; .trans (.defeqDF h h₁) h₂

theorem IsDefEq.trans_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEq U Γ e₁ e₂ A) (h₂ : env.IsDefEq U Γ e₂ e₃ B) :
    env.IsDefEq U Γ e₁ e₃ A := have ⟨_, h⟩ := h₁.uniq henv hΓ h₂; h₁.trans (.defeqDF (.symm h) h₂)

theorem IsDefEq.transU_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEqU U Γ e₁ e₂) (h₂ : env.IsDefEq U Γ e₂ e₃ A) :
    env.IsDefEq U Γ e₁ e₃ A := have ⟨_, h₁⟩ := h₁; .trans_r henv hΓ h₁ h₂

theorem IsDefEq.transU_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEq U Γ e₁ e₂ A) (h₂ : env.IsDefEqU U Γ e₂ e₃) :
    env.IsDefEq U Γ e₁ e₃ A := have ⟨_, h₂⟩ := h₂; .trans_l henv hΓ h₁ h₂

theorem IsDefEqU.defeqDF (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h₁ : env.IsDefEqU U Γ A B) (h₂ : env.IsDefEq U Γ e₁ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ B := by
  have ⟨_, h₁⟩ := h₁
  have ⟨_, hA⟩ := h₂.isType henv hΓ
  exact .defeqDF (hA.trans_l henv hΓ h₁) h₂

theorem IsDefEqU.of_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₁ A) :
    env.IsDefEq U Γ e₁ e₂ A := let ⟨_, h⟩ := h1; h2.trans_l henv hΓ h

theorem HasType.defeqU_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₁ A) :
    env.HasType U Γ e₂ A := (h1.of_l henv hΓ h2).hasType.2

theorem IsType.defeqU_l (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ A₁ A₂) (h2 : env.IsType U Γ A₁) :
    env.IsType U Γ A₂ := h2.imp fun _ h2 => h2.defeqU_l henv hΓ h1

theorem IsDefEqU.of_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.HasType U Γ e₂ A) :
    env.IsDefEq U Γ e₁ e₂ A := (h1.symm.of_l henv hΓ h2).symm

theorem HasType.defeqU_r (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ A₁ A₂) (h2 : env.HasType U Γ e A₁) :
    env.HasType U Γ e A₂ := h1.defeqDF henv hΓ h2

theorem IsDefEqU.trans (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ e₁ e₂) (h2 : env.IsDefEqU U Γ e₂ e₃) :
    env.IsDefEqU U Γ e₁ e₃ := h1.imp fun _ h1 => let ⟨_, h2⟩ := h2; h1.trans_l henv hΓ h2

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ' (env.IsType U)) in
/-- Legacy migration obligation, not an established structural principle.
The two-dependent-singleton model in `docs/inductives/STRENGTHENING.md`
challenges this unrestricted inverse direction: both endpoints can omit a
proof variable while an equality derivation uses it in intermediate terms.
Consumers need justified context transport; do not use this admission as
a premise of the new inversion/confluence foundation. -/
theorem IsDefEqU.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2 := by
  refine ⟨fun h => have := henv; have := hΓ; sorry, fun h => h.weakN henv W⟩

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    VExpr.WF env U Γ' (e.liftN n k) ↔ VExpr.WF env U Γ e := IsDefEqU.weakN_iff henv hΓ W

theorem IsDefEq.skips (henv : VEnv.WF env) (hΓ : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ')
    (H : env.IsDefEq U Γ' e₁ e₂ A) (h1 : e₁.Skips n k) (h2 : e₂.Skips n k) :
    ∃ B, env.IsDefEq U Γ' e₁ e₂ B ∧ B.Skips n k := by
  obtain ⟨e₁, rfl⟩ := VExpr.skips_iff_exists.1 h1
  obtain ⟨e₂, rfl⟩ := VExpr.skips_iff_exists.1 h2
  have ⟨_, H⟩ := (IsDefEqU.weakN_iff henv hΓ W).1 ⟨_, H⟩
  exact ⟨_, H.weakN henv W, .liftN⟩

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.weakN_iff' (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) ↔ env.IsDefEq U Γ e1 e2 A := by
  refine ⟨fun h => ?_, fun h => h.weakN henv W⟩
  have ⟨_, H⟩ := (IsDefEqU.weakN_iff henv hΓ' W).1 ⟨_, h⟩
  refine IsDefEqU.defeqDF henv hΓ ?_ H
  exact (IsDefEqU.weakN_iff henv hΓ' W).1 <| (H.weakN henv W).uniqU henv hΓ' h.symm

variable! (henv : VEnv.WF env) in
theorem _root_.Lean4Lean.OnCtx.weakN_inv
    (W : Ctx.LiftN n k Γ Γ') (H : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) := by
  induction W with
  | zero As h =>
    clear h
    induction As with
    | nil => exact H
    | cons A As ih => exact ih H.1
  | succ W ih =>
    let ⟨H1, _, H2⟩ := H
    exact ⟨ih H1, _, (IsDefEq.weakN_iff' henv H1 (ih H1) W).1 H2⟩

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEq.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) ↔ env.IsDefEq U Γ e1 e2 A :=
  IsDefEq.weakN_iff' henv hΓ' (hΓ'.weakN_inv henv W) W

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.HasType U Γ' (e.liftN n k) (A.liftN n k) ↔ env.HasType U Γ e A :=
  IsDefEq.weakN_iff henv hΓ' W

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsType.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsType U Γ' (A.liftN n k) ↔ env.IsType U Γ A :=
  exists_congr fun _ => HasType.weakN_iff henv hΓ' W (A := .sort _)

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.skips (W : Ctx.LiftN n k Γ Γ')
    (h1 : env.HasType U Γ' e A) (h2 : e.Skips n k) : ∃ B, env.HasType U Γ' e B ∧ B.Skips n k :=
  IsDefEq.skips henv hΓ' W h1 h2 h2

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEqU.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsDefEqU U Γ' (e1.lift' l) (e2.lift' l) ↔ env.IsDefEqU U Γ e1 e2 := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => simp [VExpr.lift'_depth_zero e, W.depth_zero e]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN,
      weakN_iff henv hΓ' W2, ih (hΓ'.weakN_inv henv W2) W1 Lift.depth_consN]

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEq.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsDefEq U Γ' (e1.lift' l) (e2.lift' l) (A.lift' l) ↔ env.IsDefEq U Γ e1 e2 A := by
  generalize e : l.depth = n
  induction n generalizing l Γ' with
  | zero => simp [VExpr.lift'_depth_zero e, W.depth_zero e]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    rw [Lift.consN_skip_eq, VExpr.lift'_comp, VExpr.lift'_comp, VExpr.lift'_comp,
      ← Lift.skipN_one, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN, VExpr.lift'_consN_skipN,
      weakN_iff henv hΓ' W2, ih (hΓ'.weakN_inv henv W2) W1 Lift.depth_consN]

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.HasType U Γ' (e.lift' l) (A.lift' l) ↔ env.HasType U Γ e A :=
  IsDefEq.weak'_iff henv hΓ' W

variable! (henv : VEnv.WF env) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsType.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsType U Γ' (e.lift' l) ↔ env.IsType U Γ e :=
  exists_congr fun _ => HasType.weak'_iff henv hΓ' W (A := .sort _)

variable! (henv : VEnv.WF env) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    VExpr.WF env U Γ' (e.lift' l) ↔ VExpr.WF env U Γ e := IsDefEqU.weak'_iff henv hΓ W

variable! (henv : VEnv.WF env) in
theorem _root_.Lean4Lean.OnCtx.weak'_inv
    (W : Ctx.Lift' ρ Γ Γ') (H : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) := by
  generalize e : ρ.depth = n
  induction n generalizing ρ Γ' with
  | zero => simp [W.depth_zero e, H]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    exact ih W1 (.weakN_inv henv W2 H) (by simp)
