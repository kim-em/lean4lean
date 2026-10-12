import Lean4Lean.Theory.Typing.HeadInversion
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.CanonicalEq

/-! # Unique typing and its consequences.

Uniqueness of types for well-formed environments: the chain-level uniqueness and its collapse
to a single definitional equality are proved in `HeadInjectivity/Uniqueness.lean`
(`HasTypeStrong.uniq_chain_of_chainHeadInjectivity`,
`TypeChain.collapse_of_chainHeadInjectivity`) from the model's chain-level head injectivity
(`VEnv.WF.chainHeadInjectivity`). This file states the public consequences. -/

namespace Lean4Lean
namespace VEnv

variable {env : VEnv} {U : Nat}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env U Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq env U Γ e1 e2 A

theorem IsDefEq.uniq (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : Γ ⊢ e₁ ≡ e₂ : A) (h2 : Γ ⊢ e₂ ≡ e₃ : B) : ∃ u, Γ ⊢ A ≡ B : .sort u := by
  have core := henv.chainHeadInjectivity
  have H := HasTypeStrong.uniq_chain_of_chainHeadInjectivity henv core hΓ
    (h1.strong henv hΓ).hasType'.2 (h2.strong henv hΓ).hasType'.1
  have ⟨_, hA⟩ := h1.isType henv.ordered hΓ
  exact ⟨_, H.collapse_of_chainHeadInjectivity henv core hΓ hA⟩

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

/-! ## Strengthening

Context strengthening for definitional equality, sharpened from master's statement by the
hypothesis that the environment has the prelude's canonical `Eq` (`VEnv.HasCanonicalEq`). It is
the one strengthening principle the checker verification uses (through `VEnv.Strengthening`).
Open proof (`OPEN_PROOFS.md`): master's statement without `HasCanonicalEq` was argued false for
well-formed environments without `Eq` (PR #53, `Tests/CacheScope.lean`); the sharpened statement
is not known to be false. -/

/-- Context strengthening for definitional equality: an equation between two lifted expressions
in a context extended by `n` binders (inserted below `k` binders) already holds in the smaller
context. -/
def Strengthening (env : VEnv) : Prop :=
  ∀ ⦃U n k Γ Γ' e1 e2⦄, Ctx.LiftN n k Γ Γ' → OnCtx Γ' (env.IsType U) →
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) → env.IsDefEqU U Γ e1 e2

/-- Context strengthening in every well-formed extension of `env`. This is monotone in `env`,
and it is what the checker verification carries through the environments it checks in. -/
def StrengtheningAbove (env : VEnv) : Prop :=
  ∀ ⦃env'⦄, env ≤ env' → env'.WF → env'.Strengthening

theorem StrengtheningAbove.mono {env env' : VEnv} (hle : env ≤ env')
    (h : env.StrengtheningAbove) : env'.StrengtheningAbove :=
  fun _ hle' hwf => h (hle.trans hle') hwf

variable! (henv : VEnv.WF env) (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem IsDefEqU.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2 := by
  refine ⟨fun _ => sorry, fun h => h.weakN henv W⟩

/-- Every well-formed environment with canonical `Eq` admits context strengthening
(`IsDefEqU.weakN_iff`). -/
theorem WF.strengthening (henv : env.WF) (heq : env.HasCanonicalEq) : env.Strengthening :=
  fun _ _ _ _ _ _ _ W hΓ h => (IsDefEqU.weakN_iff henv heq hΓ W).1 h

/-- Canonical `Eq` gives context strengthening in every well-formed extension. -/
theorem _root_.Lean4Lean.VEnv.HasCanonicalEq.strengtheningAbove (heq : env.HasCanonicalEq) :
    env.StrengtheningAbove :=
  fun _ hle hwf => hwf.strengthening (heq.mono hle)

/-- Context strengthening in every well-formed environment without canonical `Eq`: the part of
master's statement of `IsDefEqU.weakN_iff` that the sharpened statement no longer asserts. It is
argued false (`OPEN_PROOFS.md`, `Tests/CacheScope.lean`); it appears only as the hypothesis of
the fresh-replay theorems, which check the prelude's declarations before `Eq` exists. -/
def EqFreeStrengthening : Prop :=
  ∀ env : VEnv, env.WF → ¬ env.HasCanonicalEq → env.Strengthening

/-- With `EqFreeStrengthening`, every environment admits strengthening above it: the
environments with canonical `Eq` by `IsDefEqU.weakN_iff`, the others by the hypothesis. -/
theorem EqFreeStrengthening.strengtheningAbove (h : EqFreeStrengthening) (env : VEnv) :
    env.StrengtheningAbove := fun env' _ hwf =>
  open Classical in
  if heq : env'.HasCanonicalEq then hwf.strengthening heq else h env' hwf heq

/-- Strengthening in both directions, from `Strengthening`. -/
theorem Strengthening.weakN_iff (henv : VEnv.WF env) (hs : env.Strengthening)
    (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2 :=
  ⟨hs W hΓ, fun h => h.weakN henv W⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    VExpr.WF env U Γ' (e.liftN n k) ↔ VExpr.WF env U Γ e := hs.weakN_iff henv hΓ W

theorem IsDefEq.skips (henv : VEnv.WF env) (hs : env.Strengthening)
    (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ')
    (H : env.IsDefEq U Γ' e₁ e₂ A) (h1 : e₁.Skips n k) (h2 : e₂.Skips n k) :
    ∃ B, env.IsDefEq U Γ' e₁ e₂ B ∧ B.Skips n k := by
  obtain ⟨e₁, rfl⟩ := VExpr.skips_iff_exists.1 h1
  obtain ⟨e₂, rfl⟩ := VExpr.skips_iff_exists.1 h2
  have ⟨_, H⟩ := hs W hΓ ⟨_, H⟩
  exact ⟨_, H.weakN henv W, .liftN⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) (hΓ : OnCtx Γ (env.IsType U)) in
theorem IsDefEq.weakN_iff' (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) ↔ env.IsDefEq U Γ e1 e2 A := by
  refine ⟨fun h => ?_, fun h => h.weakN henv W⟩
  have ⟨_, H⟩ := (hs W hΓ') ⟨_, h⟩
  refine IsDefEqU.defeqDF henv hΓ ?_ H
  exact (hs W hΓ') <| (H.weakN henv W).uniqU henv hΓ' h.symm

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
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
    exact ⟨ih H1, _, (IsDefEq.weakN_iff' henv hs H1 (ih H1) W).1 H2⟩

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsDefEq.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsDefEq U Γ' (e1.liftN n k) (e2.liftN n k) (A.liftN n k) ↔ env.IsDefEq U Γ e1 e2 A :=
  IsDefEq.weakN_iff' henv hs hΓ' (hΓ'.weakN_inv henv hs W) W

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.HasType U Γ' (e.liftN n k) (A.liftN n k) ↔ env.HasType U Γ e A :=
  IsDefEq.weakN_iff henv hs hΓ' W

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsType.weakN_iff (W : Ctx.LiftN n k Γ Γ') :
    env.IsType U Γ' (A.liftN n k) ↔ env.IsType U Γ A :=
  exists_congr fun _ => HasType.weakN_iff henv hs hΓ' W (A := .sort _)

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.skips (W : Ctx.LiftN n k Γ Γ')
    (h1 : env.HasType U Γ' e A) (h2 : e.Skips n k) : ∃ B, env.HasType U Γ' e B ∧ B.Skips n k :=
  IsDefEq.skips henv hs hΓ' W h1 h2 h2

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
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
      Strengthening.weakN_iff henv hs hΓ' W2, ih (hΓ'.weakN_inv henv hs W2) W1 Lift.depth_consN]

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
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
      weakN_iff henv hs hΓ' W2, ih (hΓ'.weakN_inv henv hs W2) W1 Lift.depth_consN]

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem HasType.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.HasType U Γ' (e.lift' l) (A.lift' l) ↔ env.HasType U Γ e A :=
  IsDefEq.weak'_iff henv hs hΓ' W

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ' : OnCtx Γ' (env.IsType U)) in
theorem IsType.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    env.IsType U Γ' (e.lift' l) ↔ env.IsType U Γ e :=
  exists_congr fun _ => HasType.weak'_iff henv hs hΓ' W (A := .sort _)

variable! (henv : VEnv.WF env) (hs : env.Strengthening) (hΓ : OnCtx Γ' (env.IsType U)) in
theorem _root_.Lean4Lean.VExpr.WF.weak'_iff (W : Ctx.Lift' l Γ Γ') :
    VExpr.WF env U Γ' (e.lift' l) ↔ VExpr.WF env U Γ e := IsDefEqU.weak'_iff henv hs hΓ W

variable! (henv : VEnv.WF env) (hs : env.Strengthening) in
theorem _root_.Lean4Lean.OnCtx.weak'_inv
    (W : Ctx.Lift' ρ Γ Γ') (H : OnCtx Γ' (env.IsType U)) : OnCtx Γ (env.IsType U) := by
  generalize e : ρ.depth = n
  induction n generalizing ρ Γ' with
  | zero => simp [W.depth_zero e, H]
  | succ n ih =>
    obtain ⟨l, k, rfl, rfl⟩ := Lift.depth_succ e
    have ⟨Γ₁, W1, W2⟩ := W.of_cons_skip
    exact ih W1 (.weakN_inv henv hs W2 H) (by simp)

private theorem isType_wrapForalls_inv {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {domains Γ : List VExpr} {body : VExpr}, OnCtx Γ (env.IsType U) →
      env.IsType U Γ (VExpr.wrapForalls domains body) →
      OnCtx (domains.reverse ++ Γ) (env.IsType U)
  | [], _, _, hΓ, _ => hΓ
  | d :: ds, Γ, body, hΓ, H => by
    have hinv := IsType.forallE_inv henv H
    have := isType_wrapForalls_inv henv (domains := ds) (Γ := d :: Γ) (body := body)
      ⟨hΓ, hinv.1⟩ hinv.2
    simpa [List.reverse_cons, List.append_assoc] using this

/-- Close the open header form: a well-formed type definitionally equal to a
telescope whose body is definitionally a sort in the telescope's scope is
definitionally the telescope ending in that sort. -/
theorem IsDefEq.close_sort_header {env : VEnv} {U : Nat} {T A body : VExpr}
    {domains : List VExpr} {level : VLevel}
    (henv : env.WF) (hT : env.IsType U [] T)
    (h1 : env.IsDefEq U [] T (VExpr.wrapForalls domains body) A)
    (h2 : env.IsDefEq U domains.reverse body (.sort level) (.sort (.succ level))) :
    env.IsDefEqU U [] T (VExpr.wrapForalls domains (.sort level)) := by
  have hW : env.IsType U [] (VExpr.wrapForalls domains body) :=
    hT.defeqU_l henv trivial ⟨A, h1⟩
  have hctx := isType_wrapForalls_inv henv.ordered (Γ := []) trivial hW
  obtain ⟨_, hw⟩ := VExpr.wrapForalls_defeq (Γ := []) (by simpa using hctx) (by simpa using h2)
  exact IsDefEqU.trans henv trivial ⟨_, h1⟩ ⟨_, hw⟩
