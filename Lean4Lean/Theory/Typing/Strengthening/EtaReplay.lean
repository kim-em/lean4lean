import Lean4Lean.Theory.Typing.Strengthening.EtaPostponement

/-! # Replay through eta-normal expansions

Direction B3 (`docs/inductives/STRENGTHENING_B3_LOG.md`), step 4: the infrastructure for the proof
of `EtaReplayNE`. Descent of eta-free parallel steps along any lift (`Ctx.Lift'`), peeling one
insertion at a time with well-formed intermediate contexts. -/

namespace Lean4Lean.VEnv.StrengtheningEtaReplay
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal VEnv.StrengtheningEtaPostponement

section
open VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => Params.env.HasType univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => Params.env.IsDefEq univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => Params.env.IsDefEqU univs Γ e1 e2

/-! ## Peeling one insertion off a lift, with well-formed intermediate context -/

theorem Ctx.Lift'.peel {l : Lift} : ∀ {k : Nat} {Γ₁ Γ₃ : List VExpr},
    Ctx.Lift' (Lift.consN (.skip l) k) Γ₁ Γ₃ → OnCtx Γ₁ (Params.env.IsType univs) →
    OnCtx Γ₃ (Params.env.IsType univs) →
    ∃ Γ₂, Ctx.Lift' (Lift.consN l k) Γ₁ Γ₂ ∧ Ctx.LiftN 1 k Γ₂ Γ₃ ∧
      OnCtx Γ₂ (Params.env.IsType univs) := by
  intro k
  induction k with
  | zero =>
    intro Γ₁ Γ₃ H hΓ₁ hΓ₃
    cases H with
    | skip H => exact ⟨_, H, .one, hΓ₃.1⟩
  | succ k ih =>
    intro Γ₁ Γ₃ H hΓ₁ hΓ₃
    cases H with
    | @cons l' Γ Γ' A H =>
      obtain ⟨Γ₂, h1, h2, hΓ₂⟩ := ih H hΓ₁.1 hΓ₃.1
      refine ⟨A.lift' (Lift.consN l k) :: Γ₂, .cons h1, ?_, hΓ₂, ?_⟩
      · have h2' := h2
        simp only [Ctx.liftN_iff_lift'] at h2' ⊢
        simpa [← VExpr.lift'_comp, ← Lift.consN_comp] using h2'.cons (A := lift' A (.consN l k))
      · obtain ⟨u, hA⟩ := hΓ₁.2
        exact ⟨u, hA.weak' henv.ordered h1⟩

omit [Params] in
theorem lift'_consN_skip (e : VExpr) (l : Lift) (k : Nat) :
    e.lift' (Lift.consN (.skip l) k) = (e.lift' (Lift.consN l k)).liftN 1 k := by
  rw [Lift.consN_skip_eq, lift'_comp]
  exact lift'_consN_skipN (n := 1)

/-! ## Descent of eta-free parallel steps along any lift -/

theorem ParRed.descend' (hTF : TypedFrontN Params.env) (hcase : CaseRedexDescends)
    (hcv : ∀ {p : Pattern} {r : p.RHS × p.Check}, Pat p r → CheckVars r.2) :
    ∀ (n : Nat) {l : Lift} {Γ₀ Γ₁ : List VExpr} {e T out : VExpr}, l.depth = n →
      Ctx.Lift' l Γ₀ Γ₁ → OnCtx Γ₀ (Params.env.IsType univs) → OnCtx Γ₁ (Params.env.IsType univs) →
      Γ₀ ⊢ e : T → ParRed Γ₁ (e.lift' l) out → ∃ e', out = e'.lift' l ∧ ParRed Γ₀ e e' := by
  intro n
  induction n with
  | zero =>
    intro l Γ₀ Γ₁ e T out hd W hΓ₀ hΓ₁ he H
    cases W.depth_zero hd
    rw [lift'_depth_zero hd] at H
    exact ⟨out, (lift'_depth_zero hd).symm, H⟩
  | succ n ih =>
    intro l Γ₀ Γ₁ e T out hd W hΓ₀ hΓ₁ he H
    obtain ⟨l', k, hd', rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W₁, W₂, hΓ₂⟩ := Ctx.Lift'.peel W hΓ₀ hΓ₁
    rw [lift'_consN_skip] at H
    obtain ⟨e₁, rfl, H₁⟩ := ParRed.descend hTF hcase hcv W₂ hΓ₂ hΓ₁ (he.weak' henv.ordered W₁) H
    obtain ⟨e', rfl, H'⟩ := ih (by simpa using hd') W₁ hΓ₀ hΓ₂ he H₁
    exact ⟨e', (lift'_consN_skip e' l' k).symm, H'⟩

theorem DeltaPar.descend' (hTF : TypedFrontN Params.env) (hunfold : UnfoldingCheckDescends) :
    ∀ (n : Nat) {l : Lift} {Γ₀ Γ₁ : List VExpr} {e T out : VExpr}, l.depth = n →
      Ctx.Lift' l Γ₀ Γ₁ → OnCtx Γ₀ (Params.env.IsType univs) → OnCtx Γ₁ (Params.env.IsType univs) →
      Γ₀ ⊢ e : T → DeltaPar Γ₁ (e.lift' l) out → ∃ e', out = e'.lift' l ∧ DeltaPar Γ₀ e e' := by
  intro n
  induction n with
  | zero =>
    intro l Γ₀ Γ₁ e T out hd W hΓ₀ hΓ₁ he H
    cases W.depth_zero hd
    rw [lift'_depth_zero hd] at H
    exact ⟨out, (lift'_depth_zero hd).symm, H⟩
  | succ n ih =>
    intro l Γ₀ Γ₁ e T out hd W hΓ₀ hΓ₁ he H
    obtain ⟨l', k, hd', rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W₁, W₂, hΓ₂⟩ := Ctx.Lift'.peel W hΓ₀ hΓ₁
    rw [lift'_consN_skip] at H
    obtain ⟨e₁, rfl, H₁⟩ := DeltaPar.descend hTF hunfold W₂ hΓ₂ hΓ₁ (he.weak' henv.ordered W₁) H
    obtain ⟨e', rfl, H'⟩ := ih (by simpa using hd') W₁ hΓ₀ hΓ₂ he H₁
    exact ⟨e', (lift'_consN_skip e' l' k).symm, H'⟩

end

end Lean4Lean.VEnv.StrengtheningEtaReplay
