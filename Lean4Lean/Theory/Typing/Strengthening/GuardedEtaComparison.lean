import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaEnvironment

/-! # Guarded recursive loops resist bidirectional beta-only comparison

An independent comparison cannot relate an unexpanded diagonal to a guarded
recursive lambda. Common-mode eta can add application arguments, but eventually
comparison of their function heads encounters this independent obstruction.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments

/-- An application spine whose head is the unexpanded diagonal. -/
inductive BadFn (c : Name) : VExpr → Prop where
  | diagonal : BadFn c (diagonal c)
  | app : BadFn c f → BadFn c (.app f a)

theorem BadFn.liftN (H : BadFn c e) : BadFn c (e.liftN n k) := by
  induction H with
  | diagonal =>
    simpa only [GuardedEta.diagonal, domain, selfBody, VExpr.liftN, liftVar,
      Nat.zero_lt_succ, if_true] using (BadFn.diagonal (c := c))
  | app _ ih => exact .app ih

theorem BadFn.not_guarded (H : BadFn c e) : ¬ Guarded c e := by
  induction H with
  | diagonal => exact diagonal_not_guarded
  | app _ ih => intro H; cases H with | app Hf _ => exact ih Hf

private theorem Guarded.lam_body (H : Guarded c (.lam A b)) : Guarded c b := by
  cases H with
  | lamProp hb => exact hb
  | lamDomain hb => exact .lamProp hb

section
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

/-- Independent certificates cannot remove a guarding eta binder. The recursive
constant cannot align with Prop, and comparing the lambda bodies has no eta rule. -/
theorem no_independent
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero))
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : BiNormal false n Γ e out)
    (hbad : BadFn c e) (hg : Guarded c out) (hn : ¬ IsProof Γ e) : False := by
  generalize hm : false = mode at H
  induction H with
  | refl _ => exact hbad.not_guarded hg
  | sortDF | constDF | projDF | forallEDF => cases hbad
  | appDF hf _ ha _ _ _ ihf _ =>
    cases hbad with
    | app hbad =>
      cases hg with
      | app hgf _ => exact ihf hΓ hbad hgf (not_isProof_fn hΓ hf ha hn) rfl
  | lamIndependent hD HD HB _ _ =>
    cases hbad
    cases hg with
    | lamProp _ =>
      have he := HD.defeq hΓ
      have hPi := he.symm.trans henv hΓ ⟨_, hδ _⟩
      exact hPi.sort_forallE_inv henv hΓ
    | lamDomain _ =>
      cases HB with
      | proofIrrel hP hb _ => exact hn (IsProof.lam hΓ hD ⟨_, hb, hP⟩)
  | proofIrrel hP he _ => exact hn ⟨_, he, hP⟩
  | lamCommon | etaL | etaR | etaBoth | promote => cases hm

/-- Common-mode eta only extends an application spine. Its independent function
comparison must still encounter the unexpanded diagonal. -/
theorem no_common
    (hδ : ∀ Γ, Γ ⊢ domain c ≡ domainValue c : .sort (.succ .zero))
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (H : BiNormal true n Γ e out)
    (hbad : BadFn c e) (hl : ¬ IsLam e) (hg : Guarded c out)
    (hn : ¬ IsProof Γ e) : False := by
  generalize hm : true = mode at H
  induction H with
  | refl _ => exact hbad.not_guarded hg
  | sortDF | constDF | projDF | forallEDF => cases hbad
  | appDF hf _ ha _ HF _ _ _ =>
    cases hbad with
    | app hbad =>
      cases hg with
      | app hgf _ => exact no_independent hδ hΓ HF hbad hgf (not_isProof_fn hΓ hf ha hn)
  | lamIndependent | lamCommon | etaL => exact hl trivial
  | etaR hf HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    exact ih ⟨hΓ, _, hA⟩ (.app hbad.liftN) (by simp [IsLam]) hg.lam_body
      (fun hp => hn (IsProof.of_etaBody hΓ hf hp)) rfl
  | etaBoth hf _ HB ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    exact ih ⟨hΓ, _, hA⟩ (.app hbad.liftN) (by simp [IsLam]) (.app hg.liftN .var)
      (fun hp => hn (IsProof.of_etaBody hΓ hf hp)) rfl
  | proofIrrel hP he _ => exact hn ⟨_, he, hP⟩
  | promote H _ => exact no_independent hδ hΓ H hbad hg hn

end
end Lean4Lean.VEnv.Strengthening.GuardedEta
