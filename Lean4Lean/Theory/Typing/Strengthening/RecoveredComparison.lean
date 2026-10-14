import Lean4Lean.Theory.Typing.Strengthening.TypeRecovery
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalDescent

/-! # Independent comparison using recovered endpoint types

A common-mode comparison may be used independently when its endpoint types can
be reconstructed and compared below. This is a finite certificate, allowing
application comparisons to use eta in function bodies without normalizing loops.
It does not assert recovery or comparison completeness for arbitrary equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- Extend the mode-indexed comparison at application nodes with finite type
recovery. `recover` compares the reconstructed types recursively; `sameType`
is its direct shared-type case. Ordinary normal comparisons enter through base. -/
inductive RecoveredComparison (D : Definitions) (depth : Nat) : Bool → List VExpr → VExpr → VExpr → Prop where
  | base : BiNormal mode n Γ a b → RecoveredComparison D depth mode Γ a b
  | app : Γ ⊢ f : .forallE A B → Γ ⊢ g : .forallE A B →
      Γ ⊢ a : A → Γ ⊢ b : A →
      RecoveredComparison D depth false Γ f g → RecoveredComparison D depth true Γ a b →
      RecoveredComparison D depth mode Γ (.app f a) (.app g b)
  | recover : TypeRecovery D depth Γ a T₁ → TypeRecovery D depth Γ b T₂ →
      RecoveredComparison D depth false Γ T₁ T₂ → RecoveredComparison D depth true Γ a b →
      RecoveredComparison D depth false Γ a b
  | sameType : TypeRecovery D depth Γ a T → TypeRecovery D depth Γ b T →
      RecoveredComparison D depth true Γ a b → RecoveredComparison D depth false Γ a b

/-- Every new constructor retains the original comparison's declarative
soundness. Recovery is needed for descent, not for this ambient consequence. -/
theorem RecoveredComparison.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : RecoveredComparison D depth mode Γ a b) : Γ ⊢ a ≡ b := by
  induction H with
  | base H => exact H.defeq hΓ
  | app hf _ ha _ _ _ ihf iha =>
    exact ⟨_, IsDefEq.appDF ((ihf hΓ).of_l henv hΓ hf) ((iha hΓ).of_l henv hΓ ha)⟩
  | recover _ _ _ _ _ ih | sameType _ _ _ ih => exact ih hΓ

/-- Independent certificates are also usable at a common type. -/
theorem RecoveredComparison.promote (H : RecoveredComparison D depth false Γ a b) :
    RecoveredComparison D depth true Γ a b := by
  cases H with
  | base H => exact .base (.promote H)
  | app hf hg ha hb Hf Ha => exact .app hf hg ha hb Hf Ha
  | recover _ _ _ H | sameType _ _ H => exact H

/-- Both modes descend. Recovery reconstructs the lower endpoint typings before
using the common-mode child. Its chosen type may be computed from the term; no
common lower type is assumed in independent mode. -/
theorem RecoveredComparison.descend
    (H : RecoveredComparison D depth mode Γ' (a.lift' ρ) (b.lift' ρ))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ha : Γ ⊢ a : A) (hb : Γ ⊢ b : B)
    (hmode : if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ a) : Γ ⊢ a ≡ b := by
  generalize hl : a.lift' ρ = l at H
  generalize hr : b.lift' ρ = r at H
  induction H generalizing ρ Γ a b A B with
  | base H =>
    subst hl hr
    exact BiNormal.descend _ W hΓ hΓ' ha hb H hmode
  | app hf hg hx hy Hf Hx ihf ihx =>
    obtain ⟨f, x, rfl, rfl, rfl⟩ := lift'_eq_app hl
    obtain ⟨g, y, rfl, rfl, rfl⟩ := lift'_eq_app hr
    by_cases hp : IsProof Γ (.app f x)
    · split at hmode
      · exact IsProof.descend hΓ hp ha hb hmode
      · exact (hmode hp).elim
    obtain ⟨_, _, hf₀, hx₀⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg₀, hy₀⟩ := hb.app_inv henv hΓ
    have hfg := ihf W hΓ hΓ' hf₀ hg₀ (not_isProof_fn hΓ hf₀ hx₀ hp) rfl rfl
    have hfPi := hfg.of_l henv hΓ hf₀
    obtain ⟨⟨_, hAA⟩, _⟩ := (hfPi.uniqU henv hΓ hg₀).forallE_inv henv hΓ
    have hxy := ihx W hΓ hΓ' hx₀ hy₀ ⟨_, hAA⟩ rfl rfl
    exact ⟨_, IsDefEq.appDF hfPi (hxy.of_l henv hΓ hx₀)⟩
  | recover Ra Rb HT Hab ihT ihab =>
    subst hl hr
    obtain ⟨T₁, hT₁, haT⟩ := Ra.descend heq hs W hΓ hΓ' ⟨_, ha⟩
    obtain ⟨T₂, hT₂, hbT⟩ := Rb.descend heq hs W hΓ hΓ' ⟨_, hb⟩
    obtain ⟨_, hT₁s⟩ := haT.isType henv hΓ
    obtain ⟨_, hT₂s⟩ := hbT.isType henv hΓ
    have hTT := ihT W hΓ hΓ' hT₁s hT₂s (not_isProof_of_sort hΓ hT₁s) hT₁.symm hT₂.symm
    exact ihab W hΓ hΓ' haT hbT hTT rfl rfl
  | sameType Ra Rb Hab ih =>
    subst hl hr
    obtain ⟨T₁, hT₁, haT⟩ := Ra.descend heq hs W hΓ hΓ' ⟨_, ha⟩
    obtain ⟨T₂, hT₂, hbT⟩ := Rb.descend heq hs W hΓ hΓ' ⟨_, hb⟩
    have hTT := lift'_inj.1 (hT₁.symm.trans hT₂)
    subst T₂
    obtain ⟨_, hT⟩ := haT.isType henv hΓ
    exact ih W hΓ hΓ' haT hbT ⟨_, hT⟩ rfl rfl


/-- Binder insertion preserves both modes of the base comparison. -/
theorem BiNormal.weakN (W : Ctx.LiftN k j Γ Γ') (H : BiNormal mode n Γ a b) :
    BiNormal mode n Γ' (a.liftN k j) (b.liftN k j) := by
  induction H generalizing j Γ' with
  | refl h => exact .refl (h.weakN henv W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.weakN henv W) (h2.weakN henv W) (h3.weakN henv W)
      (h4.weakN henv W) (ih1 W) (ih2 W)
  | projDF h _ ih => exact .projDF (h.weakN henv W) (ih W)
  | lamIndependent hA _ _ ihA ihb => exact .lamIndependent (hA.weakN henv W) (ihA W) (ihb W.succ)
  | lamCommon h1 h2 _ ih => exact .lamCommon (h1.weakN henv W) (h2.weakN henv W) (ih W.succ)
  | forallEDF hA _ hB _ ihA ihB =>
    exact .forallEDF (hA.weakN henv W) (ihA W) (hB.weakN henv W.succ) (ihB W.succ)
  | etaL hf _ ih =>
    refine .etaL (hf.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaR hf _ ih =>
    refine .etaR (hf.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN']
  | etaBoth hf hg _ ih =>
    refine .etaBoth (hf.weakN henv W) (hg.weakN henv W) ?_
    have := ih W.succ
    simp [liftN] at this; rwa [lift_liftN', lift_liftN']
  | proofIrrel hP ha hb => exact .proofIrrel (hP.weakN henv W) (ha.weakN henv W) (hb.weakN henv W)
  | promote _ ih => exact .promote (ih W)

/-- The application and recovery extensions also survive arbitrary finite binder
insertion. Computation and recovery depths are unchanged. -/
theorem RecoveredComparison.weakN (W : Ctx.LiftN k j Γ Γ')
    (H : RecoveredComparison D depth mode Γ a b) :
    RecoveredComparison D depth mode Γ' (a.liftN k j) (b.liftN k j) := by
  induction H generalizing j Γ' with
  | base H => exact .base (H.weakN W)
  | app hf hg ha hb _ _ ihf iha =>
    exact .app (hf.weakN henv W) (hg.weakN henv W) (ha.weakN henv W) (hb.weakN henv W) (ihf W) (iha W)
  | recover Ra Rb _ _ ihT ihab => exact .recover (Ra.weakN W) (Rb.weakN W) (ihT W) (ihab W)
  | sameType Ra Rb _ ih => exact .sameType (Ra.weakN W) (Rb.weakN W) (ih W)

end Lean4Lean.VEnv.Strengthening
