import Lean4Lean.Theory.Typing.Strengthening.HybridNormal

/-! # Normal comparison with explicit typing modes

The Boolean index records the intended descent mode: `true` permits use of a
common endpoint type, while `false` compares independently typed non-proofs.
Application functions use independent mode and arguments use common-type mode.
An independent lambda recursively compares its domains in common-type mode and
its bodies independently. Eta is retained only in common-type mode.

Soundness and context conversion are established here. Descent, substitution
repair, and completeness are separate obligations; this file assumes none of them.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

/-- A mode-indexed comparison. `true` means common-type descent, `false` means
independent non-proof descent. The mode is a restriction on the certificate, not
an assertion that its arbitrary smaller-context endpoint types already align. -/
inductive BiNormal : Bool → Nat → List VExpr → VExpr → VExpr → Prop where
  | refl : Γ ⊢ e : A → BiNormal mode 0 Γ e e
  | sortDF : u.WF univs → v.WF univs → u ≈ v → BiNormal mode 0 Γ (.sort u) (.sort v)
  | constDF : Params.env.constants c = some ci →
      (∀ l ∈ ls, l.WF univs) → (∀ l ∈ ls', l.WF univs) → ls.length = ci.uvars →
      List.Forall₂ (· ≈ ·) ls ls' → BiNormal mode 0 Γ (.const c ls) (.const c ls')
  | appDF : Γ ⊢ f₁ : .forallE A B → Γ ⊢ f₂ : .forallE A B →
      Γ ⊢ a₁ : A → Γ ⊢ a₂ : A →
      BiNormal false nf Γ f₁ f₂ → BiNormal true na Γ a₁ a₂ →
      BiNormal mode (nf + na + 1) Γ (.app f₁ a₁) (.app f₂ a₂)
  | projDF : Γ ⊢ .proj S i m : T → BiNormal false n Γ m m' →
      BiNormal mode (n+1) Γ (.proj S i m) (.proj S i m')
  | lamIndependent : Γ ⊢ A₁ : .sort u → BiNormal true nd Γ A₁ A₂ →
      BiNormal false nb (A₁ :: Γ) b₁ b₂ →
      BiNormal false (nd + nb + 1) Γ (.lam A₁ b₁) (.lam A₂ b₂)
  | lamCommon : Γ ⊢ A ≡ A₁ : .sort u → Γ ⊢ A ≡ A₂ : .sort u →
      BiNormal true n (A :: Γ) b₁ b₂ →
      BiNormal true (n+1) Γ (.lam A₁ b₁) (.lam A₂ b₂)
  | forallEDF : Γ ⊢ A₁ : .sort u → BiNormal true nd Γ A₁ A₂ →
      A₁ :: Γ ⊢ B₁ : .sort v → BiNormal true nb (A₁ :: Γ) B₁ B₂ →
      BiNormal mode (nd + nb + 1) Γ (.forallE A₁ B₁) (.forallE A₂ B₂)
  | etaL : Γ ⊢ f : .forallE A B → BiNormal true n (A :: Γ) b (.app f.lift (.bvar 0)) →
      BiNormal true (n+2) Γ (.lam A b) f
  | etaR : Γ ⊢ f : .forallE A B → BiNormal true n (A :: Γ) (.app f.lift (.bvar 0)) b →
      BiNormal true (n+2) Γ f (.lam A b)
  | etaBoth : Γ ⊢ f : .forallE A B → Γ ⊢ g : .forallE A B →
      BiNormal true n (A :: Γ) (.app f.lift (.bvar 0)) (.app g.lift (.bvar 0)) →
      BiNormal true (n+2) Γ f g
  | proofIrrel : Γ ⊢ P : .sort .zero → Γ ⊢ a : P → Γ ⊢ b : P → BiNormal mode 0 Γ a b
  | promote : BiNormal false n Γ a b → BiNormal true (n+1) Γ a b

/-- Both modes have ordinary normal-equality soundness in their ambient context. -/
theorem BiNormal.toNormal (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : BiNormal mode n Γ a b) : NormalEqF true Γ a b := by
  induction H with
  | refl h => exact .refl h
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 => exact .appDF h1 h2 h3 h4 (ih1 hΓ) (ih2 hΓ)
  | projDF h _ ih => exact .projDF h (ih hΓ)
  | lamIndependent hA _ _ ihA ihb =>
    exact .lamDF hA (((ihA hΓ).defeq hΓ).of_l henv hΓ hA) (ihb ⟨hΓ, _, hA⟩)
  | lamCommon h1 h2 _ ih => exact .lamDF h1 h2 (ih ⟨hΓ, _, h1.hasType.1⟩)
  | forallEDF hA _ hB _ ihA ihB => exact .forallEDF hA (ihA hΓ) hB (ihB ⟨hΓ, _, hA⟩)
  | etaL hf _ ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    exact .etaL hf (ih ⟨hΓ, _, hA⟩)
  | etaR hf _ ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    exact .etaR hf (ih ⟨hΓ, _, hA⟩)
  | etaBoth hf hg _ ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    exact .etaBoth hf hg (ih ⟨hΓ, _, hA⟩)
  | proofIrrel hP ha hb => exact .proofIrrel hP ha hb
  | promote _ ih => exact ih hΓ

/-- Declarative soundness does not assert descent in either mode. -/
theorem BiNormal.defeq (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : BiNormal mode n Γ a b) : IsDefEqU Params.env univs Γ a b := (H.toNormal hΓ).defeq hΓ

/-- Conversion of the context preserves the mode and certificate index. -/
theorem BiNormal.defeqDFC (hΓ : OnCtx Γ₀ (Params.env.IsType univs))
    (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂) (H : BiNormal mode n Γ₁ a b) :
    BiNormal mode n Γ₂ a b := by
  induction H generalizing Γ₂ with
  | refl h => exact .refl (h.defeqDFC henv W)
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 => exact .constDF h1 h2 h3 h4 h5
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    exact .appDF (h1.defeqDFC henv W) (h2.defeqDFC henv W) (h3.defeqDFC henv W)
      (h4.defeqDFC henv W) (ih1 W) (ih2 W)
  | projDF h _ ih => exact .projDF (h.defeqDFC henv W) (ih W)
  | lamIndependent hA _ _ ihA ihb =>
    exact .lamIndependent (hA.defeqDFC henv W) (ihA W) (ihb (.succ W hA))
  | lamCommon h1 h2 _ ih =>
    exact .lamCommon (h1.defeqDFC henv W) (h2.defeqDFC henv W) (ih (.succ W h1.hasType.1))
  | forallEDF hA _ hB _ ihA ihB =>
    exact .forallEDF (hA.defeqDFC henv W) (ihA W) (hB.defeqDFC henv (.succ W hA))
      (ihB (.succ W hA))
  | etaL hf _ ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv (W.isType' hΓ)).forallE_inv henv
    exact .etaL (hf.defeqDFC henv W) (ih (.succ W hA))
  | etaR hf _ ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv (W.isType' hΓ)).forallE_inv henv
    exact .etaR (hf.defeqDFC henv W) (ih (.succ W hA))
  | etaBoth hf hg _ ih =>
    obtain ⟨⟨_, hA⟩, _⟩ := (hf.isType henv (W.isType' hΓ)).forallE_inv henv
    exact .etaBoth (hf.defeqDFC henv W) (hg.defeqDFC henv W) (ih (.succ W hA))
  | proofIrrel hP ha hb => exact .proofIrrel (hP.defeqDFC henv W) (ha.defeqDFC henv W) (hb.defeqDFC henv W)
  | promote _ ih => exact .promote (ih W)

/-- Eta-free recursive domain certificates embed in independent mode. -/
theorem DomainNormal.toBiNormal (H : DomainNormal n Γ a b) : ∃ m, BiNormal false m Γ a b := by
  induction H with
  | refl h => exact ⟨_, .refl h⟩
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    obtain ⟨_, H1⟩ := ih1; obtain ⟨_, H2⟩ := ih2
    exact ⟨_, .appDF h1 h2 h3 h4 H1 (.promote H2)⟩
  | projDF h _ ih => obtain ⟨_, H⟩ := ih; exact ⟨_, .projDF h H⟩
  | lamDF hA _ _ ihA ihb =>
    obtain ⟨_, HA⟩ := ihA; obtain ⟨_, Hb⟩ := ihb
    exact ⟨_, .lamIndependent hA (.promote HA) Hb⟩
  | forallEDF hA _ hB _ ihA ihB =>
    obtain ⟨_, HA⟩ := ihA; obtain ⟨_, HB⟩ := ihB
    exact ⟨_, .forallEDF hA (.promote HA) hB (.promote HB)⟩
  | proofIrrel hP ha hb => exact ⟨_, .proofIrrel hP ha hb⟩

end Lean4Lean.VEnv.Strengthening
