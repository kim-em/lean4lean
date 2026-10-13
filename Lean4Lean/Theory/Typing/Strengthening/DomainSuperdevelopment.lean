import Lean4Lean.Theory.Typing.Strengthening.DomainNormalAlgebra
import Lean4Lean.Theory.Typing.Strengthening.Superdevelopments

/-! # Superdevelopment preserves recursive domain comparisons

The heterogeneous substitution theorem tracks domain certificates through a matched
beta contraction, including redexes created at substituted function variables.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

private theorem contractApp_simAt (hΓ : OnCtx Γ (Params.env.IsType univs)) (f a : VExpr) :
    Params.env.SimAt univs Γ (.app f a) (contractApp f a) :=
  (contractApp_betaRed f a).simAt henv.orderedStrong henv.betaSubjectReduction hΓ

/-- Contracting a pair of related applications preserves the recorded domain
comparisons. Proof functions are handled by proof irrelevance at the result type. -/
theorem DomainNormal.contractApp (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : .forallE A B) (hf' : Γ ⊢ f' : .forallE A B)
    (ha : Γ ⊢ a : A) (ha' : Γ ⊢ a' : A)
    (Hf : DomainNormal nf Γ f f') (Ha : DomainNormal na Γ a a') :
    ∃ n, DomainNormal n Γ (contractApp f a) (contractApp f' a') := by
  have whole := DomainNormal.appDF hf hf' ha ha' Hf Ha
  cases Hf with
  | refl h =>
    cases f with
    | lam D b =>
      obtain ⟨⟨u, hD⟩, _, hb⟩ := hf.lam_inv henv hΓ
      obtain ⟨⟨_, hAD⟩, _⟩ := (hf.uniqU henv hΓ (HasType.lam hD hb)).forallE_inv henv hΓ
      exact DomainNormal.instN_r (by exact ⟨hΓ, u, hD⟩) (hAD.defeq ha) Ha .zero hb
    | bvar | sort | const | app | forallE | proj => exact ⟨_, whole⟩
  | lamDF hD _ Hb =>
    obtain ⟨⟨_, hd⟩, _, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨⟨_, hAD⟩, _⟩ := (hf.uniqU henv hΓ (HasType.lam hd hb)).forallE_inv henv hΓ
    exact DomainNormal.instN_lr (by exact ⟨hΓ, _, hD⟩) (hAD.defeq ha) Ha .zero Hb
  | proofIrrel hP hfl hfr =>
    obtain ⟨Q, happ, hQ⟩ := IsProof.app_fn hΓ hf ha ⟨_, hfl, hP⟩
    have happ' := ((whole.defeq hΓ).of_l henv hΓ happ).hasType.2
    exact ⟨_, .proofIrrel hQ ((contractApp_simAt hΓ _ _ _ happ).hasType.2)
      ((contractApp_simAt hΓ _ _ _ happ').hasType.2)⟩
  | sortDF | constDF | appDF | projDF | forallEDF => exact ⟨_, whole⟩

/-- One structural superdevelopment preserves recursively certified comparisons.
This includes the downward-created redexes left uncontracted by the pass. -/
theorem DomainNormal.superdevelop (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : DomainNormal n Γ a b) :
    ∃ m, DomainNormal m Γ (superdevelop a) (superdevelop b) := by
  induction H with
  | refl h => exact ⟨_, .refl ((superdevelop_simAt henv hΓ _ _ h).hasType.2)⟩
  | sortDF h1 h2 h3 => exact ⟨_, .sortDF h1 h2 h3⟩
  | constDF h1 h2 h3 h4 h5 => exact ⟨_, .constDF h1 h2 h3 h4 h5⟩
  | appDF h1 h2 h3 h4 _ _ ih1 ih2 =>
    obtain ⟨_, hf⟩ := ih1 hΓ
    obtain ⟨_, ha⟩ := ih2 hΓ
    exact hf.contractApp hΓ ((superdevelop_simAt henv hΓ _ _ h1).hasType.2)
      ((superdevelop_simAt henv hΓ _ _ h2).hasType.2)
      ((superdevelop_simAt henv hΓ _ _ h3).hasType.2)
      ((superdevelop_simAt henv hΓ _ _ h4).hasType.2) ha
  | projDF h _ ih =>
    obtain ⟨_, hm⟩ := ih hΓ
    have hh := (superdevelop_simAt henv hΓ _ _ h).hasType.2
    exact ⟨_, .projDF hh hm⟩
  | lamDF hA _ _ ihA ihb =>
    obtain ⟨_, HA⟩ := ihA hΓ
    obtain ⟨_, Hb⟩ := ihb ⟨hΓ, _, hA⟩
    have hAA := superdevelop_simAt henv hΓ _ _ hA
    exact ⟨_, .lamDF hAA.hasType.2 HA (Hb.defeqDFC (.succ .zero hAA))⟩
  | forallEDF hA _ hB _ ihA ihB =>
    obtain ⟨_, HA⟩ := ihA hΓ
    obtain ⟨_, HB⟩ := ihB ⟨hΓ, _, hA⟩
    have hAA := superdevelop_simAt henv hΓ _ _ hA
    have hb := (superdevelop_simAt henv (by exact ⟨hΓ, _, hA⟩) _ _ hB).hasType.2
    exact ⟨_, .forallEDF hAA.hasType.2 HA (hb.defeqDFC henv (.succ .zero hAA))
      (HB.defeqDFC (.succ .zero hAA))⟩
  | proofIrrel hP ha hb =>
    exact ⟨_, .proofIrrel hP ((superdevelop_simAt henv hΓ _ _ ha).hasType.2)
      ((superdevelop_simAt henv hΓ _ _ hb).hasType.2)⟩

end Lean4Lean.VEnv.Strengthening
