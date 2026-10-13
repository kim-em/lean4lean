import Lean4Lean.Theory.Typing.Strengthening.DomainNormalAlgebra

/-! # Matching finite beta reductions across certified comparisons

This is a reduction-compatibility theorem for recursive domain comparisons, not
completeness for the full calculus. It includes beta reduction inside annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

private theorem beta_simAt (hΓ : OnCtx Γ (Params.env.IsType univs)) (R : BetaRed e e') :
    Params.env.SimAt univs Γ e e' :=
  R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ

private theorem DomainNormal.beta_proof (hΓ : OnCtx Γ (Params.env.IsType univs))
    (R : BetaRed e e') (H : DomainNormal n Γ e f) (hp : IsProof Γ e) :
    ∃ m, DomainNormal m Γ e' f := by
  obtain ⟨P, he, hP⟩ := hp
  exact ⟨_, .proofIrrel hP ((beta_simAt hΓ R _ he).hasType.2)
    (((H.defeq hΓ).of_l henv hΓ he).hasType.2)⟩

/-- Every finite beta reduction on the left can be matched by a finite beta
reduction on the right, retaining recursive lambda-domain certificates. The proof
uses heterogeneous substitution for matched redexes and includes annotation reduction. -/
theorem DomainNormal.beta_simulation (hΓ : OnCtx Γ (Params.env.IsType univs))
    (he : Γ ⊢ e : T) (H : DomainNormal n Γ e f) (R : BetaRed e e') :
    ∃ f', BetaRed f f' ∧ ∃ m, DomainNormal m Γ e' f' := by
  induction R generalizing Γ n f T with
  | refl => exact ⟨_, .refl, _, H⟩
  | trans R1 R2 ih1 ih2 =>
    obtain ⟨f1, Rf1, _, H1⟩ := ih1 hΓ he H
    obtain ⟨f2, Rf2, _, H2⟩ := ih2 hΓ ((beta_simAt hΓ R1 _ he).hasType.2) H1
    exact ⟨f2, Rf1.trans Rf2, _, H2⟩
  | app Rf Ra ihf iha =>
    cases H with
    | refl => exact ⟨_, .app Rf Ra, _, .refl ((beta_simAt hΓ (.app Rf Ra) _ he).hasType.2)⟩
    | appDF hf hf' ha ha' Hf Ha =>
      obtain ⟨f2, Rf2, _, HF⟩ := ihf hΓ hf Hf
      obtain ⟨a2, Ra2, _, HA⟩ := iha hΓ ha Ha
      exact ⟨_, .app Rf2 Ra2, _, .appDF ((beta_simAt hΓ Rf _ hf).hasType.2)
        ((beta_simAt hΓ Rf2 _ hf').hasType.2) ((beta_simAt hΓ Ra _ ha).hasType.2)
        ((beta_simAt hΓ Ra2 _ ha').hasType.2) HF HA⟩
    | proofIrrel hP hl hr =>
      exact ⟨_, .refl, DomainNormal.beta_proof hΓ (.app Rf Ra) (.proofIrrel hP hl hr) ⟨_, hl, hP⟩⟩
  | lam RD Rb ihD ihb =>
    cases H with
    | refl => exact ⟨_, .lam RD Rb, _, .refl ((beta_simAt hΓ (.lam RD Rb) _ he).hasType.2)⟩
    | lamDF hD HD Hb =>
      obtain ⟨⟨_, _⟩, _, hb⟩ := he.lam_inv henv hΓ
      obtain ⟨D2, RD2, _, HD2⟩ := ihD hΓ hD HD
      obtain ⟨b2, Rb2, _, HB2⟩ := ihb (by exact ⟨hΓ, _, hD⟩) hb Hb
      have hDD := beta_simAt hΓ RD _ hD
      exact ⟨_, .lam RD2 Rb2, _, .lamDF hDD.hasType.2 HD2
        (HB2.defeqDFC (.succ .zero hDD))⟩
    | proofIrrel hP hl hr =>
      exact ⟨_, .refl, DomainNormal.beta_proof hΓ (.lam RD Rb) (.proofIrrel hP hl hr) ⟨_, hl, hP⟩⟩
  | forallE RD RB ihD ihB =>
    cases H with
    | refl => exact ⟨_, .forallE RD RB, _, .refl ((beta_simAt hΓ (.forallE RD RB) _ he).hasType.2)⟩
    | forallEDF hD HD hB HB =>
      obtain ⟨D2, RD2, _, HD2⟩ := ihD hΓ hD HD
      obtain ⟨B2, RB2, _, HB2⟩ := ihB (by exact ⟨hΓ, _, hD⟩) hB HB
      have hDD := beta_simAt hΓ RD _ hD
      have hb := (beta_simAt (by exact ⟨hΓ, _, hD⟩) RB _ hB).hasType.2
      exact ⟨_, .forallE RD2 RB2, _, .forallEDF hDD.hasType.2 HD2
        (hb.defeqDFC henv (.succ .zero hDD)) (HB2.defeqDFC (.succ .zero hDD))⟩
    | proofIrrel hP hl hr =>
      exact ⟨_, .refl, DomainNormal.beta_proof hΓ (.forallE RD RB) (.proofIrrel hP hl hr) ⟨_, hl, hP⟩⟩
  | proj Rm ihm =>
    cases H with
    | refl => exact ⟨_, .proj Rm, _, .refl ((beta_simAt hΓ (.proj Rm) _ he).hasType.2)⟩
    | projDF hp HM =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := hp.proj_inv henv hΓ
      obtain ⟨m2, Rm2, _, HM2⟩ := ihm hΓ hmajor.hasType.2 HM
      exact ⟨_, .proj Rm2, _, .projDF ((beta_simAt hΓ (.proj Rm) _ hp).hasType.2) HM2⟩
    | proofIrrel hP hl hr =>
      exact ⟨_, .refl, DomainNormal.beta_proof hΓ (.proj Rm) (.proofIrrel hP hl hr) ⟨_, hl, hP⟩⟩
  | beta =>
    cases H with
    | refl => exact ⟨_, .beta, _, .refl ((beta_simAt hΓ .beta _ he).hasType.2)⟩
    | appDF hf hf' ha ha' Hf Ha =>
      have whole := DomainNormal.appDF hf hf' ha ha' Hf Ha
      cases Hf with
      | refl =>
        obtain ⟨⟨u, hD⟩, _, hb⟩ := hf.lam_inv henv hΓ
        obtain ⟨⟨_, hAD⟩, _⟩ := (hf.uniqU henv hΓ (HasType.lam hD hb)).forallE_inv henv hΓ
        exact ⟨_, .beta, DomainNormal.instN_r (by exact ⟨hΓ, u, hD⟩) (hAD.defeq ha) Ha .zero hb⟩
      | lamDF hD _ Hb =>
        obtain ⟨⟨_, hd⟩, _, hb⟩ := hf.lam_inv henv hΓ
        obtain ⟨⟨_, hAD⟩, _⟩ := (hf.uniqU henv hΓ (HasType.lam hd hb)).forallE_inv henv hΓ
        exact ⟨_, .beta, DomainNormal.instN_lr (by exact ⟨hΓ, _, hD⟩) (hAD.defeq ha) Ha .zero Hb⟩
      | proofIrrel hP hfl _ =>
        exact ⟨_, .refl, DomainNormal.beta_proof hΓ .beta whole
          (IsProof.app_fn hΓ hf ha ⟨_, hfl, hP⟩)⟩
    | proofIrrel hP hl hr =>
      exact ⟨_, .refl, DomainNormal.beta_proof hΓ .beta (.proofIrrel hP hl hr) ⟨_, hl, hP⟩⟩

end Lean4Lean.VEnv.Strengthening
