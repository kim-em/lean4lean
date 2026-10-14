import Lean4Lean.Theory.Typing.Strengthening.BidirectionalDescent

/-! # The common-mode obligation in bidirectional normal composition

Inferred certificates have no head-eta cases. Their composition is structural,
provided common-mode certificates compose in domains and arguments. This file
isolates the proposed obligation; BidirectionalCompositionBoundary refutes it
on a concrete common-typed pair of certificates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Proposed common-mode composition of finite bidirectional normal certificates.
All inputs carry original typing. BidirectionalCompositionBoundary proves this
false even with a common endpoint type and no bound on the output index. -/
def BiCommonComposition : Prop :=
  ∀ {Γ a b c n m}, OnCtx Γ (env.IsType univs) → BiNormal true n Γ a b →
    BiNormal true m Γ b c → ∃ k, BiNormal true k Γ a c

/-- Inferred-mode composition reduces to common-mode composition in arguments
and binder domains. The induction decreases the first certificate's index;
context conversion preserves the index of the second body certificate. -/
theorem BiNormal.inferred_trans_of_common (Hcomp : BiCommonComposition) :
    ∀ n {Γ a b c m}, OnCtx Γ (env.IsType univs) → BiNormal false n Γ a b →
      BiNormal false m Γ b c → ∃ k, BiNormal false k Γ a c := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro Γ a b c m hΓ H1 H2
    have H12 := (H1.defeq hΓ).trans henv hΓ (H2.defeq hΓ)
    by_cases hp : IsProof Γ a
    · obtain ⟨P, ha, hP⟩ := hp
      exact ⟨0, .proofIrrel hP ha (H12.of_l henv hΓ ha).hasType.2⟩
    have hnpb : ¬ IsProof Γ b := by
      rintro ⟨P, hb, hP⟩
      exact hp ⟨P, ((H1.defeq hΓ).symm.of_l henv hΓ hb).hasType.2, hP⟩
    cases H1 with
    | refl ht => exact ⟨_, H2⟩
    | proofIrrel hP ha hb => exact (hp ⟨_, ha, hP⟩).elim
    | sortDF hu hv huv =>
      cases H2 with
      | refl => exact ⟨_, .sortDF hu hv huv⟩
      | sortDF _ hw hvw => exact ⟨_, .sortDF hu hw (huv.trans hvw)⟩
      | proofIrrel hP hb => exact (hnpb ⟨_, hb, hP⟩).elim
    | constDF hc hl hl' hlen hlevels =>
      cases H2 with
      | refl => exact ⟨_, .constDF hc hl hl' hlen hlevels⟩
      | constDF _ _ hl'' _ hlevels' =>
        exact ⟨_, .constDF hc hl hl'' hlen (hlevels.trans (fun _ _ _ h₁ h₂ => h₁.trans h₂) hlevels')⟩
      | proofIrrel hP hb => exact (hnpb ⟨_, hb, hP⟩).elim
    | appDF hf1 hf2 ha1 ha2 Hf Ha =>
      cases H2 with
      | refl => exact ⟨_, .appDF hf1 hf2 ha1 ha2 Hf Ha⟩
      | appDF hf2' hf3 ha2' ha3 Hf' Ha' =>
        obtain ⟨nf, HF⟩ := ih _ (by omega) hΓ Hf Hf'
        obtain ⟨na, HA⟩ := Hcomp hΓ Ha Ha'
        have hf3' := (HF.defeq hΓ).of_l henv hΓ hf1
        have ha3' := (HA.defeq hΓ).of_l henv hΓ ha1
        exact ⟨_, .appDF hf1 hf3'.hasType.2 ha1 ha3'.hasType.2 HF HA⟩
      | proofIrrel hP hb => exact (hnpb ⟨_, hb, hP⟩).elim
    | projDF ht Hm =>
      cases H2 with
      | refl => exact ⟨_, .projDF ht Hm⟩
      | projDF _ Hm' =>
        obtain ⟨_, HM⟩ := ih _ (by omega) hΓ Hm Hm'
        exact ⟨_, .projDF ht HM⟩
      | proofIrrel hP hb => exact (hnpb ⟨_, hb, hP⟩).elim
    | lamIndependent hA HD Hb =>
      cases H2 with
      | refl => exact ⟨_, .lamIndependent hA HD Hb⟩
      | lamIndependent hA' HD' Hb' =>
        obtain ⟨_, HDD⟩ := Hcomp hΓ HD HD'
        have hAB := (HD.defeq hΓ).of_l henv hΓ hA
        have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
        have Hb'' := Hb'.defeqDFC hΓ (IsDefEqCtx.succ .zero hAB.symm)
        obtain ⟨_, Hbb⟩ := ih _ (by omega) hΓA Hb Hb''
        exact ⟨_, .lamIndependent hA HDD Hbb⟩
      | proofIrrel hP hb => exact (hnpb ⟨_, hb, hP⟩).elim
    | forallEDF hA HD hB HB =>
      cases H2 with
      | refl => exact ⟨_, .forallEDF hA HD hB HB⟩
      | forallEDF hA' HD' hB' HB' =>
        obtain ⟨_, HDD⟩ := Hcomp hΓ HD HD'
        have hAB := (HD.defeq hΓ).of_l henv hΓ hA
        have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
        have HB'' := HB'.defeqDFC hΓ (IsDefEqCtx.succ .zero hAB.symm)
        obtain ⟨_, HBB⟩ := Hcomp hΓA HB HB''
        exact ⟨_, .forallEDF hA HDD hB HBB⟩
      | proofIrrel hP hb => exact (hnpb ⟨_, hb, hP⟩).elim

end Lean4Lean.VEnv.Strengthening
