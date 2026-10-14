import Lean4Lean.Theory.Typing.Strengthening.ProofErasure
import Lean4Lean.Theory.Typing.Strengthening.DomainNormalAlgebra
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalApplication

/-! # Comparing independently typed substitution instances

A raw template need not have a typing in an open smaller context. If two of its
instances are independently typed, pointwise convertible substitution values may
be mixed with arbitrary pairs of proofs. The propositions of those proof pairs
need not align in advance. Typing of the surrounding application aligns them at
each use. Lambda annotations are traversed, not erased.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- Substitution entries either coincide literally, have a recursive domain
comparison certificate, or are both proofs.
Literal equality permits unused untyped entries beyond the context. The proof
alternative requires no conversion of the two propositions. -/
def ProofSubstRel (Γ : List VExpr) (σ τ : Subst) : Prop :=
  ∀ i, σ i = τ i ∨ (∃ n, DomainNormal n Γ (σ i) (τ i)) ∨
    (IsProof Γ (σ i) ∧ IsProof Γ (τ i))

/-- Identical substitutions need no typing of their unused entries. -/
theorem ProofSubstRel.refl (σ : Subst) : ProofSubstRel Γ σ σ :=
  fun _ => .inl rfl

/-- Add a pair of proof arguments, even at unrelated propositions. -/
theorem ProofSubstRel.cons_proofs (H : ProofSubstRel Γ σ τ)
    (hp : IsProof Γ p) (hq : IsProof Γ q) : ProofSubstRel Γ (σ.cons p) (τ.cons q) := by
  intro i
  cases i with
  | zero => exact .inr (.inr ⟨hp, hq⟩)
  | succ i => exact H i

/-- Opening a binder preserves the relation, independently of its domain. -/
theorem ProofSubstRel.lift (H : ProofSubstRel Γ σ τ) :
    ProofSubstRel (D :: Γ) σ.lift τ.lift := by
  intro i
  cases i with
  | zero => exact .inl rfl
  | succ i =>
    rcases H i with h | h | ⟨⟨P, hp, hP⟩, ⟨Q, hq, hQ⟩⟩
    · exact .inl (congrArg VExpr.lift h)
    · obtain ⟨n, h⟩ := h
      exact .inr (.inl ⟨n, h.weakN .one⟩)
    · exact .inr (.inr ⟨⟨P.lift, hp.weak henv, hP.weak henv⟩,
        ⟨Q.lift, hq.weak henv, hQ.weak henv⟩⟩)

/-- Independently typed non-proof instances of one raw template have a recursive
domain comparison under a proof-insensitive substitution pair. No open typing of the template, common
type of its instances, or matching types of substituted proofs is assumed. -/
theorem subst_certificate_nonproof (e : VExpr) (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : ProofSubstRel Γ σ τ) (ha : Γ ⊢ e.subst σ : A) (hb : Γ ⊢ e.subst τ : B)
    (hn : ¬ IsProof Γ (e.subst σ)) : ∃ n, DomainNormal n Γ (e.subst σ) (e.subst τ) := by
  induction e generalizing Γ σ τ A B with
  | bvar i =>
    rcases H i with h | h | h
    · simpa only [subst_bvar, h] using
        (show ∃ n, DomainNormal n Γ (σ i) (σ i) from ⟨_, .refl ha⟩)
    · exact h
    · exact (hn h.1).elim
  | sort | const => exact ⟨_, .refl ha⟩
  | app f x ihf ihx =>
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hf', hx'⟩ := hb.app_inv henv hΓ
    obtain ⟨_, HF⟩ := ihf hΓ H hf hf' (not_isProof_fn hΓ hf hx hn)
    have hff := (HF.defeq hΓ).of_l henv hΓ hf
    obtain ⟨⟨_, hDD⟩, _⟩ := (hff.uniqU henv hΓ hf').forallE_inv henv hΓ
    have hxx : ∃ n, DomainNormal n Γ (x.subst σ) (x.subst τ) := by
      by_cases hp : IsProof Γ (x.subst σ)
      · obtain ⟨P, hxP, hP⟩ := hp
        have hAP := hx.uniqU henv hΓ hxP
        have hx'P := hx'.defeqU_r henv hΓ
          ((show Γ ⊢ _ ≡ _ from ⟨_, hDD⟩).symm.trans henv hΓ hAP)
        exact ⟨_, .proofIrrel hP hxP hx'P⟩
      · exact ihx hΓ H hx hx' hp
    obtain ⟨_, HX⟩ := hxx
    exact ⟨_, .appDF hf hff.hasType.2 hx ((HX.defeq hΓ).of_l henv hΓ hx).hasType.2 HF HX⟩
  | proj s i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    obtain ⟨_, HM⟩ := ih hΓ H hm.hasType.2 hm'.hasType.2 (not_isProof_major hΓ ha hn)
    exact ⟨_, .projDF ha HM⟩
  | lam D body ihD ihb =>
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := ha.lam_inv henv hΓ
    obtain ⟨⟨_, hD'⟩, _, hbody'⟩ := hb.lam_inv henv hΓ
    obtain ⟨_, HD⟩ := ihD hΓ H hD hD' (not_isProof_of_sort hΓ hD)
    have hDD := (HD.defeq hΓ).of_l henv hΓ hD
    have W := IsDefEqCtx.succ .zero hDD.symm
    have hbody'' := hbody'.defeqDFC henv W
    obtain ⟨_, HB⟩ := ihb (Γ := D.subst σ :: Γ) ⟨hΓ, _, hD⟩ H.lift hbody hbody''
      (fun hp => hn (hp.lam hΓ hD))
    exact ⟨_, .lamDF hD HD HB⟩
  | forallE D body ihD ihb =>
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hbody'⟩ := hb.forallE_inv henv
    obtain ⟨_, HD⟩ := ihD hΓ H hD hD' (not_isProof_of_sort hΓ hD)
    have hDD := (HD.defeq hΓ).of_l henv hΓ hD
    have W := IsDefEqCtx.succ .zero hDD.symm
    have hbody'' := hbody'.defeqDFC henv W
    obtain ⟨_, HB⟩ := ihb (Γ := D.subst σ :: Γ) ⟨hΓ, _, hD⟩ H.lift hbody hbody''
      (not_isProof_of_sort ⟨hΓ, _, hD⟩ hbody)
    exact ⟨_, .forallEDF hD HD hbody HB⟩

/-- At convertible endpoint types, proof instances are covered as well. -/
theorem subst_certificate_common (e : VExpr) (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : ProofSubstRel Γ σ τ) (ha : Γ ⊢ e.subst σ : A) (hb : Γ ⊢ e.subst τ : B)
    (hAB : Γ ⊢ A ≡ B) : ∃ n, DomainNormal n Γ (e.subst σ) (e.subst τ) := by
  by_cases hp : IsProof Γ (e.subst σ)
  · obtain ⟨P, haP, hP⟩ := hp
    have hAP := ha.uniqU henv hΓ haP
    exact ⟨_, .proofIrrel hP haP (hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hAP))⟩
  · exact subst_certificate_nonproof e hΓ H ha hb hp

/-- Replacing one proof variable by independently typed proofs preserves a
recursive domain certificate whenever the complete instances have convertible
types. Neither proof is required to inhabit the other's proposition. -/
theorem inst_proofs_certificate (e : VExpr) (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hp : IsProof Γ p) (hq : IsProof Γ q)
    (ha : Γ ⊢ e.inst p : A) (hb : Γ ⊢ e.inst q : B) (hAB : Γ ⊢ A ≡ B) :
    ∃ n, DomainNormal n Γ (e.inst p) (e.inst q) := by
  simp only [inst_eq] at ha hb ⊢
  exact subst_certificate_common e hΓ ((ProofSubstRel.refl .id).cons_proofs hp hq) ha hb hAB

/-- Matched beta redexes with a shared raw body and proof arguments have a
bidirectional beta join. The two lambda domains may differ and are never aligned;
the body instances supply their own typings by beta subject reduction. This is
the benign duplicated-template case of delayed proof-argument contraction. -/
theorem beta_proofs_same_template (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hp : IsProof Γ p) (hq : IsProof Γ q)
    (ha : Γ ⊢ .app (.lam D body) p : A)
    (hb : Γ ⊢ .app (.lam D' body) q : B) (hAB : Γ ⊢ A ≡ B) :
    BiBetaJoin true Γ (.app (.lam D body) p) (.app (.lam D' body) q) := by
  have ra : VExpr.BetaRed (.app (.lam D body) p) (body.inst p) := .beta
  have rb : VExpr.BetaRed (.app (.lam D' body) q) (body.inst q) := .beta
  have ha' := ra.simAt henv.orderedStrong henv.betaSubjectReduction hΓ A ha
  have hb' := rb.simAt henv.orderedStrong henv.betaSubjectReduction hΓ B hb
  obtain ⟨_, H⟩ := inst_proofs_certificate body hΓ hp hq ha'.hasType.2 hb'.hasType.2 hAB
  obtain ⟨_, H⟩ := H.toBiNormal
  exact ⟨_, _, _, ra, rb, .promote H⟩

end Lean4Lean.VEnv.Strengthening
