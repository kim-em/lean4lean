import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
import Lean4Lean.Theory.Typing.Strengthening.SingletonIndexAlignmentBoundary

/-! # Why inferred erased eta needs domain alignment

For propositions P and Q and a supplied q : Q, the expression
`fun p : P => (fun x : Q => Prop) q` has the apparent erased eta shape of
`fun x : Q => Prop`. Both terms are non-proofs. Their definitional equality is
exactly conversion of P and Q, which the erased eta shape does not record.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedEtaDomains
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A constant type-valued function with domain Q. -/
def short (Q : VExpr) : VExpr := .lam Q (.sort .zero)

/-- The last argument is a supplied proof of Q, independent of the P binder. -/
def long (P Q q : VExpr) : VExpr := .lam P (.app (short Q).lift q.lift)

/-- Both endpoints are typed and non-proof; their function domains may differ. -/
theorem typings (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero)) (hq : env.HasType univs Γ q Q) :
    env.HasType univs Γ (short Q) (.forallE Q (.sort (.succ .zero))) ∧
    env.HasType univs Γ (long P Q q) (.forallE P (.sort (.succ .zero))) := by
  have hf : env.HasType univs Γ (short Q) (.forallE Q (.sort (.succ .zero))) :=
    HasType.lam hQ (.sort (by trivial))
  have hbody := HasType.app (hf.weak henv (B := P)) (hq.weak henv (B := P))
  exact ⟨hf, HasType.lam hP hbody⟩

/-- The apparent erased eta match holds without P ≡ Q: the supplied q erases
to the same marker that would represent the fresh proof variable. -/
theorem apparent_eta (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero)) (hq : env.HasType univs Γ q Q) :
    ProofShape.EtaHead (proofErase Γ (long P Q q)) (proofErase Γ (short Q)) := by
  have ⟨hf, he⟩ := typings hP hQ hq
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  have hnf := not_isProof_of_sort hΓP (HasType.app (hf.weak henv (B := P)) (hq.weak henv))
  have hne : ¬ IsProof Γ (long P Q q) := by
    intro hp
    have hh := IsProof.app_fn hΓP (he.weak henv (B := P))
      (show env.HasType univs (P :: Γ) (.bvar 0) P.lift from .bvar .zero)
      (by simpa only [lift_eq_lift'] using hp.lift' (Ctx.Lift'.skip .refl))
    exact not_isProof_of_sort hΓP
      (HasType.app (he.weak henv (B := P)) (.bvar .zero)) hh
  have hqp : IsProof (P :: Γ) q.lift := ⟨_, hq.weak henv, hQ.weak henv⟩
  have HE := proofErase_liftN hΓ hΓP Ctx.LiftN.one hf
  unfold long at hne ⊢
  simp only [proofErase, if_neg hne, if_neg hnf]
  change ProofShape.EtaHead
    (.lam (proofErase Γ P) (.app (proofErase (P :: Γ) (short Q).lift) (proofErase (P :: Γ) q.lift)))
    (proofErase Γ (short Q))
  rw [HE, proofErase_eq_proof.2 hqp]
  exact .proof

/-- Any equality of these independently typed eta-shaped endpoints recovers
conversion of their domains. Conversely domain conversion makes them equal. -/
theorem equality_iff_domains (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero)) (hq : env.HasType univs Γ q Q) :
    env.IsDefEqU univs Γ (long P Q q) (short Q) ↔ env.IsDefEqU univs Γ P Q := by
  have ⟨hf, he⟩ := typings hP hQ hq
  constructor
  · intro H
    have HH := (H.of_l henv hΓ he).hasType.2.uniqU henv hΓ hf
    obtain ⟨⟨_, HD⟩, _⟩ := HH.forallE_inv henv hΓ
    exact ⟨_, HD⟩
  · intro H
    exact proofErase_eta_head_infer hΓ he hf H (apparent_eta hΓ hP hQ hq)

/-- Whenever two proposition domains are separated and Q is inhabited, the
displayed erased eta rule is unsound in unrestricted inferred mode. This is an
explicit conditional counterexample, not an assumed consistency assertion. -/
theorem apparent_eta_not_inferred (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero)) (hq : env.HasType univs Γ q Q)
    (hne : ¬ env.IsDefEqU univs Γ P Q) :
    ProofShape.EtaHead (proofErase Γ (long P Q q)) (proofErase Γ (short Q)) ∧
      ¬ env.IsDefEqU univs Γ (long P Q q) (short Q) :=
  ⟨apparent_eta hΓ hP hQ hq, fun H => hne ((equality_iff_domains hΓ hP hQ hq).1 H)⟩

/-- A fixed inhabited proposition with rigid Eq head. -/
def sourceDomain : VExpr :=
  eqApp (.succ (.succ .zero)) (.sort (.succ .zero)) (.sort .zero) (.sort .zero)

/-- An inhabited Pi proposition, separated from the rigid source domain. -/
def targetDomain : VExpr := .forallE sourceDomain sourceDomain.lift

/-- The identity proof supplies the hidden argument independently of the binder. -/
def targetProof : VExpr := .lam sourceDomain (.bvar 0)

/-- Canonical Eq supplies explicit inhabited, separated proposition domains.
Thus the apparent inferred eta failure requires neither inconsistent axioms nor
an empty binder. It is a failure of this erased rule, not of strengthening. -/
theorem canonical_domain_obstruction (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    env.HasType univs Γ sourceDomain (.sort .zero) ∧
    env.HasType univs Γ targetDomain (.sort .zero) ∧
    env.HasType univs Γ targetProof targetDomain ∧
    (∃ p, env.HasType univs Γ p sourceDomain) ∧
    ProofShape.EtaHead (proofErase Γ (long sourceDomain targetDomain targetProof))
      (proofErase Γ (short targetDomain)) ∧
    ¬ env.IsDefEqU univs Γ (long sourceDomain targetDomain targetProof)
      (short targetDomain) := by
  have hA : env.HasType univs Γ (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have ha : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) :=
    .sort (by trivial)
  have hP : env.HasType univs Γ sourceDomain (.sort .zero) :=
    HasType.eqApp heq (by trivial) hA ha ha
  have hQ : env.HasType univs Γ targetDomain (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE hP (hP.weak henv))
  have hq : env.HasType univs Γ targetProof targetDomain :=
    HasType.lam hP (.bvar .zero)
  have hne : ¬ env.IsDefEqU univs Γ sourceDomain targetDomain :=
    IsDefEqU.rigidApp_forallE_inv henv hΓ (heq.rigid henv)
      (ls := [.succ (.succ .zero)])
      (args := [.sort (.succ .zero), .sort .zero, .sort .zero]) hP
  exact ⟨hP, hQ, hq, ⟨_, HasType.eqReflApp heq (by trivial) hA ha⟩,
    apparent_eta_not_inferred hΓ hP hQ hq hne⟩

end Lean4Lean.VEnv.Strengthening.ErasedEtaDomains
