import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-! # Hidden proof dependencies at erased eta contractions

For `F : Q → Q → Prop`, the term `λ h : Q. F h h` erases to an apparent
eta redex with a proof-marker argument. Its proposed eta contractum `F ⋆` has a
typed original representative only if Q is inhabited in the original context.
Thus exact beta replay does not extend automatically to proof-erased eta.
This is an implication under explicit typing assumptions, not a claim that some
canonical-Eq environment is consistent or that strengthening fails.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

/-- A function returning a sort cannot be a proof. -/
theorem not_isProof_function_to_sort (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : .forallE A (.sort u)) : ¬ IsProof Γ f := by
  obtain ⟨⟨v, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
  have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, v, hA⟩
  have hfw := hf.weak henv (B := A)
  have hx : A :: Γ ⊢ .bvar 0 : A.lift := .bvar .zero
  have happ : A :: Γ ⊢ .app f.lift (.bvar 0) : .sort u := HasType.app hfw hx
  intro hp
  have hpw : IsProof (A :: Γ) f.lift := by
    simpa only [lift_eq_lift'] using hp.lift' (Ctx.Lift'.skip .refl)
  exact not_isProof_of_sort hΓA happ (IsProof.app_fn hΓA hfw hx hpw)

namespace ErasedEta
/-- F's type in the example. -/
def familyType (Q : VExpr) : VExpr := .forallE Q (.forallE Q.lift (.sort .zero))
/-- The binder is used twice in proof positions. -/
def source (Q : VExpr) (i : Nat) : VExpr :=
  .lam Q (.app (.app (VExpr.bvar i).lift (.bvar 0)) (.bvar 0))
/-- The proposed erased eta contractum. -/
def target (i : Nat) : ProofShape := .app (.bvar i) .proof

/-- The original term is well typed, and erasure hides the first occurrence of h
inside the function of the outer application. -/
theorem source_typed_and_erased (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hQ : Γ ⊢ Q : .sort .zero) (hF : Γ ⊢ .bvar i : familyType Q) :
    (Γ ⊢ source Q i : .forallE Q (.sort .zero)) ∧
    proofErase Γ (source Q i) =
      .lam (proofErase Γ Q) (.app ((target i).liftN 1) .proof) := by
  have hΓQ : OnCtx (Q :: Γ) (Params.env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hx : Q :: Γ ⊢ .bvar 0 : Q.lift := .bvar .zero
  have hp : IsProof (Q :: Γ) (.bvar 0) := ⟨_, hx, hQ.weak henv⟩
  have hFw : Q :: Γ ⊢ (VExpr.bvar i).lift : (familyType Q).lift := hF.weak henv
  have hFx : Q :: Γ ⊢ .app (VExpr.bvar i).lift (.bvar 0) : .forallE Q.lift (.sort .zero) := by
    have hh : Q :: Γ ⊢ .app (VExpr.bvar i).lift (.bvar 0) :
        ((VExpr.forallE Q.lift (.sort .zero)).liftN 1 1).inst (.bvar 0) := HasType.app hFw hx
    simpa only [inst_liftN_bvar] using hh
  have hbody : Q :: Γ ⊢ .app (.app (VExpr.bvar i).lift (.bvar 0)) (.bvar 0) : .sort .zero := HasType.app hFx hx
  have hs : Γ ⊢ source Q i : .forallE Q (.sort .zero) := HasType.lam hQ hbody
  have hns := not_isProof_function_to_sort hΓ hs
  have hnb := not_isProof_of_sort hΓQ hbody
  have hnfx := not_isProof_function_to_sort hΓQ hFx
  have hnf := not_isProof_fn hΓQ hFw hx hnfx
  refine ⟨hs, ?_⟩
  simp only [source] at hns ⊢
  simp only [proofErase, if_neg hns, if_neg hnb, if_neg hnfx]
  simp only [lift, VExpr.liftN] at hnf ⊢
  simp only [proofErase, if_neg hnf, if_pos hp, target, ProofShape.liftN]

/-- Any typed original with the proposed contractum's erasure supplies a proof of Q.
The proof marker cannot be replayed without an actual inhabitant. -/
theorem target_representative_inhabits (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hF : Γ ⊢ .bvar i : familyType Q) (he : Γ ⊢ e : T)
    (H : proofErase Γ e = target i) : ∃ q, Γ ⊢ q : Q := by
  have app_inv {e : VExpr} {f a : ProofShape} (H : proofErase Γ e = .app f a) :
      ∃ f₀ a₀, e = .app f₀ a₀ ∧ proofErase Γ f₀ = f ∧ proofErase Γ a₀ = a := by
    cases e <;> simp only [proofErase] at H <;> split at H <;> simp_all
    exact ⟨_, _, ⟨rfl, rfl⟩, H⟩
  obtain ⟨f, a, rfl, Hf, _⟩ := app_inv H
  have hfvar : f = .bvar i := by
    cases f <;> simp only [proofErase] at Hf <;> split at Hf <;> simp_all
  subst f
  obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
  obtain ⟨⟨_, hAQ⟩, _⟩ := (hf.uniqU henv hΓ hF).forallE_inv henv hΓ
  exact ⟨a, hAQ.defeq ha⟩

/-- Supplying a proof of Q produces an original for the short erased form. -/
theorem applied_typed (hF : Γ ⊢ .bvar i : familyType Q) (hq : Γ ⊢ q : Q) :
    Γ ⊢ .app (.bvar i) q : .forallE Q (.sort .zero) := by
  simpa only [familyType, VExpr.inst, inst_lift] using HasType.app hF hq

/-- Existence of a typed representative for the proposed eta contractum is
exactly inhabitation of Q, with no normalization or consistency assumption. -/
theorem target_representative_iff (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hQ : Γ ⊢ Q : .sort .zero) (hF : Γ ⊢ .bvar i : familyType Q) :
    (∃ e T, (Γ ⊢ e : T) ∧ proofErase Γ e = target i) ↔ ∃ q, Γ ⊢ q : Q := by
  constructor
  · rintro ⟨e, T, he, H⟩
    exact target_representative_inhabits hΓ hF he H
  · rintro ⟨q, hq⟩
    have ht := applied_typed hF hq
    have hn := not_isProof_function_to_sort hΓ ht
    have hnf := not_isProof_fn hΓ hF hq hn
    have hp : IsProof Γ q := ⟨_, hq, hQ⟩
    refine ⟨_, _, ht, ?_⟩
    simp only [proofErase, if_neg hn, if_neg hnf, proofErase_eq_proof.2 hp, target]

/-- When an inhabitant is available, proof irrelevance followed by typed eta
repairs the example. The need for a representative does not prevent this repair. -/
theorem source_eq_of_inhabitant (hQ : Γ ⊢ Q : .sort .zero)
    (hF : Γ ⊢ .bvar i : familyType Q) (hq : Γ ⊢ q : Q) :
    IsDefEq Params.env univs Γ (source Q i) (.app (.bvar i) q) (.forallE Q (.sort .zero)) := by
  have hx : Q :: Γ ⊢ .bvar 0 : Q.lift := .bvar .zero
  have hFw : Q :: Γ ⊢ (VExpr.bvar i).lift : (familyType Q).lift := hF.weak henv
  have Hq : IsDefEq Params.env univs (Q :: Γ) (.bvar 0) q.lift Q.lift :=
    .proofIrrel (hQ.weak henv) hx (hq.weak henv)
  have Hf : IsDefEq Params.env univs (Q :: Γ)
      (.app (VExpr.bvar i).lift (.bvar 0)) (.app (VExpr.bvar i).lift q.lift)
      (.forallE Q.lift (.sort .zero)) := by
    have h : IsDefEq Params.env univs (Q :: Γ)
        (.app (VExpr.bvar i).lift (.bvar 0)) (.app (VExpr.bvar i).lift q.lift)
        (((VExpr.forallE Q.lift (.sort .zero)).liftN 1 1).inst (.bvar 0)) := .appDF hFw Hq
    simpa only [inst_liftN_bvar] using h
  exact (IsDefEq.lamDF hQ (IsDefEq.appDF Hf hx)).trans (IsDefEq.eta (applied_typed hF hq))

/-- If Q has no inhabitant below, the apparent erased eta contractum has no typed
original below, although its eta-expanded source is typed there. This rules out
exact target replay under these hypotheses; it does not rule out typed eta repair. -/
theorem target_not_replayable (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hF : Γ ⊢ .bvar i : familyType Q) (hQ : ∀ q, ¬ (Γ ⊢ q : Q)) :
    ¬ ∃ e T, (Γ ⊢ e : T) ∧ proofErase Γ e = target i := by
  rintro ⟨e, T, he, H⟩
  obtain ⟨q, hq⟩ := target_representative_inhabits hΓ hF he H
  exact hQ q hq

end ErasedEta
end Lean4Lean.VEnv.Strengthening
