import Lean4Lean.Theory.Typing.Strengthening.DeclarationHeadTyping

/-! # Proof irrelevance does not preserve untyped function observations

In the well-formed context Q : Prop, h : Q, the proofs λ x : Q. x and
λ x : Q. h have the same proposition type. The first accepts a hypothetical Pi
observation of x; the second has no observation at the empty variable valuation.
Such demands describe untyped arguments. This rules out extending the present
observation preservation theorem directly to arbitrary definitional equality,
even in a canonical-Eq environment. It does not refute typed head exposure.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation.ProofBoundary
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

def ctx : List VExpr := [.bvar 0, .sort .zero]
def identityProof : VExpr := .lam (.bvar 1) (.bvar 0)
def constantProof : VExpr := .lam (.bvar 1) (.bvar 1)
def proofType : VExpr := .forallE (.bvar 1) (.bvar 2)

/-- The example context is well formed in every environment. -/
theorem context_wf (env : VEnv) (U : Nat) : OnCtx ctx (env.IsType U) :=
  ⟨⟨⟨⟩, _, HasType.sort (by trivial)⟩, _, HasType.bvar .zero⟩

/-- Both lambda terms prove Q → Q and hence are equal by proof irrelevance. -/
theorem proof_equality (env : VEnv) (U : Nat) :
    IsDefEq env U ctx constantProof identityProof proofType := by
  have hQ : HasType env U ctx (.bvar 1) (.sort .zero) := .bvar (.succ .zero)
  have hbody : HasType env U (.bvar 1 :: ctx) (.bvar 2) (.sort .zero) :=
    .bvar (.succ (.succ .zero))
  have hpi : HasType env U ctx proofType (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_zero).defeq
      (HasType.forallE hQ hbody)
  have hp : HasType env U ctx identityProof proofType := .lam hQ (.bvar .zero)
  have hq : HasType env U ctx constantProof proofType := .lam hQ (.bvar (.succ .zero))
  exact .proofIrrel hpi hq hp

/-- Untyped demands can feed a Pi observation to the bound proof variable. -/
theorem identity_observation :
    Obs D (fun _ _ => False) identityProof (.app [.pi] .pi) :=
  .lam (.var (by simp [Sets.cons]))

/-- The constant proof's body demands an observation of the free proof h,
which the empty valuation never supplies. -/
theorem constant_unobserved : ¬ Obs D (fun _ _ => False) constantProof o := by
  intro H
  obtain ⟨keys, result, hb, _⟩ := H.lam_inv
  obtain ⟨key, hk, _⟩ := hb.var_inv
  exact hk

/-- The existing observation relation cannot be backwards sound for all typed
definitional equalities. The example works in every environment, so adding
canonical Eq cannot repair this particular proposed extension. -/
theorem no_defeq_observation_preservation (env : VEnv) (U : Nat) (D : Definitions) :
    ¬ (∀ Γ e out T o, OnCtx Γ (env.IsType U) → IsDefEq env U Γ e out T →
      Obs D (fun _ _ => False) out o → Obs D (fun _ _ => False) e o) := by
  intro h
  exact constant_unobserved
    (h ctx constantProof identityProof proofType (.app [.pi] .pi)
      (context_wf env U) (proof_equality env U) identity_observation)

end Lean4Lean.VEnv.Strengthening.PureObservation.ProofBoundary

namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- In contrast to higher-order untyped demands, a Pi observation of a proof is
impossible for a sound declaration collection. This uses actual typed replay. -/
theorem Obs.proof_no_pi (hD : D.Sound Params.env univs)
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hp : IsProof Γ e) :
    ¬ Obs D (fun _ _ => False) e .pi := by
  intro H
  obtain ⟨A, B, R⟩ := H.pi_exposure
  obtain ⟨P, hp, hP⟩ := hp
  have ht := (R.simAt henv hD hΓ P hp).hasType.2
  obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
  exact not_isProof_of_sort hΓ (HasType.forallE hA hB) ⟨P, ht, hP⟩

/-- Sort observations also remain impossible for actual proofs. The boundary
above concerns preservation of all finite function demands, not these base heads. -/
theorem Obs.proof_no_sort (hD : D.Sound Params.env univs)
    (hΓ : OnCtx Γ (Params.env.IsType univs)) (hp : IsProof Γ e) :
    ¬ Obs D (fun _ _ => False) e .sort := by
  intro H
  obtain ⟨u, R⟩ := H.sort_exposure
  obtain ⟨P, hp, hP⟩ := hp
  have ht := (R.simAt henv hD hΓ P hp).hasType.2
  exact not_isProof_of_sort hΓ (HasType.sort (ht.sort_inv henv)) ⟨P, ht, hP⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
