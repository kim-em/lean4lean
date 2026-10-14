import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixK
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextApplication

/-! # Finite erased computation with proof-major prefixes

Each stage admits full K and the prefix before its proof major, guarded by raw
checking at the preceding stage. Every stage retains typed descent, substitution
and weakening, so existing contextual transport and application apply unchanged.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Core computation followed by finite layers of full and prefix K. -/
def ErasedPrefixKStage (D : PureObservation.Definitions) : Nat → ProofShape → ProofShape → Prop
  | 0 => ErasedIotaPrimitive D
  | stage + 1 => fun a b => ErasedPrefixKStage D stage a b ∨
      ProofShape.RawCheckedKPrimitive (ErasedPrefixKStage D stage) a b ∨
      ProofShape.RawCheckedPrefixKPrimitive (ErasedPrefixKStage D stage) a b

/-- Full and prefix K both replay below insertion at every finite stage. -/
theorem erased_prefix_K_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedPrimitiveDescent (ErasedPrefixKStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    rcases R with R | R | R
    · exact ih hΓ hΓ' W ht R
    · exact erased_rawChecked_K_descent heq ih hΓ hΓ' W ht R
    · exact erased_rawChecked_prefix_K_descent heq ih hΓ hΓ' W ht R

/-- Stage bounds are unchanged by arbitrary raw simultaneous substitution. -/
theorem erased_prefix_K_stage_subst : ∀ stage {a b} {σ : ProofShape.Subst},
    ErasedPrefixKStage D stage a b → ErasedPrefixKStage D stage (a.subst σ) (b.subst σ) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_subst H
  | succ stage ih =>
    intro a b σ H
    rcases H with H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.subst ih))
    · exact .inr (.inr (H.subst ih))

/-- Stage bounds are unchanged by block insertion in raw syntax. -/
theorem erased_prefix_K_stage_liftN : ∀ stage {a b n k},
    ErasedPrefixKStage D stage a b → ErasedPrefixKStage D stage (a.liftN n k) (b.liftN n k) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_liftN H
  | succ stage ih =>
    intro a b n k H
    rcases H with H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.liftN ih))
    · exact .inr (.inr (H.liftN ih))

/-- Every raw checking K stage embeds at the same bound in the enlarged stages. -/
theorem erased_rawChecked_K_stage_prefix : ∀ stage {a b},
    ErasedRawCheckedKStage D stage a b → ErasedPrefixKStage D stage a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro a b H
    rcases H with H | H
    · exact .inl (ih H)
    · cases H with
      | intro HC => exact .inr (.inl (.intro (HC.mono ih)))

/-- A typed prefix with a preceding-stage endpoint guard computes one stage
later to its canonical proof-domain lambda. -/
theorem proofErase_prefix_K_stage_forward (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (HC : ProofShape.RawCheckedCompare (ErasedPrefixKStage D stage) true
      (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.Compute (ErasedPrefixKStage D (stage + 1))
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) :=
  (proofErase_rawChecked_prefix_K_forward heq (erased_prefix_K_stage_descent heq hs stage) hΓ ht HC).mono
    (fun H => .inr (.inr H))

/-- Full K can use endpoint guards containing the new prefix computations.
The guard is checked at the preceding stage, so the recursion remains finite. -/
theorem proofErase_prefix_K_stage_full_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (HC : ProofShape.RawCheckedCompare (ErasedPrefixKStage D stage) true
      (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.Compute (ErasedPrefixKStage D (stage + 1))
      (proofErase Γ (eqRecApp v w α a M m b p)) (proofErase Γ m) := by
  obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
  have hab := (proofErase_rawChecked_compare_reflect
    (erased_prefix_K_stage_descent heq hs stage) hΓ ha hb HC).1 ⟨_, hα⟩
  have HH := eqRecApp_simAt henv heq hΓ hab T ht
  by_cases hp : IsProof Γ (eqRecApp v w α a M m b p)
  · have hp' : IsProof Γ m := by
      obtain ⟨P, hsource, hP⟩ := hp
      exact ⟨P, (show env.IsDefEqU univs Γ _ _ from ⟨_, HH⟩).of_l henv hΓ hsource |>.hasType.2, hP⟩
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    exact .refl
  · have HE := proofErase_const_spine hΓ (args := [α, a, M, m, b, p]) ht hp
    change proofErase Γ (eqRecApp v w α a M m b p) = _ at HE
    rw [HE]
    exact .base (.inr (.inl (.intro HC)))

namespace ProofShape
/-- Contextual comparison is monotone in its primitive computation relation.
Its contextual domain-sort witnesses do not depend on that relation. -/
theorem ContextCompare.mono (hstep : ∀ {a b}, Step a b → Step' a b)
    (H : ContextCompare Step Δ mode a b) : ContextCompare Step' Δ mode a b := by
  induction H with
  | base H => exact .base (H.mono hstep)
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | lamSorted SA SA' _ _ ihA ihb => exact .lamSorted SA SA' ihA ihb
  | forallSorted SA SA' _ SB SB' _ ihA ihB => exact .forallSorted SA SA' ihA SB SB' ihB
  | lamCommon _ ih => exact .lamCommon ih
  | etaBodyL SA _ ih => exact .etaBodyL SA ih
  | etaBodyR SA _ ih => exact .etaBodyR SA ih
  | compute Ra Rb _ ih => exact .compute (Ra.mono hstep) (Rb.mono hstep) ih
  | symm _ ih => exact .symm ih
end ProofShape

/-- The enlarged concrete stages support common function application to a
shared typed argument without increasing their computation bound. -/
theorem proofErase_prefix_K_context_apply_same
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.ContextCompare (ErasedPrefixKStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.ContextCompare (ErasedPrefixKStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) :=
  proofErase_context_apply_same (erased_prefix_K_stage_descent heq hs stage)
    (fun H => erased_prefix_K_stage_subst stage H) hΓ hf hg hx H

end Lean4Lean.VEnv.Strengthening
