import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicCoreReflection
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelRecursiveTransport

/-! # Evolving comparisons after atomic substitution

Atomic substitution can change a neutral head into a sort, but cannot expose
an ordinary redex. Reflecting ordinary paths avoids reconstructing the recursive
guard after substitution. Typed instantiated endpoints supply the universe
factorization; the original guard supplies all pre-substitution leaf typings.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Independent level-core paths from atomic instances of a recursive guard
remain comparable. Only the instantiated whole endpoints need typed witnesses;
leaf contexts need not be transported or synchronized with the substitution.
The recursive atomic constructor supplies a certificate before these tails;
this interface reads out its raw comparison. -/
theorem LevelRecursiveGuard.atomic_subst_forward
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode a b) (Hσ : AtomicSubstitution σ)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e A) (hf : env.HasType univs Γ f B)
    (Ee : proofErase Γ e = a.subst σ) (Ef : proofErase Γ f = b.subst σ)
    (RL : Compute (ErasedLevelCore D) (a.subst σ) left)
    (RR : Compute (ErasedLevelCore D) (b.subst σ) right) :
    RawCheckedCompare (ErasedLevelCore D) mode left right := by
  exact (H.atomic Hσ hΓ he hf Ee Ef).forward hs hl hcon hc (Ee.symm ▸ RL) (Ef.symm ▸ RR)

/-- Outputs joined to atomic instances compare by evolving those instances.
No fixedness, common reduct between the references, or new certificate after
substitution is required. -/
theorem LevelRecursiveGuard.atomic_subst_of_joins
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode a b) (Hσ : AtomicSubstitution σ)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e A) (hf : env.HasType univs Γ f B)
    (Ee : proofErase Γ e = a.subst σ) (Ef : proofErase Γ f = b.subst σ)
    (JL : ComputeJoin (ErasedLevelCore D) left (a.subst σ))
    (JR : ComputeJoin (ErasedLevelCore D) right (b.subst σ)) :
    RawCheckedCompare (ErasedLevelCore D) mode left right := by
  obtain ⟨l, RL, AL⟩ := JL
  obtain ⟨r, RR, BR⟩ := JR
  exact .compute RL RR (H.atomic_subst_forward hs hl hcon hc Hσ hΓ he hf Ee Ef AL BR)

/-- A recursive comparison of whole Pis suffices after atomic codomain
instantiation and independent computation. Reflect the instantiated codomain
paths first, extend them beneath the original Pis, then read out their raw
codomain comparison. No separate recursive codomain guard is required. -/
theorem LevelRecursiveGuard.pi_atomic_subst_forward
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode (.forallE X a) (.forallE Z b)) (Hσ : AtomicSubstitution σ)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e A) (hf : env.HasType univs Γ f B)
    (Ee : proofErase Γ e = a.subst σ) (Ef : proofErase Γ f = b.subst σ)
    (RL : Compute (ErasedLevelCore D) (a.subst σ) left)
    (RR : Compute (ErasedLevelCore D) (b.subst σ) right) :
    RawCheckedCompare (ErasedLevelCore D) false left right := by
  exact (H.piAtomic Hσ hΓ he hf Ee Ef).forward hs hl hcon hc (Ee.symm ▸ RL) (Ef.symm ▸ RR)

/-- Independent outputs joined to instantiated codomains compare directly from
one recursive whole-Pi certificate and atomic substitution. -/
theorem LevelRecursiveGuard.pi_atomic_subst_of_joins
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode (.forallE X a) (.forallE Z b)) (Hσ : AtomicSubstitution σ)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e A) (hf : env.HasType univs Γ f B)
    (Ee : proofErase Γ e = a.subst σ) (Ef : proofErase Γ f = b.subst σ)
    (JL : ComputeJoin (ErasedLevelCore D) left (a.subst σ))
    (JR : ComputeJoin (ErasedLevelCore D) right (b.subst σ)) :
    RawCheckedCompare (ErasedLevelCore D) false left right := by
  obtain ⟨l, RL, AL⟩ := JL
  obtain ⟨r, RR, BR⟩ := JR
  exact .compute RL RR (H.pi_atomic_subst_forward hs hl hcon hc Hσ hΓ he hf Ee Ef AL BR)

omit [Params] in
/-- The reflection strategy cannot be extended to arbitrary raw images:
substituting an identity lambda creates a beta redex at a previously neutral
head. This refutes unrestricted path reflection, not comparison transport or
typed strengthening. -/
theorem non_atomic_substitution_creates_beta :
    ∃ a σ out, ProofShape.BetaRed (a.subst σ) out ∧
      ¬ ∃ a', ProofShape.BetaRed a a' ∧ a'.subst σ = out := by
  let a := ProofShape.app (.bvar 0) .proof
  let σ := ProofShape.Subst.one (.lam .proof (.bvar 0))
  refine ⟨a, σ, .proof, .beta, ?_⟩
  rintro ⟨a', RA, EA⟩
  obtain ⟨args, rfl, HA⟩ := RA.bvar_spine (args := [.proof])
  cases HA with
  | cons _ Hnil => cases Hnil; cases EA

end Lean4Lean.VEnv.Strengthening
