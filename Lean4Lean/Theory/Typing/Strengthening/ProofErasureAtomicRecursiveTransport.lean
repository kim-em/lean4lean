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

private theorem structure_not_pi (H : StructureEtaHead (.forallE A B) m) : False := by
  generalize E : ProofShape.forallE A B = source at H
  cases H
  have HH := congrArg ProofShape.constHead E
  simp only [ProofShape.constHead, ProofShape.constHead_mkApps] at HH
  cases HH

/-- Raw Pi comparison exposes an inferred comparison of its codomains when
no primitive rewrites a Pi head. Computation prefixes are retained componentwise;
no common typing, normalization or domain comparison is an extra premise. -/
theorem ProofShape.Compare.pi_bodies
    (hpi : ∀ {A B out}, ¬ Step (.forallE A B) out)
    (H : Compare Step mode (.forallE A B) (.forallE C E)) : Compare Step false B E := by
  generalize EL : ProofShape.forallE A B = left at H
  generalize ER : ProofShape.forallE C E = right at H
  induction H generalizing A B C E with
  | refl => cases EL; cases ER; exact .refl
  | forallE HA HB => cases EL; cases ER; exact HB
  | compute RL RR H ih =>
    obtain ⟨A', B', E₁, _, RB⟩ := (EL ▸ RL).pi_parts hpi
    obtain ⟨C', E', E₂, _, RE⟩ := (ER ▸ RR).pi_parts hpi
    exact .compute RB RE (ih E₁.symm E₂.symm)
  | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EL.trans E
  | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases ER.trans E
  | structL H => exact (structure_not_pi (EL ▸ H)).elim
  | structR H => exact (structure_not_pi (ER ▸ H)).elim
  | sort | const | app | proj | lam | etaLams => cases EL

/-- Common-lambda checking adds no Pi case, so raw checked comparison has the
same codomain readout through arbitrary compatible computation prefixes. -/
theorem ProofShape.RawCheckedCompare.pi_bodies
    (hpi : ∀ {A B out}, ¬ Step (.forallE A B) out)
    (H : RawCheckedCompare Step mode (.forallE A B) (.forallE C E)) :
    RawCheckedCompare Step false B E := by
  generalize EL : ProofShape.forallE A B = left at H
  generalize ER : ProofShape.forallE C E = right at H
  induction H generalizing A B C E with
  | base H => exact .base ((EL ▸ ER ▸ H).pi_bodies hpi)
  | forallE HA HB => cases EL; cases ER; exact HB
  | compute RL RR H ih =>
    obtain ⟨A', B', E₁, _, RB⟩ := (EL ▸ RL).pi_parts hpi
    obtain ⟨C', E', E₂, _, RE⟩ := (ER ▸ RR).pi_parts hpi
    exact .compute RB RE (ih E₁.symm E₂.symm)
  | app | proj | lam | lamCommon => cases EL

/-- Independent level-core paths from atomic instances of a recursive guard
remain comparable. Only the instantiated whole endpoints need typed witnesses;
leaf contexts need not be transported or synchronized with the substitution.
The conclusion is a raw comparison, not recursive-guard closure. -/
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
  obtain ⟨left₀, RL₀, TL⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ he (Ee.symm ▸ RL)
  obtain ⟨right₀, RR₀, TR⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ hf (Ef.symm ▸ RR)
  rw [Ee] at RL₀
  rw [Ef] at RR₀
  obtain ⟨a', RA, EA⟩ := RL₀.iota_atomic_subst_inv Hσ
  obtain ⟨b', RB, EB⟩ := RR₀.iota_atomic_subst_inv Hσ
  have HC := (H.forward hs hl hcon hc (RA.mono (fun H => .inl H))
    (RB.mono (fun H => .inl H))).subst (fun H => erased_level_core_subst H) (σ := σ)
  exact .compute TL TR (by simpa only [EA, EB] using HC)

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
  obtain ⟨left₀, RL₀, TL⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ he (Ee.symm ▸ RL)
  obtain ⟨right₀, RR₀, TR⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ hf (Ef.symm ▸ RR)
  rw [Ee] at RL₀
  rw [Ef] at RR₀
  obtain ⟨a', RA, EA⟩ := RL₀.iota_atomic_subst_inv Hσ
  obtain ⟨b', RB, EB⟩ := RR₀.iota_atomic_subst_inv Hσ
  have HC := (H.forward hs hl hcon hc (.forallE .refl (RA.mono (fun H => .inl H)))
    (.forallE .refl (RB.mono (fun H => .inl H)))).pi_bodies (fun H => erased_level_core_no_pi H)
  have HS := HC.subst (fun H => erased_level_core_subst H) (σ := σ)
  exact .compute TL TR (by simpa only [EA, EB] using HS)

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
