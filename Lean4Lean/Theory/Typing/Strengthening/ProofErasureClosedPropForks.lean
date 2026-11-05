import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextLambdaAnnotation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Closed inhabited proposition forks retain the full type-fork obligation

Pi wrappers close every ambient binder. A final inhabited proposition wrapper
stores an arbitrary type in its domain. Exact Pi readout recovers the original
component joins, so restricting roots to closed inhabited propositions does not
by itself remove the type-fork problem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Fork joining restricted to inhabited propositions in one fixed context.
This is an open proposition, not a supplied joining or completeness theorem. -/
def InhabitedPropForkJoinAt (D : PureObservation.Definitions) (Γ : List VExpr) : Prop :=
  ∀ {P p left right}, env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ p P →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ P) left →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ P) right →
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared

/-- The restricted open obligation at closed inhabited propositions only.
The equivalence below is a boundary result, not a strictly smaller sufficient
strengthening obligation or a proof that these forks actually join. -/
def ClosedInhabitedPropForkJoin (D : PureObservation.Definitions) : Prop :=
  InhabitedPropForkJoinAt D []

private theorem forall_prop (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hP : env.HasType univs (A :: Γ) P (.sort .zero)) :
    env.HasType univs Γ (.forallE A P) (.sort .zero) := by
  have HL : env.IsDefEq univs Γ (.sort (.imax u .zero)) (.sort .zero)
      (.sort (.succ (.imax u .zero))) :=
    .sortDF ⟨hA.sort_r henv hΓ, by trivial⟩ (by trivial) VLevel.imax_zero
  exact HL.defeq (HasType.forallE hA hP)

/-- Joining two typed Pis with the same domain yields a join of their bodies
in the original binder context. The intermediate Pi domain may have changed;
marked readout retains both original codomain computation histories. -/
theorem static_structure_same_domain_pi_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs (A :: Γ) C (.sort w))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) out)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A C)) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) B) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) C) shared := by
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))] at RB
  rw [show proofErase Γ (.forallE A C) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hC))] at RC
  obtain ⟨X, Y, HB, Rβ⟩ := proofErase_static_structure_union_pi_origin heq hs hΓ hA hB RB
  have HC := proofErase_static_structure_union_pi_components heq hs hΓ hA hC (RC.trans (.beta Rβ))
  obtain ⟨_, _, _, _, _, _, _, RBY⟩ := HB
  obtain ⟨_, _, _, _, _, _, _, RCY⟩ := HC
  exact ⟨Y, RBY, RCY⟩

/-- Inhabited proposition fork joining in a context implies the same property
after adding any typed binder, even an uninhabited one. Universal closure uses
the given proof only under that binder and creates an inhabited Pi proposition. -/
theorem InhabitedPropForkJoinAt.cons
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : InhabitedPropForkJoinAt D Γ)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    InhabitedPropForkJoinAt D (A :: Γ) := by
  intro P p left right hP hp RL RR
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨B, HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hP rfl rfl RL
  obtain ⟨C, HC, EC⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hP rfl rfl RR
  have hQ := forall_prop hΓ hA hP
  have QL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A P)) (proofErase Γ (.forallE A B)) := by
    rw [show proofErase Γ (.forallE A P) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hQ),
      show proofErase Γ (.forallE A B) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ (HasType.forallE hA HB.hasType.2)), EB]
    exact .forallE .refl RL
  have QR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A P)) (proofErase Γ (.forallE A C)) := by
    rw [show proofErase Γ (.forallE A P) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hQ),
      show proofErase Γ (.forallE A C) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ (HasType.forallE hA HC.hasType.2)), EC]
    exact .forallE .refl RR
  obtain ⟨shared, QB, QC⟩ := HF hQ (HasType.lam hA hp) QL QR
  obtain ⟨body, RB, RC⟩ := static_structure_same_domain_pi_join heq hs hΓ hA HB.hasType.2 HC.hasType.2 QB QC
  exact ⟨body, EB ▸ RB, EC ▸ RC⟩

/-- Closing all ambient binders shows that closed inhabited proposition forks
already contain inhabited proposition forks in every well-formed context. -/
theorem ClosedInhabitedPropForkJoin.in_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : ClosedInhabitedPropForkJoin D) (hΓ : OnCtx Γ (env.IsType univs)) :
    InhabitedPropForkJoinAt D Γ := by
  induction Γ with
  | nil => exact HF
  | cons A Γ ih =>
    obtain ⟨u, hA⟩ := hΓ.2
    exact InhabitedPropForkJoinAt.cons heq hs (ih hΓ.1) hΓ.1 hA

private def truthType : VExpr := .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))

private theorem truth_type (Γ : List VExpr) : env.HasType univs Γ truthType (.sort .zero) := by
  have hP : env.HasType univs (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have hP' : env.HasType univs (.bvar 0 :: .sort .zero :: Γ) (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have H := HasType.forallE (HasType.sort (l := .zero) (by trivial)) (HasType.forallE hP hP')
  have HL : env.IsDefEq univs Γ (.sort (.imax (.succ .zero) (.imax .zero .zero))) (.sort .zero)
      (.sort (.succ (.imax (.succ .zero) (.imax .zero .zero)))) :=
    .sortDF (by trivial) (by trivial) (by rfl)
  exact HL.defeq H

private theorem truth_inhabited (Γ : List VExpr) :
    env.HasType univs Γ (.lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))) truthType :=
  HasType.lam (HasType.sort (by trivial)) (HasType.lam (HasType.bvar .zero) (HasType.bvar .zero))

/-- Every type fork is the domain component of a fork at an inhabited
proposition. The proof of that proposition ignores its arbitrary type argument,
so neither the type nor the ambient context needs an inhabitant. -/
theorem InhabitedPropForkJoinAt.type_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : InhabitedPropForkJoinAt D Γ) (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u))
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) right) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared := by
  obtain ⟨A, HA, EA⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT rfl rfl RL
  obtain ⟨B, HB, EB⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT rfl rfl RR
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hQ := forall_prop hΓ hT (truth_type (T :: Γ))
  have XA := proofErase_defeqCtx hΓT (IsDefEqCtx.succ .zero HA) (truth_type (T :: Γ))
  have XB := proofErase_defeqCtx hΓT (IsDefEqCtx.succ .zero HB) (truth_type (T :: Γ))
  have QL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE T truthType)) (proofErase Γ (.forallE A truthType)) := by
    rw [show proofErase Γ (.forallE T truthType) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hQ),
      show proofErase Γ (.forallE A truthType) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ (forall_prop hΓ HA.hasType.2 (truth_type _))), EA, ← XA]
    exact .forallE RL .refl
  have QR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE T truthType)) (proofErase Γ (.forallE B truthType)) := by
    rw [show proofErase Γ (.forallE T truthType) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hQ),
      show proofErase Γ (.forallE B truthType) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ (forall_prop hΓ HB.hasType.2 (truth_type _))), EB, ← XB]
    exact .forallE RR .refl
  obtain ⟨shared, QA, QB⟩ := HF hQ (HasType.lam hT (truth_inhabited _)) QL QR
  rw [show proofErase Γ (.forallE A truthType) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (forall_prop hΓ HA.hasType.2 (truth_type _)))] at QA
  rw [show proofErase Γ (.forallE B truthType) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (forall_prop hΓ HB.hasType.2 (truth_type _)))] at QB
  obtain ⟨X, Y, OA, Rβ⟩ := proofErase_static_structure_union_pi_origin heq hs hΓ HA.hasType.2 (truth_type _) QA
  have OB := proofErase_static_structure_union_pi_components heq hs hΓ HB.hasType.2 (truth_type _) (QB.trans (.beta Rβ))
  obtain ⟨_, _, _, _, _, _, RAX, _⟩ := OA
  obtain ⟨_, _, _, _, _, _, RBX, _⟩ := OB
  exact ⟨X, EA ▸ RAX, EB ▸ RBX⟩

/-- Restricting roots to closed inhabited propositions retains all type forks.
This is an equivalence of open obligations, not a confluence proof and not a
claim that the original strengthening goal has been reduced to a smaller gap. -/
theorem type_fork_join_iff_closed_inhabited_prop
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    TypeForkJoin D ↔ ClosedInhabitedPropForkJoin D := by
  constructor
  · intro HF P p left right hP _ RL RR
    exact HF (by trivial) hP RL RR
  · intro HF Γ T u left right hΓ hT RL RR
    exact InhabitedPropForkJoinAt.type_fork heq hs (HF.in_context heq hs hΓ) hΓ hT RL RR

end Lean4Lean.VEnv.Strengthening
