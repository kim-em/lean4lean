import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeForkBinderJoin

/-! # Pi congruence from type-only fork joining

A common domain reduct determines one binder context. The codomain join is
transported forward to that context up to joining, then both paths are pulled
back along their domain computations. This aligns the two compatible Pi paths
without assuming forward native-certificate transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Type-only fork joining composes a domain join and a codomain join into a
Pi join. The codomain paths are supplied in the original A context only. Actual
domain equality gives typing under A', while the common computed domain is
realized and used to align the two paths. No native coverage is assumed. -/
theorem TypeForkJoin.pi_congr
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAA' : env.IsDefEq univs Γ A A' (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hB' : env.HasType univs (A :: Γ) B' (.sort v))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) commonA)
    (RA' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A') commonA)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) commonB)
    (RB' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B') commonB) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE A B)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE A' B')) shared := by
  obtain ⟨E, HAE, EE⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ HAA'.hasType.1 rfl rfl RA
  rw [← EE] at RA RA'
  have HA'E := HAA'.symm.trans HAE
  obtain ⟨sharedB, RBE, RB'E⟩ := HF.type_join_forward_context heq hs hΓ HAE RA hB hB' RB RB'
  have WAE : IsDefEqCtx env univs Γ (A :: Γ) (E :: Γ) := .succ .zero HAE
  have hBE := hB.defeqDFC henv WAE
  have hB'E := hB'.defeqDFC henv WAE
  have RBL := proofErase_static_structure_union_compute_backward_context heq hs hΓ HAE RA hBE RBE
  have RBR := proofErase_static_structure_union_compute_backward_context heq hs hΓ HA'E RA' hB'E RB'E
  have hPi := HasType.forallE HAA'.hasType.1 hB
  have hPi' := HasType.forallE HAA'.hasType.2
    (hB'.defeqDFC henv (IsDefEqCtx.succ .zero HAA'))
  have EP : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have EP' : proofErase Γ (.forallE A' B') = .forallE (proofErase Γ A') (proofErase (A' :: Γ) B') :=
    if_neg (not_isProof_of_sort hΓ hPi')
  refine ⟨.forallE (proofErase Γ E) sharedB, ?_, ?_⟩
  · rw [EP]
    exact .forallE RA (by simpa only [proofEraseCtx] using RBL)
  · rw [EP']
    exact .forallE RA' (by simpa only [proofEraseCtx] using RBR)

/-- The dependent Pi congruence case for contextual equality observations.
Domain and codomain contextual observations are the induction premises; their
identity contexts provide type joins. This closes this binder case under the
open TypeForkJoin premise, without asserting general contextual completeness. -/
theorem TypeForkJoin.contextual_forall_congr
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAA' : env.IsDefEq univs Γ A A' (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hB' : env.HasType univs (A :: Γ) B' (.sort v))
    (HA : TypeContextJoin D Γ (.sort u) A A')
    (HB : TypeContextJoin D (A :: Γ) (.sort v) B B') :
    TypeContextJoin D Γ (.sort (.imax u v)) (.forallE A B) (.forallE A' B') := by
  obtain ⟨a, RA, RA'⟩ := TypeContextJoin.type_join HA
  obtain ⟨b, RB, RB'⟩ := TypeContextJoin.type_join HB
  obtain ⟨shared, RL, RR⟩ := HF.pi_congr heq hs hΓ HAA' hB hB' RA RA' RB RB'
  have hPi := HasType.forallE HAA'.hasType.1 hB
  have hPi' := HasType.forallE HAA'.hasType.2
    (hB'.defeqDFC henv (IsDefEqCtx.succ .zero HAA'))
  obtain ⟨w, hSort⟩ := hPi.isType henv hΓ
  have hΓSort : OnCtx (.sort (.imax u v) :: Γ) (env.IsType univs) := ⟨hΓ, w, hSort⟩
  intro C z hC
  exact TypeContextJoin.of_compute_join heq hs hΓSort hPi hPi' RL RR hC

end Lean4Lean.VEnv.Strengthening
