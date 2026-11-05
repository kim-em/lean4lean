import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextBasicCases

/-! # Observe arbitrary data instantiation through type-valued beta forks

A generic body may have a genuinely dependent data type. Computing it before
instantiation and contracting beta first still gives two paths from its typed
beta redex. Observing that redex in an actual type context makes the fork's root
a type. Thus type-only fork joining supplies contextual instantiation without
assuming that the generic body itself has a sort type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Arbitrary typed bodies, including data bodies and proofs, produce the
instantiation beta peak. Source-typed replay handles the proof case: any output
of a proof erasure is again the proof marker. No substitution of native guards
or native certificate for the supplied argument is used. -/
theorem static_structure_instantiation_compute_peak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (he : env.HasType univs (A :: Γ) e E) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A e) x)) (proofErase Γ (e.inst x)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A e) x)) (out.inst (proofErase Γ x)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hf := HasType.lam hA he
  have ht := HasType.app hf hx
  refine ⟨.beta (proofErase_beta_forward hΓ ht .beta), ?_⟩
  classical
  by_cases hp : IsProof Γ (.app (.lam A e) x)
  · have hpx := (isProof_congr hΓ (IsDefEq.beta he hx)).1 hp
    have hpe := (isProof_instN hΓA hx Ctx.InstN.zero he).1 hpx
    obtain ⟨e', HE, Ee⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓA he rfl rfl R
    have hp' := (isProof_congr hΓA HE).1 hpe
    rw [proofErase_eq_proof.2 hp, ← Ee, proofErase_eq_proof.2 hp']
    exact .refl
  have hnf := not_isProof_fn hΓ hf hx hp
  rw [show proofErase Γ (.app (.lam A e) x) = .app _ _ from if_neg hp,
    show proofErase Γ (.lam A e) = .lam _ _ from if_neg hnf]
  exact (ScopedCompute.app (ScopedCompute.lam .refl
    (by simpa only [proofEraseCtx] using R)) .refl).trans (.beta .beta)

/-- Type-only fork joining transports computation of any typed generic body
through an arbitrary typed argument and then through an actual type observer.
The generic body need not be a type. Only the complete observed beta redex is
a type, which is sufficient for the fork premise. The raw output is explicit. -/
theorem TypeForkJoin.contextual_compute_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (he : env.HasType univs (A :: Γ) e E) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out)
    (hC : env.HasType univs (E.inst x :: Γ) C (.sort v)) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (C.inst (e.inst x))) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        ((proofErase (E.inst x :: Γ) C).inst (out.inst (proofErase Γ x))) shared := by
  have ht := HasType.app (HasType.lam hA he) hx
  have hex := he.instN henv.ordered Ctx.InstN.zero hx
  obtain ⟨w, hT⟩ := ht.isType henv hΓ
  have hΓT : OnCtx (E.inst x :: Γ) (env.IsType univs) := ⟨hΓ, w, hT⟩
  obtain ⟨RL, RR⟩ := static_structure_instantiation_compute_peak heq hs hΓ hA he hx R
  have OL := proofErase_static_structure_compute_inst_argument heq hs hΓT hC ht RL
  have OR := proofErase_static_structure_compute_inst_argument heq hs hΓT hC ht RR
  rw [← proofErase_instN hΓT hex Ctx.InstN.zero hC] at OL
  exact HF hΓ (hC.instN henv.ordered Ctx.InstN.zero ht) OL OR

/-- A computational join of arbitrary same-typed data bodies survives typed
instantiation in every type observer. The common raw body is realized, and all
composition occurs at observed types. This generalizes type-body instantiation;
it still requires a computational body join, not just a contextual body join. -/
theorem TypeForkJoin.contextual_inst_of_compute_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (he : env.HasType univs (A :: Γ) e E) (he' : env.HasType univs (A :: Γ) e' E)
    (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out)
    (R' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e') out) :
    TypeContextJoin D Γ (E.inst x) (e.inst x) (e'.inst x) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨q, HE, Eq⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA he rfl rfl R
  have hqx := HE.hasType.2.instN henv.ordered Ctx.InstN.zero hx
  obtain ⟨w, hT⟩ := hqx.isType henv hΓ
  have hΓT : OnCtx (E.inst x :: Γ) (env.IsType univs) := ⟨hΓ, w, hT⟩
  intro C v hC
  obtain ⟨s, LE, LO⟩ := HF.contextual_compute_inst heq hs hΓ hA he hx R hC
  obtain ⟨t, RE, RO⟩ := HF.contextual_compute_inst heq hs hΓ hA he' hx R' hC
  have EO : proofErase Γ (C.inst (q.inst x)) =
      (proofErase (E.inst x :: Γ) C).inst (out.inst (proofErase Γ x)) := by
    rw [proofErase_instN hΓT hqx Ctx.InstN.zero hC,
      proofErase_instN hΓA hx Ctx.InstN.zero HE.hasType.2, Eq]
  obtain ⟨r, L, R⟩ := HF hΓ (hC.instN henv.ordered Ctx.InstN.zero hqx) (EO ▸ LO) (EO ▸ RO)
  exact ⟨r, LE.trans L, RE.trans R⟩

end Lean4Lean.VEnv.Strengthening
