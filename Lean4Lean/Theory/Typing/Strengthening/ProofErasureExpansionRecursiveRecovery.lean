import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionNativeBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreConfluence

/-! # A computed carrier repairs the recursive native-coverage obstruction

The recursive diagonal cannot recover its exact constant-headed assigned type.
It does recover the unfolded Pi, and its assigned type computes to that same Pi.
This verifies the weaker common-output interface on the actual obstruction.
-/
namespace Lean4Lean.VEnv.Strengthening.RecursiveDomain
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ctx_wf domain_typed body_typed diagonal_at_domain diagonal_not_proof
  from Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainLoop
variable [Params]

/-- The installed recursive equation exposes the carrier by ordinary core
computation, retaining exact source and target erasures. -/
theorem erased_recursive_domain_compute
    (hc : env.constants c = some (declaration c).toVConstant)
    (hd : env.defeqs (declaration c).toDefEq) :
    ProofShape.Compute ErasedCore.Step (proofErase loopCtx (domainL c))
      (.forallE (proofErase loopCtx (domainL c)) (.sort .zero)) := by
  have hs : ErasedCore.definitions.Sound env univs :=
    RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  have HD : ErasedCore.definitions.unfolds c [] (familyValue c) := by
    apply Or.inl
    refine ⟨(declaration c).toDefEq, [], hd, by simp, rfl, rfl, ?_⟩
    simp [declaration, VDefVal.toDefEq, familyValue, argType, Developments.tower,
      VExpr.instL, VLevel.inst]
  have RS : PatternStep ErasedCore.definitions (domainL c) (.app (familyValue c) fn) :=
    .appL (.delta HD)
  have hD := domain_typed hc
  have RE := proofErase_pattern_step_forward hs ctx_wf hD RS
  have hmid := (RS.toCompute.simAt hs ctx_wf _ hD).hasType.2
  have RB : VExpr.BetaRed (.app (familyValue c) fn) (.forallE (domainL c) (.sort .zero)) := by
    simpa [familyValue, domainL, VExpr.inst, instVar] using
      (VExpr.BetaRed.beta (A := argType)
        (b := .forallE (.app (.const c []) (.bvar 0)) (.sort .zero)) (a := fn))
  have R := RE.trans (.beta (proofErase_beta_forward ctx_wf hmid RB))
  have ht := (RB.simAt henv.orderedStrong henv.betaSubjectReduction ctx_wf _ hmid).hasType.2
  have hΓD : OnCtx (domainL c :: loopCtx) (env.IsType univs) := ⟨ctx_wf, _, hD⟩
  rw [show proofErase loopCtx (.forallE (domainL c) (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort ctx_wf ht),
    show proofErase (domainL c :: loopCtx) (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΓD (HasType.sort (by trivial)))] at R
  exact R

/-- The diagonal has a native unfolded Pi at stage zero, shared with a forward
computation of its assigned recursive carrier. Its exact assigned output is
still unavailable in the full union. -/
theorem expansion_native_computed_carrier_repair
    (hc : env.constants c = some (declaration c).toVConstant)
    (hd : env.defeqs (declaration c).toDefEq) :
    env.HasType univs loopCtx (diagonal (domainL c)) (domainL c) ∧
      (∃ out, ScopedTypeRecovery (ErasedExpansionStage ErasedCore.definitions 0)
        (proofEraseCtx loopCtx) (proofErase loopCtx (diagonal (domainL c))) out ∧
        ScopedCompute (ErasedExpansionStage ErasedCore.definitions 0)
          (proofEraseCtx loopCtx) (proofErase loopCtx (domainL c)) out) ∧
      ¬ ScopedTypeRecovery (ErasedExpansionUnion ErasedCore.definitions)
        (proofEraseCtx loopCtx) (proofErase loopCtx (diagonal (domainL c)))
        (proofErase loopCtx (domainL c)) := by
  have hδ (Γ) : env.IsDefEq univs Γ (.const c []) (familyValue c) familyType := by
    have H := IsDefEq.extra (Γ := Γ) (uvars := univs) (ls := []) hd (by simp) rfl
    simpa [declaration, VDefVal.toDefEq, familyType, familyValue, argType, Developments.tower,
      VExpr.instL, VLevel.params, VLevel.inst] using H
  obtain ⟨ht, hn, hno⟩ := expansion_native_exact_failure (D := ErasedCore.definitions) hc hδ
  have RC := erased_recursive_domain_compute hc hd
  let A := proofErase loopCtx (domainL c)
  have RL : ProofShape.Compute ErasedCore.Step (A.liftN 1) (.forallE (A.liftN 1) (.sort .zero)) := by
    have R := RC.subst (σ := fun i => (ProofShape.Subst.id i).liftN 1)
      (fun H => erased_iota_primitive_subst H)
    simpa only [← ProofShape.liftN_subst, ProofShape.subst_id, ProofShape.liftN] using R
  have hΓD : OnCtx (domainL c :: loopCtx) (env.IsType univs) := ⟨ctx_wf, _, domain_typed hc⟩
  have hb := body_typed hδ
  have hnb := not_isProof_of_sort hΓD hb
  obtain ⟨_, _, hf, hx⟩ := hb.app_inv henv hΓD
  have hnv := not_isProof_fn hΓD hf hx hnb
  have EE : proofErase loopCtx (diagonal (domainL c)) = .lam A (.app (.bvar 0) (.bvar 0)) := by
    rw [show proofErase loopCtx (diagonal (domainL c)) = .lam _ _ from if_neg hn,
      show proofErase (domainL c :: loopCtx) selfBody = .app _ _ from if_neg hnb,
      show proofErase (domainL c :: loopCtx) (.bvar 0) = .bvar 0 from if_neg hnv]
  refine ⟨ht, ⟨.forallE A (.sort .zero), ?_, RC.scoped (fun H => .base (.inl (.inl H)))⟩, hno⟩
  rw [EE]
  apply ScopedTypeRecovery.lam
  apply ScopedTypeRecovery.app (A := A.liftN 1) (B := .sort .zero)
  exact ScopedTypeRecovery.convert (T := A.liftN 1) .bvar
    (RL.scoped (fun H => .base (.inl (.inl H))))

omit [Params] in
/-- In the actual canonical-Eq extension, stage-zero recovery at a computed
carrier succeeds where exact recovery fails at every finite expanded depth.
The proposition front holds here independently of either recovery interface. -/
theorem canonical_expansion_computed_carrier_repair
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) :
    letI := (extended_wf hbase hfresh).params 0
    (extended base c).HasCanonicalEq ∧ PropositionFront ∧
      ∃ Γ x A, OnCtx Γ ((extended base c).IsType 0) ∧
        (extended base c).HasType 0 Γ x A ∧
        (∃ out, ScopedTypeRecovery (ErasedExpansionStage ErasedCore.definitions 0)
          (proofEraseCtx Γ) (proofErase Γ x) out ∧
          ScopedCompute (ErasedExpansionStage ErasedCore.definitions 0)
            (proofEraseCtx Γ) (proofErase Γ A) out) ∧
        ¬ ScopedTypeRecovery (ErasedExpansionUnion ErasedCore.definitions)
          (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A) := by
  letI := (extended_wf hbase hfresh).params 0
  refine ⟨extended_canonicalEq heq hfresh, canonical_recursiveDomain_front hbase heq hfresh,
    loopCtx, diagonal (domainL c), domainL c, ctx_wf, ?_⟩
  apply expansion_native_computed_carrier_repair (c := c)
  · change (extended base c).constants c = _
    simp [extended, stub, VEnv.addDefEq]
  · change (extended base c).defeqs (declaration c).toDefEq
    exact .inl rfl

end Lean4Lean.VEnv.Strengthening.RecursiveDomain
