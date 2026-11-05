import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeBetaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Arbitrary contextual function eta is already a stage-one type fork

The generic binder retains a function assignment before beta supplies an
arbitrary actual function. Eta in every occurrence of that variable needs only
stage-zero lookup guards, even in dependent annotations of the type observer.
Both resulting observations are reached at stage one. Joining those endpoints
is not proved here; no recovery certificate is required for the actual value.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- Computing a supplied argument through a typed observer preserves the
primitive stage. Only renaming of primitive guards, not arbitrary substitution
of those guards, is used. -/
theorem staged_compute_inst_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ)
      (proofErase Γ x) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) ((proofErase (A :: Γ) b).inst out) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have H := proofErase_compute_subst_images_of_renaming
    (erased_static_structure_eta_expansion_stage_rename heq hs stage)
    hΓA.1 W hb (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- A stage-bounded generic variable computation gives a sort-typed beta fork
at the same stage in every typed observer. The generic output may be raw; the
actual argument has ordinary typing only. This constructs the fork, not its join. -/
theorem staged_generic_type_context_peak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hC : env.HasType univs (A :: Γ) C (.sort v)) (ha : env.HasType univs Γ a A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx (A :: Γ))
      (.bvar 0) generic) :
    env.HasType univs Γ (.app (.lam A C) a) (.sort v) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A C) a)) (proofErase Γ (C.inst a)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A C) a))
        ((proofErase (A :: Γ) C).inst (generic.inst (proofErase Γ a))) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  let τ : ProofShape.Subst := fun i => match i with
    | 0 => generic
    | i+1 => .bvar (i+1)
  have hrename : ∀ {Δ Δ' a b σ}, ErasedStaticStructureEtaExpansionStage D stage Δ a b →
      ContextRenaming Δ Δ' σ → ErasedStaticStructureEtaExpansionStage D stage Δ' (a.subst σ) (b.subst σ) := by
    exact fun H W => erased_static_structure_eta_expansion_stage_rename heq hs stage H W
  have ES : ErasedSubstAgreement (A :: Γ) (A :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn, ProofShape.Subst.id]
  have RC := proofErase_compute_subst_images_of_renaming hrename hΓA
    (Ctx.SubstEq.id henv.ordered hΓA) hC ES (τ := τ) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [ProofShape.subst_id] at RC
  obtain ⟨ht, RL, RR⟩ := type_instantiation_compute_peak hΓ hA hC ha RC
  refine ⟨ht, RL, ?_⟩
  have E : ((proofErase (A :: Γ) C).subst τ).inst (proofErase Γ a) =
      (proofErase (A :: Γ) C).inst (generic.inst (proofErase Γ a)) := by
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
    congr 1
    funext i
    cases i <;> rfl
  exact E ▸ RR

/-- Arbitrary ordinary function eta inside an arbitrary type observer is a
stage-one fork from one explicit sort-typed beta redex. Neither a native guard
for the supplied function nor a joining premise is used. Proof functions and
proof-valued input domains are both included. -/
theorem first_stage_contextual_function_eta_peak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hC : env.HasType univs (.forallE A B :: Γ) C (.sort v)) :
    env.HasType univs Γ (.app (.lam (.forallE A B) C) f) (.sort v) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam (.forallE A B) C) f)) (proofErase Γ (C.inst f)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam (.forallE A B) C) f))
        (proofErase Γ (C.inst (.lam A (.app f.lift (.bvar 0))))) := by
  obtain ⟨w, hT⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, _⟩ := hT.forallE_inv henv
  have hΓT : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, w, hT⟩
  have heta := (IsDefEq.eta hf).hasType.1
  classical
  by_cases hp : IsProof Γ f
  · have hp' := (isProof_congr hΓ (IsDefEq.eta hf)).2 hp
    have E : proofErase Γ (C.inst f) = proofErase Γ (C.inst (.lam A (.app f.lift (.bvar 0)))) := by
      rw [proofErase_instN hΓT hf Ctx.InstN.zero hC,
        proofErase_instN hΓT heta Ctx.InstN.zero hC,
        proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    obtain ⟨ht, RL, _⟩ := type_instantiation_compute_peak
      (Step := ErasedStaticStructureEtaExpansionStage D 1) hΓ hT hC hf ScopedCompute.refl
    exact ⟨ht, RL, E ▸ RL⟩
  have ET : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hT)
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx (.forallE A B :: Γ)) (.bvar 0)
      (.forallE ((proofErase Γ A).liftN 1) ((proofErase (A :: Γ) B).liftN 1 1)) := by
    simpa only [proofEraseCtx, ET, contextOracle, TypeOracle.cons, ProofShape.liftN] using
      (ScopedTypeRecovery.bvar (Step := ErasedStaticStructureEtaExpansionStage D 0)
        (Δ := proofEraseCtx (.forallE A B :: Γ)) (i := 0))
  have SD := DomainSort.of_typed hΓT (hA.weakN henv Ctx.LiftN.one)
  rw [proofErase_liftN hΓ hΓT Ctx.LiftN.one hA] at SD
  have RG : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1)
      (proofEraseCtx (.forallE A B :: Γ)) (.bvar 0)
      (.lam ((proofErase Γ A).liftN 1) (.app ((ProofShape.bvar 0).liftN 1) (etaArgument u))) :=
    .base (.inr (.inr (.inr (.inr (.inl (.intro RN SD))))))
  obtain ⟨ht, RL, RR⟩ := staged_generic_type_context_peak heq hs hΓ hT hC hf RG
  have EG : (ProofShape.lam ((proofErase Γ A).liftN 1)
      (.app ((ProofShape.bvar 0).liftN 1) (etaArgument u))).inst (proofErase Γ f) =
      proofErase Γ (.lam A (.app f.lift (.bvar 0))) := by
    rw [proofErase_nativeEtaExpansion hΓ hA hf hp]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id, etaArgument_subst]
    rfl
  rw [EG, ← proofErase_instN hΓT heta Ctx.InstN.zero hC] at RR
  exact ⟨ht, RL, RR⟩

/-- Replacing a lambda's written domain by its assigned Pi domain in any type
observer is already a stage-one sort-typed fork. The body is arbitrary and is
preserved literally, including in proof cases. Both endpoints have contracted
the generic caller's beta redex: no surviving caller guard is supplied for the
missing residual join. This is the unrestricted annotation instance of the
mixed caller-history problem. -/
theorem first_stage_contextual_lambda_annotation_peak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam L b) (.forallE A B))
    (hC : env.HasType univs (.forallE A B :: Γ) C (.sort v)) :
    env.HasType univs Γ (.lam A b) (.forallE A B) ∧
      env.HasType univs Γ (.app (.lam (.forallE A B) C) (.lam L b)) (.sort v) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam (.forallE A B) C) (.lam L b)))
        (proofErase Γ (C.inst (.lam L b))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam (.forallE A B) C) (.lam L b)))
        (proofErase Γ (C.inst (.lam A b))) := by
  have heta := (IsDefEq.eta hf).hasType.1
  have RB : VExpr.BetaRed (.lam A (.app (VExpr.lam L b).lift (.bvar 0))) (.lam A b) := by
    apply VExpr.BetaRed.lam .refl
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar] using
      (VExpr.BetaRed.beta (A := L.lift) (b := b.liftN 1 1) (a := .bvar 0))
  have hg := (beta_eq hΓ heta RB).hasType.2
  obtain ⟨w, hPi⟩ := hf.isType henv hΓ
  have hΓPi : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, w, hPi⟩
  obtain ⟨ht, RL, RR⟩ := first_stage_contextual_function_eta_peak heq hs hΓ hf hC
  have RC := staged_compute_inst_argument (stage := 1) heq hs hΓPi hC heta
    (ScopedCompute.beta (proofErase_beta_forward hΓ heta RB))
  rw [← proofErase_instN hΓPi hg Ctx.InstN.zero hC] at RC
  exact ⟨hg, ht, RL, RR.trans RC⟩

end Lean4Lean.VEnv.Strengthening
