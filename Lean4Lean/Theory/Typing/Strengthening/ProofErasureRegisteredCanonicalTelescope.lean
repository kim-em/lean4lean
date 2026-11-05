import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidTypeHeadReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureUniverseJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerCanonicalArgument

/-! # Whole registered-family computation with canonical parameters

Rigid head readout ignores all supplied arguments. Beta cleanup and universe
conversion survive arbitrary raw substitution; the target caller then replaces
those arguments using its own canonical telescope. No computational argument
demand, original-argument ancestry, or native substitution theorem is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D Target : PureObservation.Definitions}

/-- Every whole registered-family computation exposes the original universe
instance and arity after arbitrary raw substitution. Cleanup uses only beta and
universe conversion; it needs no target typing or target native certificate. -/
theorem static_structure_registered_spine_substitution_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) out) :
    ∃ rawArgs, rawArgs.length = info.nparams + info.nindices ∧
      ScopedCompute (fun _ => ErasedLevelCore Target) Δ (out.subst σ)
        (ProofShape.mkApps (.const s ls) rawArgs) := by
  obtain ⟨ls', rawArgs, hlen, RB⟩ :=
    RigidDemandProfile.static_structure_registered_family_head_readout heq hs hi hD hΓ hS R
  obtain ⟨actual, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hS rfl rfl
    (R.trans (.beta RB))
  obtain ⟨args', rfl, rfl⟩ := proofErase_const_spine_inv EE
  have HF := HE.toU.structApp_inv henv hΓ hi hS
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hS⟩
  obtain ⟨hw, _⟩ := StructureReplay.family_instance_levels hi hΓ hhead
  refine ⟨(args'.map (proofErase Γ)).map (fun a => a.subst σ), ?_, ?_⟩
  · simpa only [List.length_map] using hlen
  · apply (ScopedCompute.beta (RB.subst (σ := σ))).trans
    simp only [ProofShape.subst_mkApps, ProofShape.subst]
    exact ScopedCompute.mkApps (.base (.inr (.const (HF.1.flip.imp (fun _ _ H => H.symm)) hw)))
      (List.Forall₂.rfl (fun _ _ => .refl))

/-- Target native recovery and a canonical telescope complete every source
family computation after arbitrary raw substitution. Source and target contexts,
argument syntax, and sound definition collections may differ. Only the source
computation needs a soundness premise; target certificates are explicit. -/
theorem static_structure_registered_canonical_substitution_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion Target) Δ (.const s ls) T)
    (HC : CallerCanonicalTelescope Target Δ T (info.nparams + info.nindices) cs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion Target) Δ (out.subst σ)
      (ProofShape.mkApps (.const s ls) cs) := by
  obtain ⟨rawArgs, hlen, RB⟩ := static_structure_registered_spine_substitution_readout
    (Target := Target) (Δ := Δ) (σ := σ) heq hs hi hD hΓ hS R
  exact (RB.mono (fun H => ⟨0, .inl H⟩)).trans (HC.compute RN hlen)

/-- Arbitrary whole-family computation returns to one canonical application.
Every supplied parameter and index is ignored by head readout and canonicalized
through the selected native telescope. No lookup or argument observation is
required, including for retained higher-order arguments. -/
theorem static_structure_registered_canonical_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (.const s ls) T)
    (HC : CallerCanonicalTelescope D (proofEraseCtx Γ) T (info.nparams + info.nindices) cs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (ProofShape.mkApps (.const s ls) cs) := by
  simpa only [ProofShape.subst_id] using static_structure_registered_canonical_substitution_return
    (σ := Subst.id) heq hs hi hD hΓ hS RN HC R

/-- A source type computation before substitution joins any independent
computation after typed substitution. Source and target computation collections
may differ. The target family header and canonical telescope supply the repair. The left
branch may substitute any raw image, even independently of the typed value on
the right. Neither value needs native recovery or a computational demand. -/
theorem static_structure_registered_canonical_instantiation_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (ht : Target.Sound env univs)
    (hi : env.projections s info)
    (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hTarget : ∀ levels rhs, ¬ Target.unfolds s levels rhs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (hB : env.HasType univs (A :: Γ) (VExpr.mkApps (.const s ls) args) (.sort u))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion Target)
      (proofEraseCtx Γ) (.const s ls) T)
    (HC : CallerCanonicalTelescope Target (proofEraseCtx Γ) T (info.nparams + info.nindices) cs)
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (VExpr.mkApps (.const s ls) args)) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion Target) (proofEraseCtx Γ)
      (proofErase Γ ((VExpr.mkApps (.const s ls) args).inst x)) right) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion Target) (proofEraseCtx Γ)
        (left.inst image) (ProofShape.mkApps (.const s ls) cs) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion Target) (proofEraseCtx Γ)
        right (ProofShape.mkApps (.const s ls) cs) := by
  constructor
  · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      static_structure_registered_canonical_substitution_return
      (σ := Subst.one image) heq hs hi hD hΓA hB RN HC RL
  · have hB' := hB.instN henv Ctx.InstN.zero hx
    simp only [VExpr.inst_mkApps, VExpr.inst] at hB' RR
    exact static_structure_registered_canonical_return heq ht hi hTarget hΓA.1 hB' RN HC RR

end Lean4Lean.VEnv.Strengthening
