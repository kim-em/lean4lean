import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidTypeHeadReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureUniverseJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder

/-! # Return from computed registered families with erased arguments

Rigid head readout leaves the universe instance and argument vector open.
Typed family injectivity identifies the universes and forces every argument
back to a proof whenever the original parameters and indices are proofs.
Consequently arbitrary enriched computations return to the exact original
erasure. This supplies exact native guards from common native type output,
without assuming global type-fork joining or native parameter recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private empty_compute_beta from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedComparison
variable [Params] {D : PureObservation.Definitions}

/-- Beta cleanup exposes the original erased argument vector of a registered
family whose supplied parameters and indices are proofs. Its universe instance
may change only to an equivalent one. Empty vectors are included. The family
must have no selected delta rule; retained data arguments are not covered. -/
theorem static_structure_registered_proof_family_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (hp : ∀ a ∈ args, IsProof Γ a)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) out) :
    ∃ ls', List.Forall₂ (· ≈ ·) ls ls' ∧
      ProofShape.BetaRed out (ProofShape.mkApps (.const s ls') (args.map (proofErase Γ))) := by
  obtain ⟨ls', rawArgs, hlen, RB⟩ :=
    RigidDemandProfile.static_structure_registered_family_head_readout heq hs hi hD hΓ hS R
  obtain ⟨actual, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hS rfl rfl
    (R.trans (.beta RB))
  obtain ⟨args', rfl, rfl⟩ := proofErase_const_spine_inv EE
  have HF := HE.toU.structApp_inv henv hΓ hi hS
  have Eargs : args'.map (proofErase Γ) = args.map (proofErase Γ) := by
    have H := HF.2
    clear R RB HE EE hS HF hlen
    induction H with
    | nil => rfl
    | @cons a b args args' E H ih =>
      obtain ⟨_, E⟩ := E
      have hpa := hp a (by simp)
      have hpb := (isProof_congr hΓ E).1 hpa
      simp only [List.map_cons, proofErase_eq_proof.2 hpa, proofErase_eq_proof.2 hpb]
      exact congrArg (ProofShape.proof :: ·) (ih (fun a ha => hp a (by simp [ha])))
  exact ⟨ls', HF.1, Eargs ▸ RB⟩

/-- The return path survives every raw substitution, in any target context.
Only beta and universe conversion are needed on the target side. In particular,
no native image certificates, typed target substitution, or confluence premise
is required. The proof restriction is on the original family's arguments. -/
theorem static_structure_registered_proof_family_substitution_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (hp : ∀ a ∈ args, IsProof Γ a)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) out) :
    ScopedCompute (fun _ => ErasedLevelCore Target) Δ (out.subst σ)
      ((proofErase Γ (VExpr.mkApps (.const s ls) args)).subst σ) := by
  obtain ⟨ls', HL, RB⟩ := static_structure_registered_proof_family_readout heq hs hi hD hΓ hS hp R
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hS⟩
  obtain ⟨hw, _⟩ := StructureReplay.family_instance_levels hi hΓ hhead
  rw [proofErase_const_spine hΓ hS (not_isProof_of_sort hΓ hS)]
  apply (ScopedCompute.beta (RB.subst (σ := σ))).trans
  simp only [ProofShape.subst_mkApps, ProofShape.subst]
  exact ScopedCompute.mkApps (.base (.inr (.const (HL.flip.imp (fun _ _ H => H.symm)) hw)))
    (List.Forall₂.rfl (fun _ _ => .refl))

/-- Full enriched computation from the family returns to the exact original
source. Unlike neutral proof-family return, universe conversion may be needed
in addition to beta cleanup. -/
theorem static_structure_registered_proof_family_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (hp : ∀ a ∈ args, IsProof Γ a)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (proofErase Γ (VExpr.mkApps (.const s ls) args)) := by
  have H := static_structure_registered_proof_family_substitution_return
    (Target := D) (Δ := proofEraseCtx Γ) (σ := ProofShape.Subst.id) heq hs hi hD hΓ hS hp R
  simp only [ProofShape.subst_id] at H
  exact H.mono (fun H => ⟨0, .inl H⟩)

/-- A sort-typed family body with proof-only arguments has an exact backward
instantiation residual for every ordinarily typed argument. The argument may
lack native recovery at its assigned domain. This discharges that case of the
open TypeInstantiationJoin obligation without assuming common coverage. -/
theorem static_structure_registered_proof_type_instantiation_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (hB : env.HasType univs (A :: Γ) (VExpr.mkApps (.const s ls) args) (.sort u))
    (hp : ∀ a ∈ args, IsProof (A :: Γ) a)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (VExpr.mkApps (.const s ls) args)) out) :
    ScopedCompute (fun _ => ErasedLevelCore Target) (proofEraseCtx Γ)
      (out.inst (proofErase Γ x))
      (proofErase Γ ((VExpr.mkApps (.const s ls) args).inst x)) := by
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hB]
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
  exact static_structure_registered_proof_family_substitution_return heq hs hi hD hΓA hB hp R

/-- Common native coverage at a proof-argument registered family recovers the
exact assigned family. Producing common coverage for arbitrary values remains
open; this theorem removes the residual type computation once it is supplied. -/
theorem CommonNativeArgument.exact_registered_proof_family
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (hp : ∀ a ∈ args, IsProof Γ a)
    (H : CommonNativeArgument D Γ x (VExpr.mkApps (.const s ls) args)) (hn : ¬ IsProof Γ x) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ (VExpr.mkApps (.const s ls) args)) := by
  obtain ⟨shared, RN, RC⟩ := H hn
  exact RN.convert (static_structure_registered_proof_family_return heq hs hi hD hΓ hS hp RC)

/-- A common native type suffices for a structure-eta pivot with proof-only
parameters. Arbitrary dependent data/proof fields are allowed. The pivot and
shared major need no extra typing, parameter recovery, or common-output guard.
The expanded branch has a pure-beta residual. The common native type is
explicit; its general construction remains open. -/
theorem common_native_proof_parameter_structure_pivot_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (hp : ∀ a ∈ args, IsProof Γ a) (hx : info.nindices = 0)
    (ha : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (hlen : args.length = info.nparams)
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original pivot)
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot target)
    (Rβ : ProofShape.BetaRed source target)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot commonType)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) commonType) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original shared ∧
      ProofShape.BetaRed
        (nativeStructureOutput s info ls (args.map (proofErase Γ)) source) shared := by
  have RP := RN.convert (static_structure_registered_proof_family_return heq hs hi hD hΓ hS hp RT)
  rw [proofErase_const_spine hΓ hS (not_isProof_of_sort hΓ hS)] at RP
  refine ⟨nativeStructureOutput s info ls (args.map (proofErase Γ)) target, ?_, ?_⟩
  · exact Rbefore.trans ((ScopedCompute.base (erased_static_structure_eta_expansion_union_structure
      (.intro hi hx ha (by simpa only [List.length_map] using hlen) RP))).trans
        (nativeStructureOutput_compute (List.Forall₂.rfl (fun _ _ => .refl)) Rafter))
  · apply empty_compute_beta
    exact (nativeStructureOutput_compute
      (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl))
      (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := proofEraseCtx Γ) Rβ)).core_forget

end Lean4Lean.VEnv.Strengthening
