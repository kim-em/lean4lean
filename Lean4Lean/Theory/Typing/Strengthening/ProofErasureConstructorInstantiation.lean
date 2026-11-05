import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedNativeInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMaskedConstructorRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureUniverseJoin

/-! # Constructor endpoints repair instantiation of arbitrary bodies

A saturated registered constructor provides its native family without native
field certificates. When the assigned family parameters are proofs, type
injectivity aligns the selected parameters and universe conversion restores the
exact assignment. Dependent retained fields are unrestricted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Once native recovery exposes the registered family, ordinary type
injectivity aligns every proof parameter and the universe instance. This gives
the exact assigned native type without common-coverage or type joining. -/
theorem static_structure_native_proof_family_exact
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (ht : env.HasType univs Γ e (VExpr.mkApps (.const s ls) params))
    (hp : ∀ p ∈ params, IsProof Γ p)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const s ls') ps)) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ (VExpr.mkApps (.const s ls) params)) := by
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN
  obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv EA
  obtain ⟨_, hS⟩ := ht.isType henv hΓ
  have HE := (ht.uniqU henv hΓ heA).structApp_inv henv hΓ hi hS
  have EP : args.map (proofErase Γ) = params.map (proofErase Γ) := by
    have H := HE.2
    clear RN EA heA ht HE hS
    induction H with
    | nil => rfl
    | @cons p a params args E H ih =>
      obtain ⟨_, E⟩ := E
      have hpa := hp p (by simp)
      have hpb := (isProof_congr hΓ E).1 hpa
      simp only [List.map_cons, proofErase_eq_proof.2 hpa, proofErase_eq_proof.2 hpb]
      exact congrArg (ProofShape.proof :: ·) (ih (fun p h => hp p (by simp [h])))
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hS⟩
  have hw := (StructureReplay.family_instance_levels hi hΓ hhead).1
  rw [proofErase_const_spine hΓ hS (not_isProof_of_sort hΓ hS)]
  apply RN.convert
  rw [EP]
  exact ScopedCompute.mkApps (.base ⟨0, .inl (.inr
    (.const (HE.1.flip.imp (fun _ _ H => H.symm)) hw))⟩)
    (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))

/-- A literal saturated constructor at a family with proof-only parameters
recovers that exact assigned family. There may be arbitrarily many dependent
retained fields; their native recovery and syntactic purity are not required.
An unparameterized structure is included vacuously. -/
theorem static_structure_constructor_proof_family_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (hlen : images.length = info.nparams + info.numFields)
    (ht : env.HasType univs Γ e (VExpr.mkApps (.const s ls) params))
    (hp : ∀ p ∈ params, IsProof Γ p)
    (EE : proofErase Γ e = ProofShape.mkApps (.const info.ctorName levels) images) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ (VExpr.mkApps (.const s ls) params)) := by
  obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv EE
  have hn : ¬ IsProof Γ (VExpr.mkApps (.const info.ctorName levels) args) := by
    intro H
    have E := (proofErase_eq_proof.2 H).symm.trans EE
    have E := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  have RN := proofErase_structure_constructor_native
    (Step := ErasedStaticStructureEtaExpansionUnion D) hΓ hi hx
    (by simpa only [List.length_map] using hlen) ht hn
  exact static_structure_native_proof_family_exact heq hs hΓ hi ht hp RN

/-- Reaching a saturated constructor suffices to join arbitrary generic-body
instantiation. The original argument may have no exact native assignment.
Proof parameters align by erasure, while all dependent fields remain arbitrary.
The constructor-reaching computation is an explicit premise, not a claim of
normalization or constructor coverage for every inhabitant. -/
theorem static_structure_inst_join_constructor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hx : info.nindices = 0)
    (hlen : images.length = info.nparams + info.numFields)
    (hΓA : OnCtx (VExpr.mkApps (.const s ls) params :: Γ) (env.IsType univs))
    (hb : env.HasType univs (VExpr.mkApps (.const s ls) params :: Γ) b B)
    (ht : env.HasType univs Γ x (VExpr.mkApps (.const s ls) params))
    (hp : ∀ p ∈ params, IsProof Γ p)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (ProofShape.mkApps (.const info.ctorName levels) images))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (VExpr.mkApps (.const s ls) params :: Γ)) (proofErase (VExpr.mkApps (.const s ls) params :: Γ) b) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (out.inst (ProofShape.mkApps (.const info.ctorName levels) images)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst (proofErase Γ x)) (out.inst (ProofShape.mkApps (.const info.ctorName levels) images)) := by
  obtain ⟨y, Hxy, Ey⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA.1 ht rfl rfl RX
  have RN := static_structure_constructor_proof_family_native heq hs hΓA.1 hi hx hlen Hxy.hasType.2 hp Ey
  rw [Ey] at RN
  exact static_structure_inst_join_computed_recovery heq hs hΓA hb ht RX (fun _ => RN) RB

/-- Independent body and argument histories meet after the current argument
reaches a constructor. Neither the original nor the intermediate argument
requires exact recovery; dependent fields remain unrestricted. -/
theorem static_structure_body_argument_join_constructor
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hx : info.nindices = 0)
    (hlen : images.length = info.nparams + info.numFields)
    (hΓA : OnCtx (VExpr.mkApps (.const s ls) params :: Γ) (env.IsType univs))
    (hb : env.HasType univs (VExpr.mkApps (.const s ls) params :: Γ) b B)
    (ht : env.HasType univs Γ x (VExpr.mkApps (.const s ls) params))
    (hp : ∀ p ∈ params, IsProof Γ p)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      image (ProofShape.mkApps (.const info.ctorName levels) images))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (VExpr.mkApps (.const s ls) params :: Γ)) (proofErase (VExpr.mkApps (.const s ls) params :: Γ) b) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (out.inst (ProofShape.mkApps (.const info.ctorName levels) images)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (out.inst image) (out.inst (ProofShape.mkApps (.const info.ctorName levels) images)) := by
  obtain ⟨y, Hxy, Ey⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA.1 ht rfl rfl (RX.trans RC)
  have RN := static_structure_constructor_proof_family_native heq hs hΓA.1 hi hx hlen Hxy.hasType.2 hp Ey
  rw [Ey] at RN
  exact static_structure_body_argument_join_native_pivot heq hs hΓA hb ht RX RC (fun _ => RN) RB

end Lean4Lean.VEnv.Strengthening
