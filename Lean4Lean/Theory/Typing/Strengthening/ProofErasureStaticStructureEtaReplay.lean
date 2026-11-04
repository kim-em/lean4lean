import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaNativeTransport

/-! # Replay and proof-only joins for native structure eta

Every actual typed structure expansion is represented once its retained major
has native family recovery. Proof majors require no recovery certificate.
Nonempty proof-only structures also join opaque majors at their masked constructor.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Actual structure eta replays in the expanded language. Native family
recovery is required only when the major survives proof erasure; the expansion's
actual typing supplies the exact closed projection-admissibility condition. -/
theorem proofErase_static_structure_eta_native
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family ls) ps))
    (hc : env.HasType univs Γ (structExpand family info ls ps m)
      (VExpr.mkApps (.const family ls) ps))
    (RN : ¬ IsProof Γ m → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n)
      (proofEraseCtx Γ) (proofErase Γ m)
      (ProofShape.mkApps (.const family ls) (ps.map (proofErase Γ)))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) (proofEraseCtx Γ)
      (proofErase Γ m) (proofErase Γ (structExpand family info ls ps m)) := by
  have HE := (IsDefEq.structEta hi hp hx hm hc).symm
  by_cases hn : IsProof Γ m
  · have hp : IsProof Γ (structExpand family info ls ps m) := (isProof_congr hΓ HE).1 hn
    rw [proofErase_eq_proof.2 hn, proofErase_eq_proof.2 hp]
    exact .refl
  · have hnc : ¬ IsProof Γ (structExpand family info ls ps m) :=
      fun H => hn ((isProof_congr hΓ HE).2 H)
    rw [proofErase_nativeStructureOutput hΓ hi hp hc hnc]
    exact .base (.inr (.inr (.inr (.inr (.inr (.intro hi hx
      ((StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc)
      (by simpa only [List.length_map] using hp) (RN hn)))))))

/-- A global closed proof-field certificate certifies each individual field.
This uses the registered constructor shape, with no occurrence typing premise. -/
theorem StructureReplay.ProofFields.field
    (hi : env.projections family info) (H : ProofFields env univs info ls)
    (hj : j < info.numFields) : ProofField env univs info ls j := by
  obtain ⟨decl, family', ctor, _, _, _, _, _, hnparams, _, _, _, hctorType,
    _, _, _, hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, _, _, harity⟩ := hraw.forallArity
  have hlen : doms.length = info.nparams + info.numFields := by
    change doms.length = info.nparams + (info.ctorType.forallArity - info.nparams)
    rw [← hctorType, ← harity]
    omega
  have hs : info.ctorType = wrapForalls doms result := hctorType.symm.trans hshape
  exact ⟨doms, result, by omega, hs, hlen, H doms result hs hlen _ (by omega) (by omega)⟩

/-- Proof-only expansions have no remaining reference to their major. This
includes nonempty structures and arbitrary open or dependent parameters. -/
theorem ProofShape.nativeStructureOutput_proofFields
    (hi : env.projections family info) (H : StructureReplay.ProofFields env univs info ls) :
    nativeStructureOutput family info ls ps m =
      ProofShape.mkApps (.const info.ctorName ls) (ps ++ List.replicate info.numFields .proof) := by
  classical
  unfold nativeStructureOutput
  congr 2
  calc
    (List.range info.numFields).map (nativeStructureField family info ls m) =
        (List.range info.numFields).map (fun _ => ProofShape.proof) := by
      apply List.map_congr_left
      intro j hj
      exact if_pos (H.field hi (List.mem_range.1 hj))
    _ = _ := by rw [List.map_const', List.length_range]

/-- Opaque majors of a proof-only structure share a constructor reduct after
one guard stage. Unlike the empty-unit case, there may be arbitrarily many
proof fields, with dependent domains and arbitrary parameters. -/
theorem static_structure_eta_proof_fields_native_join
    (hi : env.projections family info) (hx : info.nindices = 0)
    (H : StructureReplay.ProofFields env univs info ls) (hp : ps.length = info.nparams)
    (RA : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ a
      (ProofShape.mkApps (.const family ls) ps))
    (RB : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ b
      (ProofShape.mkApps (.const family ls) ps)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) Δ a
        (ProofShape.mkApps (.const info.ctorName ls) (ps ++ List.replicate info.numFields .proof)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) Δ b
        (ProofShape.mkApps (.const info.ctorName ls) (ps ++ List.replicate info.numFields .proof)) := by
  have CA : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) Δ a
      (nativeStructureOutput family info ls ps a) :=
    .base (.inr (.inr (.inr (.inr (.inr (.intro hi hx (.inr H) hp RA))))))
  have CB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+1)) Δ b
      (nativeStructureOutput family info ls ps b) :=
    .base (.inr (.inr (.inr (.inr (.inr (.intro hi hx (.inr H) hp RB))))))
  rw [nativeStructureOutput_proofFields hi H] at CA CB
  exact ⟨CA, CB⟩

end Lean4Lean.VEnv.Strengthening
