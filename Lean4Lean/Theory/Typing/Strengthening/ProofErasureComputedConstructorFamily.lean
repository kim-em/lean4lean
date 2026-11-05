import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParameterizedStructureNativeWalk
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplateComputation

/-! # Family recovery after independent constructor argument computations

A retained saturated constructor remains a typed constructor after arbitrary
independent computations of its parameters and fields. Its literal declaration
therefore recovers the family at the resulting parameter images. This supplies
the target guard without assuming native evidence for the computed arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Arbitrary computations of all constructor arguments supply exact recovery
at the resulting family parameters. Only primitive descent and original typing
are used. Target recovery can use any relation, including the empty relation.
The theorem does not identify the new parameter images with the old ones. -/
theorem computed_structure_constructor_family
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hx : info.nindices = 0) (hlen : args.length = info.nparams + info.numFields)
    (ht : env.HasType univs Γ (VExpr.mkApps (.const info.ctorName ls) args) U)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const info.ctorName ls) args))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ)) (args.map (proofErase Γ)) images) :
    ScopedTypeRecovery Target (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) images)
      (ProofShape.mkApps (.const s ls) (images.take info.nparams)) := by
  have RC : ScopedCompute Source (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const info.ctorName ls) args))
      (ProofShape.mkApps (.const info.ctorName ls) images) := by
    rw [proofErase_const_spine hΓ ht hn]
    exact .mkApps .refl HA
  obtain ⟨e, HE, Ee⟩ := proofErase_scoped_compute_realize hstep hΓ ht rfl rfl RC
  obtain ⟨args', rfl, Eargs⟩ := proofErase_const_spine_inv Ee
  have hlen' : args'.length = info.nparams + info.numFields := by
    have H := HA.length_eq
    rw [Eargs, List.length_map, List.length_map] at H
    omega
  have hn' : ¬ IsProof Γ (VExpr.mkApps (.const info.ctorName ls) args') := by
    intro H
    have E := (proofErase_eq_proof.2 H).symm.trans Ee
    have EN : ProofShape.mkApps (.const info.ctorName ls) images ≠ .proof := by
      induction images using List.snoc_induction with
      | nil => simp [ProofShape.mkApps]
      | snoc => simp [ProofShape.mkApps_snoc]
    exact EN E.symm
  have RN := proofErase_structure_constructor_native (Step := Target) hΓ hi hx hlen' HE.hasType.2 hn'
  rw [Ee] at RN
  simpa only [Eargs, ← List.map_take] using RN

/-- Keeping the parameters fixed supplies their original family guard after
arbitrary field computations. The source may have dependent fields and arbitrary
data parameters, and none of their native certificates is needed for this guard. -/
theorem computed_structure_fields_family
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (ht : env.HasType univs Γ (structExpand s info ls ps m) U)
    (hn : ¬ IsProof Γ (structExpand s info ls ps m))
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields) :
    ScopedTypeRecovery Target (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) (ps.map (proofErase Γ) ++ fields))
      (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))) := by
  have HArgs := List.Forall₂.append'
    (List.Forall₂.rfl (l := ps.map (proofErase Γ)) (fun _ _ => ScopedCompute.refl (Step := Source) (Δ := proofEraseCtx Γ))) HA
  have R := computed_structure_constructor_family (Target := Target) hstep hΓ hi hx
    (args := ps ++ projsOf s m info.numFields) (by simp [projsOf, hp]) ht hn
    (by simpa only [List.map_append] using HArgs)
  simpa only [← hp, ← List.length_map (f := proofErase Γ) (as := ps), List.take_append_length] using R

/-- Two independently evolved field vectors at fixed parameters preserve all
native outputs from the first vector to the second. Source parameter recovery
is required only for the origin theorem; the second vector's family guard is
derived here from its computation history, not supplied as an extra premise. -/
theorem native_transfer_structure_field_histories
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) U)
    (hn : ¬ IsProof Γ (structExpand s info ls ps m))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m) (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))))
    (HP : ∀ j (hj : j < ps.length) (hjd : j < doms.length), ¬ IsProof Γ ps[j] →
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ ps[j])
        (proofErase Γ (doms[j].instOuter (ps.take j))))
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields)
    (HB : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((projsOf s m info.numFields).map (proofErase Γ)) fields') :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) (ps.map (proofErase Γ) ++ fields))
      (ProofShape.mkApps (.const info.ctorName ls) (ps.map (proofErase Γ) ++ fields')) := by
  have HArgs := List.Forall₂.append'
    (List.Forall₂.rfl (l := ps.map (proofErase Γ)) (fun _ _ => ScopedCompute.refl
      (Step := ErasedStaticStructureEtaExpansionUnion D) (Δ := proofEraseCtx Γ))) HA
  exact native_transfer_parameterized_structure_fields heq hs hΓ hi hp hx HT hd hw hl hc RN HP
    (by simpa only [List.map_append] using HArgs)
    (computed_structure_fields_family (erased_static_structure_eta_expansion_union_descent heq hs)
      hΓ hi hp hx hc hn HB)

end Lean4Lean.VEnv.Strengthening
