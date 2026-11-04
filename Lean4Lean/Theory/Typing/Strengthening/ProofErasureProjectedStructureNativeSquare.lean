import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureProjectionTypeResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMaskedConstructorRecovery

/-! # Native recovery across structure expansion below a projection

The constructor supplies native recovery for the expanded major. Dependent
field-type residuals then recover the projected field at the old recipe and
replay its original conversion tail. No target-native premise remains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Projecting a typed expanded constructor recovers the original field recipe
and any original conversion tail. No native major, parameter or field evidence
is required: the expanded constructor supplies its own exact family recovery. -/
theorem proofErase_projected_structure_expansion_native
    (hinclude : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (T : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields) (hj : info.nparams + j < doms.length)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) ps))
    (hc : env.HasType univs Γ (structExpand s info ls ps m) (VExpr.mkApps (.const s ls) ps))
    (hn : ¬ IsProof Γ (structExpand s info ls ps m)) (hproj : ¬ IsProof Γ (.proj s j m))
    (RC : ScopedCompute Step (proofEraseCtx Γ)
      (projectionType s info doms j hj (ps.map (proofErase Γ)) (proofErase Γ m)) out) :
    ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ (.proj s j (structExpand s info ls ps m))) out := by
  have RN := proofErase_structure_constructor_native (Step := Step) hΓ hi hx
    (by simp only [List.length_append, List.length_map, List.length_range, hp]) hc hn
  have E : (ps ++ projsOf s m info.numFields).take info.nparams = ps := by
    rw [← hp, List.take_append_length]
  change ScopedTypeRecovery Step (proofEraseCtx Γ)
    (proofErase Γ (structExpand s info ls ps m))
    (ProofShape.mkApps (.const s ls) (((ps ++ projsOf s m info.numFields).take info.nparams).map (proofErase Γ))) at RN
  rw [E] at RN
  exact proofErase_structure_projected_recovery_transport hinclude hΓ hi hp hx
    T hd hj hw hl hm hc hn hproj RN RC

/-- The compatible structure-eta step below a retained projection has a core
return path and preserves its selected native type, including every conversion
in its original tail. Only the source major has a native-family guard; no
source-stability or target-recovery assumption is used. -/
theorem static_structure_projected_native_square
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (T : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields) (hj : info.nparams + j < doms.length)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const s ls) ps))
    (hc : env.HasType univs Γ (structExpand s info ls ps m) (VExpr.mkApps (.const s ls) ps))
    (hn : ¬ IsProof Γ m) (hproj : ¬ IsProof Γ (.proj s j m))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m) (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (projectionType s info doms j hj (ps.map (proofErase Γ)) (proofErase Γ m)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.proj s j m)) (proofErase Γ (.proj s j (structExpand s info ls ps m))) ∧
      Compute (Primitive D) (proofErase Γ (.proj s j (structExpand s info ls ps m)))
        (proofErase Γ (.proj s j m)) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.proj s j (structExpand s info ls ps m))) out := by
  have hnc := mt (isProof_congr hΓ (IsDefEq.structEta hi hp hx hm hc)).1 hn
  have hadm := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).1 hc
  have hc2 := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hc).2 hadm
  have H := structure_proofField_iff hΓ hi hp (by omega : j < info.numFields) hc
  have H2 := structure_proofField_iff hΓ hi hp (by omega : j < info.numFields) hc2
  have hproj' : ¬ IsProof Γ (.proj s j (structExpand s info ls ps m)) :=
    fun h => hproj (H.1 (H2.2 h))
  refine ⟨?_, proofErase_structure_projected_expansion_compute hΓ hi hp hx
    (by omega) hm hc hnc, ?_⟩
  · rw [show proofErase Γ (.proj s j m) = .proj s j (proofErase Γ m) from if_neg hproj,
      show proofErase Γ (.proj s j (structExpand s info ls ps m)) =
        .proj s j (proofErase Γ (structExpand s info ls ps m)) from if_neg hproj']
    apply ScopedCompute.proj
    rw [proofErase_nativeStructureOutput hΓ hi hp hc hnc]
    exact .base (erased_static_structure_eta_expansion_union_structure
      (.intro hi hx hadm (by simpa only [List.length_map] using hp) RN))
  · exact proofErase_projected_structure_expansion_native
      (fun H => .base ⟨0, .inl (.inl (.inl (.inl H)))⟩)
      hΓ hi hp hx T hd hj hw hl hm hc hnc hproj RC

end Lean4Lean.VEnv.Strengthening
