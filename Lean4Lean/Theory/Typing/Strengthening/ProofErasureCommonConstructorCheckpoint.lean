import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonStructureHeader

/-! # Matching family and constructor checkpoints from common headers

Extract the shared parameter telescope, then reuse its parameter-domain paths
around the constructor's entire dependent field tail. This gives matching
ordinary assignments and native checkpoints for both actual constant heads.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A registered unindexed constructor and its family can both select a
common parameter checkpoint, retaining all dependent fields and their original
syntax. The stored constructor header computes forward to this new checkpoint;
the family starts an exact native history there. No parameter or field argument
is supplied, and no arbitrary pre-checkpoint native output is discarded or
asserted to join the checkpoint. -/
theorem CommonStructureFamilyHeader.constructor_checkpoint
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hx : info.nindices = 0)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (H : CommonStructureFamilyHeader D s info ls) :
    ∃ qs fs u,
      qs.length = info.nparams ∧ fs.length = info.numFields ∧
      NativeFamilyPiHistory D [] (.const s ls) u qs (etaOpen qs.length (.const s ls)) ∧
      env.HasType univs [] (.const info.ctorName ls)
        (VExpr.wrapForalls qs (VExpr.wrapForalls fs
          ((etaOpen qs.length (.const s ls)).liftN fs.length))) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
        (proofErase [] (info.ctorType.instL ls))
        (proofErase [] (VExpr.wrapForalls qs (VExpr.wrapForalls fs
          ((etaOpen qs.length (.const s ls)).liftN fs.length)))) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx [])
        (.const info.ctorName ls)
        (proofErase [] (VExpr.wrapForalls qs (VExpr.wrapForalls fs
          ((etaOpen qs.length (.const s ls)).liftN fs.length)))) := by
  obtain ⟨ps, tail, qs, u, Htake, hqs, hP, hQ, RPQ, hf, RNf⟩ :=
    H.checkpoint (Γ := []) heq hs (by trivial) hw
  obtain ⟨ps₀, fs, hps₀, hfs, HTc⟩ := registered_constructor_mixed_shape hi hx hl
  have Htake' : (info.ctorType.instL ls).takeForalls info.nparams = some
      (ps₀, VExpr.wrapForalls fs ((etaOpen ps₀.length (.const s ls)).liftN fs.length)) := by
    rw [HTc, ← hps₀]
    exact VExpr.takeForalls_wrapForalls ps₀ _
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (Htake'.symm.trans Htake))
  have hc : env.HasType univs [] (.const info.ctorName ls) (info.ctorType.instL ls) :=
    .const (henv.ordered.projectionConstructor hi) hw hl
  have hOld := hc.isType henv (by trivial)
  have hCtor : env.IsType univs [] (VExpr.wrapForalls ps₀
      (VExpr.wrapForalls fs ((etaOpen ps₀.length (.const s ls)).liftN fs.length))) := HTc ▸ hOld
  obtain ⟨_, v, hTail⟩ := IsType.wrapForalls_inv henv (by trivial) hCtor
  have hlen : ps₀.length = qs.length := hps₀.trans hqs.symm
  obtain ⟨hNew, RC⟩ := static_structure_sort_header_retarget_body heq hs (by trivial)
    hP hQ hlen RPQ ⟨v, hTail⟩
  rw [← HTc] at RC
  rw [hlen] at hNew RC
  obtain ⟨C, HC, EC⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (by trivial) hOld.choose_spec rfl rfl RC
  obtain ⟨_, HN⟩ := (proofErase_reflect (by trivial) HC.hasType.2 hNew.choose_spec EC).2
    (not_isProof_of_sort (by trivial) HC.hasType.2)
  have HE := HC.toU.trans henv (by trivial) (HN.defeq (by trivial))
  have hc' := hc.defeqU_r henv (by trivial) HE
  exact ⟨qs, fs, u, hqs, hfs, NativeFamilyPiHistory.initial heq hs (by trivial) hf RNf,
    hc', RC, (ScopedTypeRecovery.const (henv.ordered.projectionConstructor hi) hw hl).convert RC⟩

end Lean4Lean.VEnv.Strengthening
