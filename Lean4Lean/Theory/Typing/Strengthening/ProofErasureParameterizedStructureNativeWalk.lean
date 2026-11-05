import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureFieldNativeOrigin

/-! # Parameter obligations for complete structure constructor histories

The major's family certificate supplies every retained field, including later
dependent fields. Only the original parameters require separate native evidence
at their literal constructor domains. Once supplied, both parameters and fields
may compute independently, without native evidence for any computed image.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private native_walk_typing from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
variable [Params] {D : PureObservation.Definitions}

/-- A parameterized structure expansion has a recoverable constructor walk
when its original retained parameters recover their literal domains. Field
certificates are derived from the major guard and typed expansion. The parameter
premise is not asserted for arbitrary data; proof parameters discharge it. -/
theorem parameterized_structure_retained_native_walk
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) U)
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ m)
      (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))))
    (HP : ∀ j (hj : j < ps.length) (hjd : j < doms.length), ¬ IsProof Γ ps[j] →
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ ps[j])
        (proofErase Γ (doms[j].instOuter (ps.take j)))) :
    RetainedNativeWalk Step Γ (info.ctorType.instL ls) (ps ++ projsOf s m info.numFields)
      (VExpr.mkApps (.const s ls) ps) := by
  have HW := structure_constructor_native_walk hΓ hi hx
    (args := ps ++ projsOf s m info.numFields) (by simp [projsOf, hp]) hc
  rw [← hp, List.take_append_length] at HW
  rw [HT.shape] at HW ⊢
  apply RetainedNativeWalk.of_domains HW (by simp [projsOf, hd, hp])
  intro j hj hjd hn
  by_cases hparam : j < ps.length
  · simpa only [List.getElem_append_left hparam,
      List.take_append_of_le_length (Nat.le_of_lt hparam)] using
        HP j hparam hjd (by simpa only [List.getElem_append_left hparam] using hn)
  · let k := j - info.nparams
    have hkp : info.nparams + k = j := by dsimp [k]; omega
    have hk : k < info.numFields := by omega
    have hj' : info.nparams + k < doms.length := by omega
    have HA := structure_expansion_prefix_telescope hΓ hi hp HT hd hw hl hc (Nat.le_of_lt hk)
    obtain ⟨u, hF⟩ := HT.doms _ hj'
    have EF := proofErase_projection_template hΓ (HT.ctx _ (Nat.le_of_lt hj')) hF HA
    have Ep : (ps ++ projsOf s m info.numFields).take j = ps ++ projsOf s m k := by
      rw [← hkp]
      exact StructureReplay.projection_args_take hp (Nat.le_of_lt hk)
    have Ej : (ps ++ projsOf s m info.numFields)[j] = .proj s k m := by
      simp only [List.getElem_append_right (by omega : ps.length ≤ j), projsOf,
        List.getElem_map, List.getElem_range, hp, k]
    have NP : ¬ IsProof Γ (.proj s k m) := by simpa only [Ej] using hn
    have RP := ScopedTypeRecovery.proj hi HT hj'
      (by simp [hp, hx]) RN
    have ED : doms[j] = doms[info.nparams + k] := by congr 1; omega
    rw [Ej, Ep, show proofErase Γ (.proj s k m) = .proj s k (proofErase Γ m) from if_neg NP,
      ED, EF]
    simpa only [projectionType, ← List.map_take, ← hp, List.take_length] using RP

/-- Proof-valued parameters require no additional native coverage. Thus the
complete structure walk is supplied by its major certificate even when its
fields are retained, depend on earlier fields, or depend on those parameters. -/
theorem proof_parameter_structure_retained_native_walk
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) U)
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ m)
      (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))))
    (HP : ∀ p ∈ ps, IsProof Γ p) :
    RetainedNativeWalk Step Γ (info.ctorType.instL ls) (ps ++ projsOf s m info.numFields)
      (VExpr.mkApps (.const s ls) ps) :=
  parameterized_structure_retained_native_walk hΓ hi hp hx HT hd hw hl hc RN
    (fun _ hj _ hn => (hn (HP _ (List.getElem_mem hj))).elim)

/-- After supplying the original parameter certificates, every native output
of independently computed parameters and fields is reachable from the original
family assignment. The parameter computations are part of the history; the
family at their computed images is not silently identified with this source. -/
theorem parameterized_structure_computed_native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) U)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m) (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))))
    (HP : ∀ j (hj : j < ps.length) (hjd : j < doms.length), ¬ IsProof Γ ps[j] →
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ ps[j])
        (proofErase Γ (doms[j].instOuter (ps.take j))))
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((ps ++ projsOf s m info.numFields).map (proofErase Γ)) args)
    (RO : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) args) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))) out := by
  have HW := parameterized_structure_retained_native_walk hΓ hi hp hx HT hd hw hl hc RN HP
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  obtain ⟨_, hS⟩ := (native_walk_typing hctor HW.typed).isType henv hΓ
  have R := static_structure_computed_const_native heq hs hΓ
    (henv.ordered.projectionConstructor hi) hw hl HW HA RO
  rwa [proofErase_const_spine hΓ hS (not_isProof_of_sort hΓ hS)] at R

/-- A same-family pivot preserves every output of independently computed
parameters and fields when the original retained parameter domains are
certified. No output certificate is required of any computed argument. -/
theorem native_transfer_parameterized_structure_fields
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) U)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m) (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))))
    (HP : ∀ j (hj : j < ps.length) (hjd : j < doms.length), ¬ IsProof Γ ps[j] →
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ ps[j])
        (proofErase Γ (doms[j].instOuter (ps.take j))))
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((ps ++ projsOf s m info.numFields).map (proofErase Γ)) args)
    (RP : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      pivot (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ)))) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) args) pivot := by
  intro out RO
  exact RP.convert (parameterized_structure_computed_native_origin heq hs hΓ hi hp hx HT hd hw hl hc RN HP HA RO)

/-- Structures whose actual parameters are proofs need no extra parameter
native premise. Every native output after independent constructor-argument
computations transfers to a same-family pivot, including conversions through
arbitrary dependent field types. Arbitrary data parameters remain outside this
unconditional specialization. -/
theorem native_transfer_proof_parameter_structure_fields
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (HT : ProjTele env univs s info ls doms result)
    (hd : doms.length = info.nparams + info.numFields)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hc : env.HasType univs Γ (structExpand s info ls ps m) U)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ m) (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ))))
    (HP : ∀ p ∈ ps, IsProof Γ p)
    (HA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      ((ps ++ projsOf s m info.numFields).map (proofErase Γ)) args)
    (RP : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      pivot (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ)))) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName ls) args) pivot :=
  native_transfer_parameterized_structure_fields heq hs hΓ hi hp hx HT hd hw hl hc RN
    (fun _ hj _ hn => (hn (HP _ (List.getElem_mem hj))).elim) HA RP

end Lean4Lean.VEnv.Strengthening
