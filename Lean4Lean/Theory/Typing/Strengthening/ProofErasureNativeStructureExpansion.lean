import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureExpansionTemplate
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeIdentityExpansion

/-! # Native structure eta with dependent proof-field masks

Native family recovery retains the constructor parameters. A closed telescope
fixes the proof-field mask, and the usual closed projection-admissibility guard
ensures the reconstructed constructor is typed. Source descent reconstructs the
whole expansion below arbitrary binder insertions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Registration supplies a closed specialized constructor telescope together
with its exact parameter-plus-field length. No occurrence-specific witness is
stored in this certificate. -/
theorem projection_expansion_telescope_exists (hi : env.projections s info)
    (hls : ∀ l ∈ ls, l.WF univs) :
    ∃ doms result, ProjTele env univs s info ls doms result ∧
      doms.length = info.nparams + info.numFields := by
  obtain ⟨decl, family, ctor, _, _, _, _, _, hnp, _, _, _, hctorType, _, _, _, hraw, _⟩ :=
    henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, hvalid, hhead, harity⟩ := hraw.forallArity
  have hresult : result = mkApps (.const family.name (VLevel.params decl.uvars)) result.getAppFnArgs.2 := by
    rw [← hhead]
    exact (mkApps_getAppFnArgs_eq result).symm
  have hshape' : info.ctorType = wrapForalls doms
      (mkApps (.const family.name (VLevel.params decl.uvars)) result.getAppFnArgs.2) := by
    rw [← hctorType, hshape, ← hresult]
  have hd : doms.length = info.nparams + info.numFields := by
    change doms.length = info.nparams + (info.ctorType.forallArity - info.nparams)
    rw [← hctorType, harity]
    omega
  exact ⟨_, _, ProjTele.of henv hshape' (henv.ordered.constWF (henv.ordered.projectionConstructor hi)) hls,
    by simpa only [List.length_map] using hd⟩

/-- General structure eta uses native family recovery, the actual registered
constructor telescope and its fixed proof mask. Nonempty dependent fields and
proof-valued parameters are permitted. Indexed structures are excluded, as in
the underlying structure-eta rule. -/
inductive ProofShape.NativeStructureExpansion
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro (hi : env.projections s info) (hx : info.nindices = 0)
      (hls : ∀ l ∈ ls, l.WF univs) (hlen : ls.length = info.uvars)
      (T : ProjTele env univs s info ls doms result)
      (hd : doms.length = info.nparams + info.numFields) (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (RN : ScopedTypeRecovery Step Δ m (ProofShape.mkApps (.const s ls) ps)) :
      NativeStructureExpansion Step Δ m (nativeStructureExpansion doms s info ls ps m)

/-- Enlarging the guard computation relation preserves the same expansion. -/
theorem ProofShape.NativeStructureExpansion.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : NativeStructureExpansion Step Δ a b) : NativeStructureExpansion Step' Δ a b := by
  cases H with
  | intro hi hx hw hl HT hd hp hadm RN => exact .intro hi hx hw hl HT hd hp hadm (RN.mono hstep)

/-- The whole dependent structure expansion descends through arbitrary inserted
binder blocks. Native recovery reconstructs parameters; typed telescope erasure
reconstructs every visible or proof field using the same closed mask. -/
theorem erased_nativeStructureExpansion_descent (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (NativeStructureExpansion Step) := by
  intro Γ Γ' n k e U out hΓ hΓ' W he H
  cases H with
  | @intro s info ls doms result m ps hi hx hw hl HT hd hp hadm RN =>
    obtain ⟨F, heF, EF⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W he rfl RN
    obtain ⟨raw, Es, Eps⟩ := ProofShape.liftN_const_spine_inv EF
    obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv Es
    have hargs : args.length = info.nparams := by
      have h := congrArg List.length Eps
      simp only [List.length_map] at h
      omega
    have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi hargs hx heF).2 hadm
    have hn : ¬ IsProof Γ e := by
      intro H
      exact RN.ne_proof (by rw [proofErase_eq_proof.2 H]; rfl)
    have HE := IsDefEq.structEta hi hargs hx heF hexp
    have hnexp : ¬ IsProof Γ (structExpand s info ls args e) := mt (isProof_congr hΓ HE).1 hn
    refine ⟨structExpand s info ls args e, HE.symm.toU.of_l henv hΓ he, ?_⟩
    rw [proofErase_structure_expansion_template hΓ hi hargs HT hd hw hl hexp hnexp,
      nativeStructureExpansion_liftN, ← Eps]

/-- Exact interpreted renaming preserves native structure eta, including all
closed field-proof masks and its selected family parameters. -/
theorem ProofShape.NativeStructureExpansion.rename
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (H : NativeStructureExpansion Step Δ a b) (W : ContextRenaming Δ Δ' τ) :
    NativeStructureExpansion Step' Δ' (a.subst τ) (b.subst τ) := by
  cases H with
  | intro hi hx hw hl HT hd hp hadm RN =>
    rw [nativeStructureExpansion_subst]
    apply NativeStructureExpansion.intro hi hx hw hl HT hd (by simpa only [List.length_map] using hp) hadm
    simpa only [ProofShape.subst_mkApps, ProofShape.subst] using RN.rename hrename W

/-- Every actual admissible structure eta expansion with exact native family
recovery is represented by the rule. Only the short source is independently
natively recovered; no field certificates or field purity assumptions occur. -/
theorem proofErase_native_structure_expansion
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections s info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = info.uvars)
    (hm : env.HasType univs Γ m (mkApps (.const s ls) ps)) (hn : ¬ IsProof Γ m)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ m)
      (ProofShape.mkApps (.const s ls) (ps.map (proofErase Γ)))) :
    NativeStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m)
      (proofErase Γ (structExpand s info ls ps m)) := by
  obtain ⟨doms, result, HT, hd⟩ := projection_expansion_telescope_exists hi hw
  have hexp := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hm).2 hadm
  have hnexp := mt (isProof_congr hΓ (IsDefEq.structEta hi hp hx hm hexp)).1 hn
  rw [proofErase_structure_expansion_template hΓ hi hp HT hd hw hl hexp hnexp]
  exact .intro hi hx hw hl HT hd (by simpa only [List.length_map] using hp) hadm RN

/-- Native-image transport substitutes the complete parameter spine and the
source's family guard. It assumes no universal coverage of such images. -/
theorem ProofShape.NativeStructureExpansion.subst_typed
    (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hinclude : ∀ {Δ a b}, ImageStep Δ a b → Target Δ a b)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source →
      NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (R : NativeStructureExpansion Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ) :
    NativeStructureExpansion Target Δ' (source.subst τ) (out.subst τ) := by
  cases R with
  | intro hi hx hw hl HT hd hp hadm RN =>
    have RN' := NativeImageTransport.recovery_of_compute hrename hstep hinclude hcompute RN hΓ ht EΓ Ee W
    rw [nativeStructureExpansion_subst]
    apply NativeStructureExpansion.intro hi hx hw hl HT hd
      (by simpa only [List.length_map] using hp) hadm
    simpa only [ProofShape.subst_mkApps, ProofShape.subst] using RN'


end Lean4Lean.VEnv.Strengthening
