import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeUnitExpansion
import Lean4Lean.Theory.Typing.Strengthening.StructureProofField

/-! # Native structure eta with an exact static proof-field mask

Closed constructor telescopes determine which projected fields are proofs.
That mask is independent of occurrence parameters, the major and the context.
Native family recovery therefore suffices to reconstruct the full expansion
below binder insertion, including mixed proof/data and dependent fields.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- The closed telescope determines whether a projected field is erased. -/
noncomputable def ProofShape.nativeStructureField (family : Name) (info : VProjectionInfo)
    (ls : List VLevel) (m : ProofShape) (j : Nat) : ProofShape := by
  classical
  exact if StructureReplay.ProofField env univs info ls j then .proof else .proj family j m

/-- Constructor parameters followed by correctly masked projected fields. -/
noncomputable def ProofShape.nativeStructureOutput (family : Name) (info : VProjectionInfo)
    (ls : List VLevel) (ps : List ProofShape) (m : ProofShape) : ProofShape :=
  ProofShape.mkApps (.const info.ctorName ls)
    (ps ++ (List.range info.numFields).map (nativeStructureField family info ls m))

/-- The static field mask commutes with every raw substitution. -/
theorem ProofShape.nativeStructureField_subst :
    (nativeStructureField family info ls m j).subst τ =
      nativeStructureField family info ls (m.subst τ) j := by
  classical
  unfold nativeStructureField
  split <;> rfl

/-- The entire expansion commutes with raw substitution. -/
theorem ProofShape.nativeStructureOutput_subst :
    (nativeStructureOutput family info ls ps m).subst τ =
      nativeStructureOutput family info ls (ps.map (fun p => p.subst τ)) (m.subst τ) := by
  simp only [nativeStructureOutput, subst_mkApps, ProofShape.subst, List.map_append,
    List.map_map, Function.comp_def, nativeStructureField_subst]

/-- Binder insertion preserves the static mask and all retained arguments. -/
theorem ProofShape.nativeStructureOutput_liftN :
    (nativeStructureOutput family info ls ps m).liftN n k =
      nativeStructureOutput family info ls (ps.map (fun p => p.liftN n k)) (m.liftN n k) := by
  classical
  simp only [nativeStructureOutput, liftN_mkApps, ProofShape.liftN, List.map_append,
    List.map_map, Function.comp_def]
  congr 2
  apply List.map_congr_left
  intro j hj
  unfold nativeStructureField
  split <;> rfl

/-- A typed expansion has precisely the erasure selected by the closed mask. -/
theorem proofErase_nativeStructureOutput
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams)
    (ht : env.HasType univs Γ (structExpand family info ls ps m) T)
    (hn : ¬ IsProof Γ (structExpand family info ls ps m)) :
    proofErase Γ (structExpand family info ls ps m) =
      nativeStructureOutput family info ls (ps.map (proofErase Γ)) (proofErase Γ m) := by
  classical
  rw [show proofErase Γ (structExpand family info ls ps m) = _ from proofErase_const_spine hΓ ht hn]
  simp only [nativeStructureOutput, List.map_append, List.map_map, Function.comp_def]
  congr 2
  apply List.map_congr_left
  intro j hj
  have hj' := List.mem_range.1 hj
  have H := structure_proofField_iff hΓ hi hp hj' ht
  unfold nativeStructureField
  by_cases h : StructureReplay.ProofField env univs info ls j
  · rw [if_pos h, proofErase_eq_proof.2 (H.1 h)]
  · rw [if_neg h]
    exact if_neg (fun hp => h (H.2 hp))

/-- Native recovery exposes the family and all parameters. The closed
admissibility condition guarantees that every required projection is typable. -/
inductive ProofShape.NativeMaskedStructureExpansion
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro (hi : env.projections family info) (hx : info.nindices = 0)
      (ha : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (hp : ps.length = info.nparams) :
      ScopedTypeRecovery Step Δ source (ProofShape.mkApps (.const family ls) ps) →
      NativeMaskedStructureExpansion Step Δ source (nativeStructureOutput family info ls ps source)

/-- Enlarging guard computation preserves structure expansion. -/
theorem ProofShape.NativeMaskedStructureExpansion.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (R : NativeMaskedStructureExpansion Step Δ a b) : NativeMaskedStructureExpansion Step' Δ a b := by
  cases R with
  | intro hi hx ha hp RN => exact .intro hi hx ha hp (RN.mono hstep)

/-- Exact native recovery reconstructs a full, correctly masked structure
expansion below arbitrary inserted binder blocks, at the original assignment. -/
theorem erased_nativeMaskedStructureExpansion_descent (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (NativeMaskedStructureExpansion Step) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro hi hx ha hp RN =>
    rename_i family info ls rawPs
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W ht rfl RN
    obtain ⟨rawPs, Es, Eps⟩ := ProofShape.liftN_const_spine_inv EA
    obtain ⟨ps, rfl, rfl⟩ := proofErase_const_spine_inv Es
    have hps : ps.length = info.nparams := by
      have H := congrArg List.length Eps
      simp only [List.length_map] at H
      omega
    have hc := (StructureReplay.expansion_typed_iff henv hΓ hi hps hx heA).2 ha
    have HE := (IsDefEq.structEta hi hps hx heA hc).symm
    have hn : ¬ IsProof Γ e := by
      intro H
      exact RN.ne_proof (by rw [proofErase_eq_proof.2 H]; rfl)
    have hnc : ¬ IsProof Γ _ := fun H => hn ((isProof_congr hΓ HE).2 H)
    refine ⟨_, HE.toU.of_l henv hΓ ht, ?_⟩
    change (proofErase Γ (structExpand family info ls ps e)).liftN n k = _
    rw [proofErase_nativeStructureOutput hΓ hi hps hc hnc, nativeStructureOutput_liftN, ← Eps]

/-- The structure mask contains no occurrence context, so renaming changes
only the recovered parameters and retained source. -/
theorem ProofShape.NativeMaskedStructureExpansion.rename
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (R : NativeMaskedStructureExpansion Step Δ a b) (W : ContextRenaming Δ Δ' τ) :
    NativeMaskedStructureExpansion Step' Δ' (a.subst τ) (b.subst τ) := by
  cases R with
  | intro hi hx ha hp RN =>
    have RN' := RN.rename hrename W
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at RN'
    rw [nativeStructureOutput_subst]
    exact .intro hi hx ha (by simpa only [List.length_map] using hp) RN'

/-- Exact native-image transport substitutes structure guards and output,
including all dependent parameters and mixed proof/data fields. -/
theorem ProofShape.NativeMaskedStructureExpansion.subst_typed
    (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hinclude : ∀ {Δ a b}, ImageStep Δ a b → Target Δ a b)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source →
      NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (R : NativeMaskedStructureExpansion Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ) :
    NativeMaskedStructureExpansion Target Δ' (source.subst τ) (out.subst τ) := by
  cases R with
  | intro hi hx ha hp RN =>
    have RN' := NativeImageTransport.recovery_of_compute hrename hstep hinclude hcompute RN hΓ ht EΓ Ee W
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at RN'
    rw [nativeStructureOutput_subst]
    exact .intro hi hx ha (by simpa only [List.length_map] using hp) RN'

/-- Empty structures specialize the full masked expansion to native unit eta. -/
theorem ProofShape.NativeUnitExpansion.maskedStructure
    (R : NativeUnitExpansion Step Δ a b) : NativeMaskedStructureExpansion Step Δ a b := by
  cases R with
  | intro hi hx hf hp RN =>
    have H := NativeMaskedStructureExpansion.intro hi hx (.inr (StructureReplay.ProofFields.of_no_fields hf)) hp RN
    simpa only [nativeStructureOutput, hf, List.range_zero, List.map_nil, List.append_nil] using H

end Lean4Lean.VEnv.Strengthening
