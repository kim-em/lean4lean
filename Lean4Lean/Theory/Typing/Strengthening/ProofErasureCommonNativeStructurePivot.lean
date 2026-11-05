import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidValueReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidTypeHeadReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureUniverseJoin

/-! # Structure pivots from common native output and parameter histories

Registered-family readout exposes equivalent universes and typed computation
chains for every supplied argument. Chains are not forward paths. Joining those
particular parameter histories suffices to join a structure-eta pivot whose
native output only meets the original family after computation. The remaining
parameter-joining premise is explicit; it is not proved here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Full computation of a registered family beta-cleans to the same head,
with equivalent well-formed universes and a scoped value chain for each original
argument. Parameters and indices may be retained data or functions. No forward
argument origin, common reduct, or native argument certificate is asserted. -/
theorem static_structure_registered_family_value_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) out) :
    ∃ ls' outputs,
      (∀ l ∈ ls, l.WF univs) ∧ (∀ l ∈ ls', l.WF univs) ∧
      ls.length = info.uvars ∧ List.Forall₂ (· ≈ ·) ls ls' ∧
      outputs.length = info.nparams + info.nindices ∧
      BetaRed out (ProofShape.mkApps (.const s ls') outputs) ∧
      List.Forall₂ (ScopedValueChain D (proofEraseCtx Γ)) (args.map (proofErase Γ)) outputs := by
  obtain ⟨doms, w, hlen, hf⟩ := StructureReplay.family_head_telescope henv hΓ hi ⟨u, hS⟩
  have hargs := StructureReplay.family_arity henv hΓ hi ⟨u, hS⟩
  have EL : args.length = doms.length := hargs.trans hlen.symm
  obtain ⟨result, HW, _⟩ := HasType.mkApps_telescope henv hΓ (hf hΓ) ⟨_, hS⟩
    (EL ▸ VExpr.takeForalls_wrapForalls doms (.sort w))
  obtain ⟨ls', outputs, RB, HC⟩ := ValueDemandProfile.static_structure_rigid_value_readout
    heq hs (henv.projectionRigid hi) hD hΓ (hf hΓ)
    (EL.symm ▸ RigidDemandProfile.sortTelescope_wrapForalls doms w) HW R
  obtain ⟨actual, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hS rfl rfl
    (R.trans (.beta RB))
  obtain ⟨args', rfl, rfl⟩ := proofErase_const_spine_inv EE
  obtain ⟨_, hhead⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, hS⟩
  obtain ⟨_, hhead'⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, HE.hasType.2⟩
  obtain ⟨hw, hl⟩ := StructureReplay.family_instance_levels hi hΓ hhead
  obtain ⟨hw', _⟩ := StructureReplay.family_instance_levels hi hΓ hhead'
  refine ⟨ls', args'.map (proofErase Γ), hw, hw', hl,
    (HE.toU.structApp_inv henv hΓ hi hS).1, ?_, RB, HC⟩
  simpa only [List.length_map] using
    StructureReplay.family_arity henv hΓ hi ⟨_, HE.hasType.2⟩

/-- Pointwise joins of the actual value histories assemble a common vector.
The missing hypothesis is only at members of the original vector, but it must
join all their scoped computation chains; sound replay alone does not do this. -/
theorem scoped_value_chain_vector_join
    (HC : List.Forall₂ (ScopedValueChain D Δ) ps qs)
    (HJ : ∀ p ∈ ps, ∀ q, ScopedValueChain D Δ p q →
      ∃ r, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ p r ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ q r) :
    ∃ rs, List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ) ps rs ∧
      List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ) qs rs := by
  induction HC with
  | nil => exact ⟨[], .nil, .nil⟩
  | @cons p q ps qs HC HT ih =>
    obtain ⟨r, HP, HQ⟩ := HJ p (by simp) q HC
    obtain ⟨rs, HPS, HQS⟩ := ih (fun p hp => HJ p (by simp [hp]))
    exact ⟨r :: rs, .cons HP HPS, .cons HQ HQS⟩

/-- Common native output suffices for a structure-eta pivot once the value
histories of the original parameters can be joined. Readout derives the new
family guard, arity, universe agreement and field-mask compatibility. Neither
the pivot's exact original family nor native recovery at the shared major is a
premise. Both residuals use full computation: retained parameter histories need
not admit pure-beta residuals. Constructing common native output and proving
the stated parameter-chain joins remain open in general. -/
theorem common_native_structure_pivot_square_of_parameter_chains
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (VExpr.mkApps (.const s ls) args) (.sort u))
    (hx : info.nindices = 0)
    (ha : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (HJ : ∀ p ∈ args.map (proofErase Γ), ∀ q, ScopedValueChain D (proofEraseCtx Γ) p q →
      ∃ r, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) p r ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) q r)
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original pivot)
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot target)
    (Rβ : BetaRed source target)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot commonType)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const s ls) args)) commonType) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) original shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (nativeStructureOutput s info ls (args.map (proofErase Γ)) source) shared := by
  obtain ⟨ls', qs, hw, hw', hl, HE, hq, RB, HC⟩ :=
    static_structure_registered_family_value_readout heq hs hi hD hΓ hS RT
  obtain ⟨rs, HP, HQ⟩ := scoped_value_chain_vector_join HC HJ
  have ha' : (info.resultLevel.inst ls').IsNeverZero ∨ StructureReplay.ProofFields env univs info ls' := by
    rcases ha with ha | ha
    · exact .inl (ha.of_equiv (VLevel.inst_congr rfl HE))
    · exact .inr (ha.level_congr henv hi hw hw' hl HE)
  have RNP := RN.convert (.beta RB)
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) pivot
      (nativeStructureOutput s info ls' qs pivot) :=
    .base (erased_static_structure_eta_expansion_union_structure
      (.intro hi hx ha' (by simpa only [hx, Nat.add_zero] using hq) RNP))
  obtain ⟨RL, RR⟩ := nativeStructureOutput_levels_join
    (fun H => ScopedCompute.base ⟨0, .inl (.inr H)⟩)
    hi hw hw' hl HE HP HQ (ScopedCompute.beta Rβ) Rafter
  exact ⟨nativeStructureOutput s info ls' rs target, Rbefore.trans (RE.trans RR), RL⟩

end Lean4Lean.VEnv.Strengthening
