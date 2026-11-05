import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedProofTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationUnindexedPrefix

/-! # Singleton family guards with propositional indices

All index arguments erase to proofs. The transported and requested family
therefore have identical erasures, even when the index telescope is dependent.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature PropElim
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions} {params : List VExpr}

/-- A proof suffix may be changed beneath fixed parameters without changing
any erased instance of a typed closed template. -/
theorem proof_telescope_suffix_erasure
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : OnCtx params.reverse (env.IsType univs))
    (H : PropTelescope env univs params.reverse ds) (hps : ps.length = params.length)
    (ha : TelInst env univs Γ (params ++ ds) (ps ++ args))
    (hb : TelInst env univs Γ (params ++ ds) (ps ++ args'))
    (ht : env.HasType univs (params ++ ds).reverse e T) :
    proofErase Γ (e.instOuter (ps ++ args)) = proofErase Γ (e.instOuter (ps ++ args')) := by
  have hctx : OnCtx (params ++ ds).reverse (env.IsType univs) := by
    simpa only [List.reverse_append] using H.wf hP
  simp only [instOuter_eq_subst]
  apply proofErase_template_congr hΓ hΓ (erasedTemplate_substEq hctx ha)
    (erasedTemplate_substEq hctx hb) ht
  intro i A hl hn
  have hi : ds.length ≤ i := proof_telescope_retained_lookup H
    (by simpa only [List.reverse_append] using hl) (by simpa only [List.reverse_append] using hn)
  have hal : args.length = ds.length := by have := ha.1; simp only [List.length_append, hps] at this; omega
  have hbl : args'.length = ds.length := by have := hb.1; simp only [List.length_append, hps] at this; omega
  simp only [Subst.ofList, List.length_append, hal, hbl]
  split
  · rename_i hj
    have hpos : ps.length + ds.length - 1 - i < ps.length := by omega
    rw [List.getElem_append_left hpos, List.getElem_append_left hpos]
  · rfl

/-- A singleton with a dependent telescope of proof indices has a reflexive
raw family guard at every typed occurrence. No computation-chain joining is
needed: the two proposition erasures are exactly equal. -/
theorem proof_indices_family_erasure
    (heq : env.HasCanonicalEq) (W : E.WF S params env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hindices : PropTelescope env univs params.reverse S.indices)
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (params ++ S.indices ++ [majorTy S params E])
      (ps ++ idx ++ [m])) :
    proofErase Γ (transportedFamily S params E ps idx m) =
      proofErase Γ (mkApps E.family (ps ++ idx)) := by
  have hidx : idx.length = S.indices.length := by
    have := hargs.1; simp only [List.length_append, List.length_singleton] at this; omega
  have hia : TelInst env univs Γ (params ++ S.indices) (ps ++ idx) := by
    have := hargs.take (doms := params ++ S.indices) (more := [majorTy S params E])
    simpa [hps, hidx, List.take_append, List.take_of_length_le] using this
  have hf := transportedFields_typed henv heq W hΓ hps hargs (Nat.le_refl S.fields.length)
  rw [List.take_length] at hf
  have hci := W.specializedCtorIndices henv hps hf
  have hP : OnCtx params.reverse (env.IsType univs) := by
    simpa using W.typed.indicesCtx 0 (Nat.zero_le _)
  have h := proof_telescope_suffix_erasure hΓ hP hindices hps hci hia W.majorTy_typed
  rw [majorTy_at W hps (by simpa using W.ctorIndices_length), majorTy_at W hps hidx] at h
  rw [transportedFamily_eq henv heq W hΓ hps hargs]
  exact h

/-- Valid singleton code with propositional indices has a reflexive family
comparison beneath every generated residual telescope. -/
theorem SingletonPrefixCode.Valid.proof_indices_guard
    {C : SingletonPrefixCode} (V : C.Valid) (heq : env.HasCanonicalEq)
    (hindices : PropTelescope env univs (C.data.propParams C.levels).reverse C.layout.indices)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const C.data.name C.levels) args)) :
    GuardedSingleton.FamilyGuard
      (ErasedFamilyComparison (fun Δ => ProofShape.CarrierRecoveredCompare Step Δ true))
      Γ C.data C.levels args program C.layout C.elim := by
  obtain ⟨_, _, hl, hll, he, _, _⟩ := InductiveSignature.RecursorData.singletonUnfolding_spec hg
  have hlen : C.levels.length = C.data.uvars := by
    rw [hl] at hll
    exact hll.trans (InductiveSignature.RecursorData.singletonEquation_uvars he)
  obtain ⟨index, howner, _⟩ := VEnv.RecursorData.singletonEquation_eq he
  obtain ⟨S, E, hS, hE, W⟩ := InductiveSignature.RecursorData.propElim_wf henv V.registered
    V.large V.zero V.levels_wf hlen ⟨index, howner⟩
  cases Option.some.inj (hS.symm.trans V.layout_eq)
  cases Option.some.inj (hE.symm.trans V.elim_eq)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ := GuardedSingleton.registered_opened_args henv hΓ
    V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht W
  change ProofShape.CarrierRecoveredCompare Step _ true _ _
  rw [proof_indices_family_erasure heq W hctx hindices hps hargs]
  exact .base (.leaf .refl)

/-- Every typed realization of valid singleton code with propositional
indices computes. The actual raw guard is supplied by erasure equality. -/
theorem TypedComputationEq.proof_indices_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    {C : SingletonPrefixCode} (V : C.Valid)
    (hindices : PropTelescope env univs (C.data.propParams C.levels).reverse C.layout.indices)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : env.HasType univs Γ (mkApps (.const C.data.name C.levels) args) T) :
    TypedComputationEq D Γ (mkApps (.const C.data.name C.levels) args) program.rhs T := by
  let Step := ErasedStaticStructureEtaExpansionStage D 0
  have hstep : ErasedScopedPrimitiveDescent Step := erased_static_structure_eta_expansion_stage_descent heq hs 0
  have HG := V.proof_indices_guard (Step := Step) heq hindices hΓ hg ⟨_, ht⟩
  have HC := V.checkWith heq (erased_carrier_recovered_family_descent hstep) hΓ hg ⟨_, ht⟩ HG
  have HE := (show env.IsDefEqU univs Γ _ _ from ⟨_, HC.defeq henv hΓ⟩).of_l henv hΓ ht
  refine .step HE ?_
  by_cases hp : IsProof Γ (mkApps (.const C.data.name C.levels) args)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
    exact .refl
  have EE := proofErase_const_spine hΓ ht hp
  have HT : ProofShape.TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const C.data.name C.levels) (args.map (proofErase Γ))) :=
    ⟨Γ, _, _, hΓ, rfl, ht, EE⟩
  rw [EE, V.output_eq heq hΓ hg HC hp]
  exact .base ⟨1, .inr (.inl ⟨HT, .intro V (by simpa only [List.length_map] using ha)
    (V.telescope_eq hΓ hg ⟨_, ht⟩) ((V.guardWith_iff heq hΓ hg ⟨_, ht⟩).2 HG)⟩)⟩

end Lean4Lean.VEnv.Strengthening
