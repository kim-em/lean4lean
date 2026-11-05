import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationDeclarations
import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonWeakening

/-! # Unindexed singleton prefixes as typed computations

With no indices the reconstructed family is literally the requested family.
The raw singleton guard is reflexive, so any typed realization of valid generated
code computes without a native recovery or computational joining assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PropElim
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- An unindexed transported family is syntactically its requested family.
The transported fields do not occur in the family's parameter spine. -/
theorem transported_family_unindexed
    (W : E.WF S params env univs) (hps : ps.length = params.length)
    (hi : S.indices = []) : transportedFamily S params E ps [] m = mkApps E.family ps := by
  have hc : E.ctorIndices = [] := List.eq_nil_of_length_eq_zero (by rw [W.ctorIndices_length, hi]; rfl)
  have hf := transportedFields_length_raw (E := E) (m := m) (i := S.fields.length)
    W.typed.scope hps (show ([] : List VExpr).length = S.indices.length by rw [hi])
  simp only [transportedFamily, branchFamily, hc, List.append_nil, instOuter_mkApps,
    instOuter_closed0 W.family_closed]
  rw [PropElim.instOuter_branch (by simp only [List.length_append, hps, hf]) hps]

/-- At a typed unindexed occurrence, valid code supplies a reflexive erased
family guard at every stage. The residual telescope may still be dependent. -/
theorem SingletonPrefixCode.Valid.unindexed_guard
    {C : SingletonPrefixCode} (V : C.Valid) (hn : C.data.numIndices = 0)
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
  obtain ⟨_, hps, _, _, _, _, _⟩ := GuardedSingleton.registered_opened_args henv hΓ
    V.registered V.large V.zero V.levels_wf hlen howner V.layout_eq V.elim_eq hg ht W
  have hi : C.layout.indices = [] := List.eq_nil_of_length_eq_zero
    ((InductiveSignature.RecursorData.singletonLayout_lengths V.layout_eq).1.trans hn)
  simp only [GuardedSingleton.FamilyGuard, hn, List.take_zero, List.append_nil,
    transported_family_unindexed W hps hi, ErasedFamilyComparison]
  exact .base (.leaf .refl)

/-- Valid unindexed singleton code computes from every typed realization of
its arity. Source typing and the reflexive family guard reconstruct the actual
unfolding check; no pre-existing check or confluence premise is required. -/
theorem TypedComputationEq.unindexed_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    {C : SingletonPrefixCode} (V : C.Valid) (hn : C.data.numIndices = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : args.length = C.arity)
    (hg : C.data.singletonUnfolding env univs C.levels args = some program)
    (ht : env.HasType univs Γ (mkApps (.const C.data.name C.levels) args) T) :
    TypedComputationEq D Γ (mkApps (.const C.data.name C.levels) args) program.rhs T := by
  let Step := ErasedStaticStructureEtaExpansionStage D 0
  have hstep : ErasedScopedPrimitiveDescent Step := erased_static_structure_eta_expansion_stage_descent heq hs 0
  have HG := V.unindexed_guard (Step := Step) hn hΓ hg ⟨_, ht⟩
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

/-- Every generated prefix of a registered unindexed proposition-source
recursor has a chain from source typing alone. All fixed code, layout and
eliminator certificates are derived from registration and generation. -/
theorem TypedComputationEq.generated_unindexed_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hreg : recursorData data.name = some data) (H : RecursorRegistered env data)
    (hl : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hn : data.numIndices = 0)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) args) T) :
    TypedComputationEq D Γ (mkApps (.const data.name levels) args) program.rhs T := by
  obtain ⟨recType, hrec⟩ := H.recursorType_exists
  obtain ⟨_, _, hlv, hlen, heqn, hbody, _⟩ :=
    InductiveSignature.RecursorData.singletonUnfolding_spec hg
  rw [hlv] at hlen
  have hnlevels := hlen.trans (InductiveSignature.RecursorData.singletonEquation_uvars heqn)
  obtain ⟨index, howner, _⟩ := VEnv.RecursorData.singletonEquation_eq heqn
  obtain ⟨S, E, hS, hE, _⟩ := InductiveSignature.RecursorData.propElim_wf
    henv H hl hz hw hnlevels ⟨index, howner⟩
  let C : SingletonPrefixCode := ⟨data, levels, args.length, recType,
    program.equation, program.equationBody, S, E⟩
  have V : C.Valid := ⟨hreg, H, hl, hz, hw, hrec, heqn, hbody, hS, hE, args, program, rfl, hg⟩
  exact TypedComputationEq.unindexed_prefix heq hs V hn hΓ rfl hg ht

end Lean4Lean.VEnv.Strengthening
