import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureFields

/-! # Recovering structure equality between two neutral endpoints

A recovered family determines the parameters below insertion. Both endpoints
can then be expanded, and dependent fields compared at sequentially aligned
types. The remaining premise is comparison of projections; this module does
not assume closure or completeness of the scoped comparison relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Two majors at the same unindexed structure family compare by their fields.
The field premise is required only after the dependent spine aligns its types.
Neither major needs to have a constructor head. -/
theorem structure_neutral_fields (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections family info) (hp : ps.length = info.nparams)
    (hx : info.nindices = 0)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (ha : env.HasType univs Γ a (VExpr.mkApps (.const family ls) ps))
    (hb : env.HasType univs Γ b (VExpr.mkApps (.const family ls) ps))
    (H : ∀ i, i < info.numFields → ∀ T,
      env.HasType univs Γ (.proj family i a) T →
      env.HasType univs Γ (.proj family i b) T →
      env.IsDefEqU univs Γ (.proj family i a) (.proj family i b)) :
    env.IsDefEqU univs Γ a b := by
  have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx ha).2 hadm
  have hexpb := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hb).2 hadm
  have HE := structure_spine_recursive_fields hΓ hi hp hx
    (fields := (List.range info.numFields).map (fun i => .proj family i a))
    (by simp) hb hexpa hexpb (by
      intro i hj T hia hib
      simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range] at hia ⊢
      exact H i hj T hia hib)
  exact (show env.IsDefEqU univs Γ a (structExpand family info ls ps a) from
    ⟨_, (IsDefEq.structEta hi hp hx ha hexpa).symm⟩).trans henv hΓ HE

/-- Type recovery of a lifted structure family reconstructs its exact lower
parameters and the left endpoint's original family typing. No inverse typing
weakening is assumed. This fact is independent of the number of fields. -/
theorem proofErase_structure_recovery_descend {info : VProjectionInfo}
    (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a A)
    (hp : args.length = info.nparams)
    (HR : ProofShape.TypeRecovery Step (contextOracle (proofEraseCtx Γ'))
      ((proofErase Γ a).liftN n k) (ProofShape.mkApps (.const family ls) args)) :
    ∃ ps, ps.length = info.nparams ∧
      env.HasType univs Γ a (VExpr.mkApps (.const family ls) ps) ∧
      ps.map (fun p => (proofErase Γ p).liftN n k) = args := by
  rw [proofEraseCtx_oracle] at HR
  obtain ⟨F, haF, EF⟩ := proofErase_typeRecovery_descend hstep hΓ hΓ' W
    (ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W) ha HR
  obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv EF
  obtain ⟨ps, rfl, Eps⟩ := proofErase_const_spine_inv Es
  rw [Eps] at Eargs
  simp only [List.map_map, Function.comp_def] at Eargs
  refine ⟨ps, ?_, haF, Eargs.symm⟩
  have Hlen := congrArg List.length Eargs
  simpa only [List.length_map, hp] using Hlen.symm

/-- A recovered structure family permits comparison of arbitrary common-typed
endpoints below insertion, provided their lower projections compare at aligned
types. Supplying those recursive projection comparisons remains the explicit
missing obligation for a recursively closed neutral-structure certificate. -/
theorem proofErase_neutral_structure_descend
    (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : args.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (HT : env.IsDefEqU univs Γ A B)
    (HR : ProofShape.TypeRecovery Step (contextOracle (proofEraseCtx Γ'))
      ((proofErase Γ a).liftN n k) (ProofShape.mkApps (.const family ls) args))
    (H : ∀ i, i < info.numFields → ∀ T,
      env.HasType univs Γ (.proj family i a) T →
      env.HasType univs Γ (.proj family i b) T →
      env.IsDefEqU univs Γ (.proj family i a) (.proj family i b)) :
    env.IsDefEqU univs Γ a b := by
  obtain ⟨ps, hps, haF, _⟩ := proofErase_structure_recovery_descend hstep hΓ hΓ' W ha hp HR
  have hbF := hb.defeqU_r henv hΓ (HT.symm.trans henv hΓ (ha.uniqU henv hΓ haF))
  exact structure_neutral_fields hΓ hi hps hx hadm haF hbF H

/-- Existing recursive projection certificates can replay the new two-major
root rule. Proof projections use common-type irrelevance directly. Requiring
certificates for every raw projection is sufficient, but does not claim coverage
of all equal structures, or closure under arbitrary typed substitution. -/
theorem proofErase_scoped_neutral_structure_descend
    (hstep : ErasedPrimitiveDescent Step)
    (hscoped : ErasedScopedPrimitiveDescent ScopedStep)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : args.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (HT : env.IsDefEqU univs Γ A B)
    (HR : ProofShape.TypeRecovery Step (contextOracle (proofEraseCtx Γ'))
      ((proofErase Γ a).liftN n k) (ProofShape.mkApps (.const family ls) args))
    (H : ∀ i, i < info.numFields → ScopedCompare ScopedStep (proofEraseCtx Γ') true
      (.proj family i ((proofErase Γ a).liftN n k))
      (.proj family i ((proofErase Γ b).liftN n k))) :
    env.IsDefEqU univs Γ a b := by
  apply proofErase_neutral_structure_descend hstep hΓ hΓ' W hi hx hp hadm ha hb HT HR
  intro i hj T hia hib
  by_cases hpa : IsProof Γ (.proj family i a)
  · obtain ⟨P, hiaP, hP⟩ := hpa
    have hibP := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaP)
    exact ⟨_, IsDefEq.proofIrrel hP hiaP hibP⟩
  have hpb : ¬ IsProof Γ (.proj family i b) := by
    rintro ⟨P, hibP, hP⟩
    exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
  have Ea : proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) := if_neg hpa
  have Eb : proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) := if_neg hpb
  have HC : ScopedCompare ScopedStep (proofEraseCtx Γ') true
      ((proofErase Γ (.proj family i a)).liftN n k)
      ((proofErase Γ (.proj family i b)).liftN n k) := by
    simpa only [Ea, Eb, ProofShape.liftN] using H i hj
  obtain ⟨_, hT⟩ := hia.isType henv hΓ
  exact (proofErase_scoped_compare_descend hscoped hΓ hΓ' W rfl hia hib HC).1 (.refl ⟨_, hT⟩)

end Lean4Lean.VEnv.Strengthening
