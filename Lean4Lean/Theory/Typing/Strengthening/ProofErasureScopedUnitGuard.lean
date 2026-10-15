import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryDescent

/-! # A type-recovery guard for neutral unit-like comparisons

A recovered empty-structure family on one endpoint suffices in common-type mode.
Its exact type and parameters reconstruct below binder insertion. This supplies
safe evidence for the missing unitLike comparison, without an untyped middle
shape or an assumed typing-strengthening theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Recovering an unindexed zero-field family on the left endpoint justifies
unitLike comparison at a common original type. This is a proposed root guard;
it is not yet a constructor of the recursively closed scoped comparison. -/
def ProofShape.ScopedUnitGuard (Step : ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (a : ProofShape) : Prop :=
  ∃ family info ls args, env.projections family info ∧ info.nindices = 0 ∧ info.numFields = 0 ∧
    args.length = info.nparams ∧
    TypeRecovery Step (contextOracle Δ) a (ProofShape.mkApps (.const family ls) args)

/-- A recovered unit-like root descends at commonly typed originals. Recovery
reconstructs the family and all parameters below the removed binders; the other
endpoint receives that type by uniqueness and the supplied common-type equation. -/
theorem proofErase_scoped_unit_guard_descend
    (hstep : ErasedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ScopedUnitGuard Step (proofEraseCtx Γ') ((proofErase Γ a).liftN n k))
    (HT : env.IsDefEqU univs Γ A B) : env.IsDefEqU univs Γ a b := by
  obtain ⟨family, info, ls, args, hi, hx, hf, hp, HR⟩ := H
  rw [proofEraseCtx_oracle] at HR
  obtain ⟨F, haF, EF⟩ := proofErase_typeRecovery_descend hstep hΓ hΓ' W
    (ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W) ha HR
  obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv EF
  obtain ⟨originalArgs, rfl, Eoriginal⟩ := proofErase_const_spine_inv Es
  have hlen : originalArgs.length = info.nparams := by
    have Hlen := congrArg List.length Eargs
    rw [Eoriginal] at Hlen
    simpa only [List.length_map, hp] using Hlen.symm
  have hbF := hb.defeqU_r henv hΓ (HT.symm.trans henv hΓ (ha.uniqU henv hΓ haF))
  exact ⟨_, IsDefEq.unitLike hi hlen hx hf haF hbF⟩

/-- At the original context, the recovered unit guard reflects to actual
unitLike equality at the two endpoints' common type. -/
theorem proofErase_scoped_unit_guard_reflect
    (hstep : ErasedPrimitiveDescent Step) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (H : ScopedUnitGuard Step (proofEraseCtx Γ) (proofErase Γ a)) :
    env.IsDefEq univs Γ a b T := by
  obtain ⟨_, hT⟩ := ha.isType henv hΓ
  have HU := proofErase_scoped_unit_guard_descend hstep hΓ hΓ (Ctx.LiftN.zero []) ha hb
    (by simpa only [List.length_nil, ProofShape.liftN_zero] using H) (.refl ⟨_, hT⟩)
  exact HU.of_l henv hΓ ha

open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

/-- An actual variable lookup at a positive-universe empty structure supplies
the guard with no computational type recovery. This covers the two-neutral
counterexample at stage zero and every larger primitive relation. -/
theorem proofErase_scoped_unit_guard_lookup
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs Γ (VExpr.mkApps (.const family ls) ps) (.sort (.succ u)))
    (hl : Lookup Γ i (VExpr.mkApps (.const family ls) ps)) :
    ScopedUnitGuard Step (proofEraseCtx Γ) (proofErase Γ (.bvar i)) := by
  have ht : env.HasType univs Γ (.bvar i) (VExpr.mkApps (.const family ls) ps) := .bvar hl
  have Ei : proofErase Γ (.bvar i) = .bvar i := if_neg (not_proof_at_positive_type hΓ hS ht)
  have ES := proofErase_const_spine hΓ hS (not_isProof_of_sort hΓ hS)
  refine ⟨family, info, ls, ps.map (proofErase Γ), hi, hx, hf,
    by simpa only [List.length_map] using hp, ?_⟩
  rw [Ei, ← ES, proofEraseCtx_oracle, ← erasedTypeOracle_valid hΓ hl]
  exact .bvar

/-- A closed zero-parameter empty structure supplies an explicit two-variable
context where the new guard succeeds and every old finite singleton stage fails.
The original variables have one positive-universe type and an actual unitLike
equality. This is strictness of the proposed root extension, not of a front. -/
theorem scoped_unit_guard_strict
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ (.bvar 0) (.const family ls) ∧
      env.HasType univs Γ (.bvar 1) (.const family ls) ∧
      env.IsDefEq univs Γ (.bvar 0) (.bvar 1) (.const family ls) ∧
      ScopedUnitGuard (fun _ _ => False) (proofEraseCtx Γ) (proofErase Γ (.bvar 0)) ∧
      ∀ stage mode, ¬ ScopedCompare (ErasedScopedTypedSingletonStage D stage) (proofEraseCtx Γ) mode
        (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) := by
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ : OnCtx Γ (env.IsType univs) :=
    ⟨⟨trivial, _, hS⟩, _, hS.weak0 henv.ordered⟩
  have hS' : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have h₀ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  obtain ⟨HE, mid, hm, HL, HR, HN⟩ := scoped_unit_typed_composition_failure
    (Stages := ErasedScopedTypedSingletonStage D) erased_scoped_typed_singleton_stage_head
    hΓ hi (ps := []) hp.symm hx hf hS' h₀ h₁ (by decide)
  exact ⟨Γ, hΓ, h₀, h₁, HE,
    proofErase_scoped_unit_guard_lookup hΓ hi (ps := []) hp.symm hx hf hS' .zero, HN⟩

end Lean4Lean.VEnv.Strengthening
