import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLeastFailureBodyRoot

/-! # Recover the sort of every actual pair observer

A registered dependent pair with no universe parameters determines the type of
its first projection independently of the selected major. Consequently every
actual observer run has the sorted certificate required to exclude administrative
roots, without changing its raw competitor predicate or its cost.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_proj_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- An actually typed constructor with empty universe arguments forces its
registered family to have no universe parameters. -/
theorem TypedSource.constructor_uvars_zero
    (hi : env.projections family info)
    (H : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) fields)) :
    info.uvars = 0 := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := H
  obtain ⟨actual, rfl, Efields⟩ := proofErase_const_spine_inv Ee
  obtain ⟨ci, Hci, _, hls⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at Hci
  cases Option.some.inj Hci
  exact hls.symm

/-- Every typed first projection of this monomorphic parameterless pair has
its registered sort, even when its actual major was supplied by later frames.
The projection's own typing supplies its elimination guard. -/
theorem TypedSource.pair_first_projection_sort
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (H : TypedSource Δ (.proj family 0 major)) :
    ControlTyping Δ (.proj family 0 major) (.sort (.succ .zero)) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := H
  obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ee
  obtain ⟨info', levels, params, indices, sm, F, v, hi', hw, hl, hparams, hindices,
    hfield, hF, hm, hclosed, hguard⟩ := ht.proj_inv henv hΓ
  obtain rfl := henv.ordered.projections_unique hi' hi
  have EL : levels = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst levels
  have ht' : env.HasType univs Γ (.proj family 0 m) (.sort (.succ .zero)) := by
    apply projection_at_recovered_family henv hΓ hi ⟨_, ht⟩ hm.hasType.2
    simp [VProjectionInfo.fieldType, hp, hu, hshape,
      VProjectionInfo.instantiateProjectionParameters, VProjectionInfo.instantiateProjectionFields]
  exact ⟨Γ, .proj family 0 m, hΓ, EΓ, ht', Ee⟩

/-- Recover the final observer's sort through every consuming, identity and
retained frame. The run, raw competitors and exact cost are unchanged. -/
theorem PiInertProjectionContinuationRun.pair_sorted
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (H : PiInertProjectionContinuationRun D Ω family 0 out Δ K e ck) :
    PiInertSortedProjectionContinuationRun D Ω family 0 out (.succ .zero) Δ K e ck := by
  induction H with
  | projection HT HP R => exact .projection HT (TypedSource.pair_first_projection_sort hi hu hp hshape HP) R
  | application HT W HNext RNext _ ih => exact .application HT W HNext RNext ih
  | retained HT SD RD WI _ ih => exact .retained HT SD RD WI ih

/-- Every pair observer minimum acquires the sorted certificate without a
new choice of body endpoint, continuation, or budget. -/
theorem PiInertProjectionContinuationMinimum.pair_sorted
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (H : PiInertProjectionContinuationMinimum D Ω family 0 out Δ source cost) :
    PiInertSortedProjectionContinuationMinimum D Ω family 0 out (.succ .zero) Δ source cost := by
  obtain ⟨K, n, cb, ck, endpoint, HT, RB, HK, hc, HM⟩ := H
  exact ⟨K, n, cb, ck, endpoint, HT, RB, HK.pair_sorted hi hu hp hshape, hc, HM⟩

end Lean4Lean.VEnv.Strengthening
