import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProjectionClosedExamples

/-! # A parameter field is outside declaration-only projection trees

The finite tree inspects a field domain before substituting occurrence
parameters. A field whose domain is a parameter variable therefore defeats
that certificate even when the actual parameter is a literal universe and
the projection is a retained type. This is a coverage boundary, not a
counterexample to strengthening or to the proved substitution laws.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

section FieldShape
variable {env : VEnv}

/-- A free type-parameter head has no declaration-only finite field tree. -/
theorem ProjectionClosedType.not_bvar : ¬ ProjectionClosedType env (.bvar i) := by
  intro H
  generalize E : VExpr.bvar i = A at H
  cases H with
  | terminal H =>
    cases H with
    | sort => cases E
    | data _ _ | fieldless _ _ =>
      have HE := congrArg (fun e => e.getAppFnArgs.1) E
      rw [VExpr.getAppFnArgs_mkApps_const] at HE
      cases HE
  | record _ _ =>
    have HE := congrArg (fun e => e.getAppFnArgs.1) E
    rw [VExpr.getAppFnArgs_mkApps_const] at HE
    cases HE

/-- A polymorphic box's sole field is its type parameter, so its constructor
cannot supply the declaration-only field certificate. -/
theorem StructureReplay.ProjectionClosedFields.not_parameter_field
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hp : info.nparams = 1) (hf : info.numFields = 1) :
    ¬ ProjectionClosedFields env info := by
  intro HF
  have H := HF _ _ hshape (by simp [hp, hf]) 1 (by decide) (by omega)
  exact ProjectionClosedType.not_bvar H

end FieldShape
variable [Params]

/-- At the concrete parameter Type, the box has a retained type projection,
yet no ProjectionClosedImage certificate, even via another convertible assigned
type. Thus the finite declaration tree does not cover all typed record images. -/
theorem projection_closed_parameter_record_boundary
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (VExpr.mkApps (.const family []) [.sort (.succ .zero)]))
    (hi : env.projections family info)
    (hshape : info.ctorType = wrapForalls [.sort (.succ (.succ .zero)), .bvar 0] result)
    (hp : info.nparams = 1) (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hu : info.uvars = 0) (hpos : (info.resultLevel.inst []).IsNeverZero) :
    env.HasType univs Γ (.proj family 0 m) (.sort (.succ .zero)) ∧
    ¬ IsProof Γ (.proj family 0 m) ∧ ¬ ProjectionClosedImage Γ m := by
  have hfield : info.fieldType family [] [.sort (.succ .zero)] 0 m =
      some (.sort (.succ .zero)) := by
    have H := info.fieldType_eq_instOuter (typeName := family) (major := m) hshape
      (levels := []) (by simp [hu]) (params := [.sort (.succ .zero)]) (by simp [hp])
      (index := 0) (by simp [hp])
    simpa [hp, VExpr.instL, VExpr.instOuter, VExpr.instOuterAt, VExpr.inst, VExpr.liftN] using H
  obtain ⟨_, hc⟩ := henv.ordered.constWF (henv.ordered.projectionConstructor hi)
  have hclosed := hc.closedN henv.ordered
    (show OnCtx ([] : List VExpr) (env.IsType info.uvars) from trivial)
  have ht : env.HasType univs Γ (.proj family 0 m) (.sort (.succ .zero)) :=
    .projDF (indexArgs := []) hi (by simp) (by simp [hu]) (by simp [hp])
      (by simp [hx]) hfield (HasType.sort (by trivial)) hm hm hclosed (.inl hpos)
  have hn := not_isProof_of_sort hΓ ht
  refine ⟨ht, hn, ?_⟩
  intro H
  cases H with
  | terminal H => exact H.not_projection hΓ ht hn
  | typed h HA =>
    cases HA with
    | terminal HA => exact (HA.image h).not_projection hΓ ht hn
    | record hi' HF =>
      obtain ⟨_, hC⟩ := h.isType henv hΓ
      obtain ⟨E, _, _⟩ := henv.headInversion.rigid_rigid hΓ
        (henv.projectionRigid hi') (henv.projectionRigid hi)
        ((h.uniqU henv hΓ hm).typeChain henv hΓ hC)
      subst E
      cases henv.ordered.projections_unique hi' hi
      exact StructureReplay.ProjectionClosedFields.not_parameter_field hshape hp hf HF

end Lean4Lean.VEnv.Strengthening
