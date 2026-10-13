import Lean4Lean.Theory.Typing.Strengthening.ProjectionComputation

/-! # Projection cancels nested structure expansions

The parameters of an eta expansion need not be scoped below an inserted binder:
selecting a field discards them. The cancellation is computational, requires only
registration, arity, and a valid field index, and remains valid for arbitrarily
many nested expansions. It does not by itself eliminate eta throughout a path.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Nested root structure expansions, with independently chosen levels and
parameters at every expansion. There are no typing or scope assumptions. -/
inductive RecordExpansion (s : Name) (info : VProjectionInfo) : VExpr → VExpr → Prop where
  | refl : RecordExpansion s info e e
  | expand : RecordExpansion s info e out → ps.length = info.nparams →
      RecordExpansion s info e (structExpand s info ls ps out)

variable [Params]

/-- Projection immediately cancels a structure expansion. Its parameters and
levels can be arbitrary: only their number matters for this syntactic step. -/
theorem ProjectionCompute.cancel_struct (hinfo : env.projections s info)
    (hps : ps.length = info.nparams) (hi : i < info.numFields) :
    ProjectionCompute D (.proj s i (structExpand s info ls ps e)) (.proj s i e) := by
  apply ProjectionCompute.projIota hinfo
  · simp [hps]
  · rw [List.getElem?_append_right (by omega), hps, Nat.add_sub_cancel_left]
    simp [hi]

/-- Any finite nesting of root expansions disappears under one field projection.
Each cancellation is an actual saturated projection computation. -/
theorem RecordExpansion.cancel_projection (R : RecordExpansion s info e out)
    (hinfo : env.projections s info) (hi : i < info.numFields) :
    ProjectionCompute D (.proj s i out) (.proj s i e) := by
  induction R with
  | refl => exact .base .refl
  | expand _ hp ih => exact (ProjectionCompute.cancel_struct hinfo hp hi).trans ih

/-- Projection cancellation is preserved by any further application spine. -/
theorem ProjectionCompute.mkApps (R : ProjectionCompute D f f') (args : List VExpr) :
    ProjectionCompute D (mkApps f args) (mkApps f' args) := by
  induction args generalizing f f' with
  | nil => exact R
  | cons a args ih => exact ih (.app R (.base .refl))

/-- Captured structure parameters can disappear before a computational head is
exposed. The resulting projection path need not itself start with scoped syntax. -/
theorem RecordExpansion.cancel_projection_lift (R : RecordExpansion s info (e.lift' ρ) out)
    (hinfo : env.projections s info) (hi : i < info.numFields) :
    ProjectionCompute D (.proj s i out) ((VExpr.proj s i e).lift' ρ) :=
  R.cancel_projection hinfo hi

/-- The original projection is genuinely typed below and its typing can be
weakened above after cancellation. No type is assigned to the arbitrary expanded
source, and no scopedness of its captured parameters is inferred. -/
theorem RecordExpansion.cancel_to_typed_projection
    (R : RecordExpansion s info (e.lift' ρ) out)
    (hinfo : env.projections s info) (hi : i < info.numFields)
    (W : Ctx.Lift' ρ Γ Γ') (ht : HasType env univs Γ (.proj s i e) T) :
    ProjectionCompute D (.proj s i out) ((VExpr.proj s i e).lift' ρ) ∧
      HasType env univs Γ' ((VExpr.proj s i e).lift' ρ) (T.lift' ρ) :=
  ⟨R.cancel_projection_lift hinfo hi, ht.weak' henv W⟩

/-- If a genuine eta expansion and its projection are typed, cancellation is
also an equality at the expanded projection's exact type. -/
theorem RecordExpansion.cancel_projection_typed
    (R : RecordExpansion s info e out)
    (hinfo : env.projections s info) (hi : i < info.numFields)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : HasType env univs Γ (.proj s i out) T) :
    IsDefEq env univs Γ (.proj s i out) (.proj s i e) T := by
  have hc : ProjectionCompute .empty (.proj s i out) (.proj s i e) :=
    R.cancel_projection hinfo hi
  exact hc.simAt (by intro Γ c ls rhs h; exact h.elim) hΓ T ht

end Lean4Lean.VEnv.Strengthening.PureObservation
