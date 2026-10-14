import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedStructureProjection

/-! # Projection iota against finite scoped constructor computation

The constructor path exposes independent field paths. Selecting a field before
or after this path has an exact common computational endpoint, without a
confluence premise or any original typing of the raw constructor arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

namespace ProofShape
/-- Projection iota commutes with arbitrary finite computation of its saturated
constructor major. Its residual field is selected at the same fixed index. -/
theorem ScopedCompute.projection_iota_exchange
    (hctor : ∀ {Δ ls args out}, ¬ Step Δ (mkApps (.const info.ctorName ls) args) out)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hi : env.projections family info) (hlen : args.length = info.nparams + info.numFields)
    (hget : args[info.nparams + i]? = some field)
    (R : ScopedCompute Step Δ (mkApps (.const info.ctorName ls) args) out) :
    ∃ field', ScopedCompute Step Δ field field' ∧
      ScopedCompute Step Δ (.proj family i out) field' := by
  obtain ⟨args', rfl, HR⟩ := R.const_spine hctor
  obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hget
  have hj' : info.nparams + i < args'.length := by rw [← HR.length_eq]; exact hj
  refine ⟨args'[info.nparams + i], HE ▸ HR.getElem_of _ hj hj', ?_⟩
  exact hprim (.projIota hi (HR.length_eq.symm.trans hlen) (List.getElem?_eq_getElem hj'))
end ProofShape

/-- The projection/constructor overlap joins within each finite contextual
prefix stage. Only absence of a selected delta at that constructor is required. -/
theorem proofErase_scoped_prefix_projection_exchange
    (heq : env.HasCanonicalEq) (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hlen : args.length = info.nparams + info.numFields)
    (hget : args[info.nparams + i]? = some field)
    (R : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) Δ
      (ProofShape.mkApps (.const info.ctorName ls) args) out) :
    ∃ field', ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) Δ field field' ∧
      ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) Δ (.proj family i out) field' := by
  apply R.projection_iota_exchange (D := D) ?_
    (fun H => .base (erased_scoped_prefix_stage_core stage (.inl (.inl H)))) hi hlen hget
  intro Δ ls args out H
  exact erased_scoped_prefix_stage_no_rigid heq (henv.projectionCtorRigid hi) hD stage H
    (ProofShape.constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
