import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Chained parameter agreement for registered projections

`Ordered.projectionShape` relates the header and constructor parameter
telescopes of a registered projection entry to one common declaration
parameter context.  Composing the two conversions needs transitivity of
definitional equality across differently typed sides, which is available only
through the uniqueness-of-typing development; the composed form is therefore
kept in this separate module.
-/

namespace Lean4Lean
namespace VEnv

/-- Compose two context conversions over the empty base.  The domain proof of
the second conversion is transported back across the already composed prefix
before transitivity is applied. -/
theorem IsDefEqCtx.trans_empty (henv : VEnv.WF env)
    (H₁ : IsDefEqCtx env U [] Γ₁ Γ₂) (H₂ : IsDefEqCtx env U [] Γ₂ Γ₃) :
    IsDefEqCtx env U [] Γ₁ Γ₃ := by
  induction H₁ generalizing Γ₃ with
  | zero => exact H₂
  | @succ Γ₁ Γ₂ A₁ A₂ u H₁ hdom ih =>
    cases H₂ with
    | succ H₂ hdom₂ =>
      have Hprefix := ih H₂
      have hdom₂' := hdom₂.defeqDFC henv.ordered (H₁.symm henv.ordered)
      exact .succ Hprefix (hdom.trans_r henv H₁.isType hdom₂')

/-- Registered projection metadata determines definitionally equal parameter
telescopes for the family header and for the raw constructor type, together
with the exact index arity and result sort of the header. -/
theorem Ordered.projectionShape_params (henv : VEnv.WF env)
    {typeName : Name} {info : VProjectionInfo}
    (hproj : env.projections typeName info) :
    ∃ typeConst normalized ownParams rest exprType ctorParams tail,
      env.constants typeName = some typeConst ∧
      env.IsDefEq info.uvars [] typeConst.type normalized exprType ∧
      normalized.takeForalls info.nparams = some (ownParams, rest) ∧
      info.ctorType.takeForalls info.nparams = some (ctorParams, tail) ∧
      env.IsDefEqCtx info.uvars [] ownParams.reverse ctorParams.reverse ∧
      ∃ indices result,
        rest.takeForalls info.nindices = some (indices, result) ∧
        env.IsDefEq info.uvars (indices.reverse ++ ownParams.reverse) result
          (.sort info.resultLevel) (.sort (.succ info.resultLevel)) := by
  rcases henv.ordered.projectionShape hproj with
    ⟨decl, type, ctor, _, _, _, _, huvars, hnparams, hindices, hlevel, _,
      hctorType, hlookup, _, ⟨params, Hshape, Hparams⟩, _⟩
  rcases Hshape with
    ⟨normalized, ownParams, rest, indices, result, exprType, hnormalized,
      hownParams, hindicesTake, HownParams, hresult⟩
  rcases Hparams with ⟨ctorParams, tail, hctorParams, HctorParams⟩
  rw [← huvars, ← hnparams, ← hindices, ← hlevel, ← hctorType]
  refine ⟨type.toVConstant, normalized, ownParams, rest, exprType, ctorParams,
    tail, hlookup, hnormalized, hownParams, hctorParams, ?_, indices, result,
    hindicesTake, hresult⟩
  exact IsDefEqCtx.trans_empty henv (HownParams.symm henv.ordered) HctorParams

end VEnv
end Lean4Lean
