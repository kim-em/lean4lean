import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLevels
import Lean4Lean.Theory.Typing.TypedWorldProofContext

/-! The forward native packet may retain a level-equivalent seed telescope.
These raw context and finite-realization lemmas change that packet without
requesting another semantic interpretation of a synthesized typing proof. -/
namespace Lean4Lean.VEnv
open VExpr AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem contextLevels
    (henv : env.Ordered) (formed : OnCtx source (env.IsType U))
    (equal : List.Forall₂ (EqUpToLevels U) source destination) :
    IsDefEqCtx env U [] source destination := by
  induction equal with
  | nil => exact .zero
  | cons head tail ih =>
    obtain ⟨context, level, formation⟩ := formed
    exact .succ (ih context) (formation.eqUpToLevels henv context head)

/-- Only source declarations change; the actual raw values remain identical. -/
theorem Ctx.SubstEq.nativeSourceLevels
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (typed : Ctx.SubstEq env U target σ σ source)
    (equal : List.Forall₂ (EqUpToLevels U) source destination) :
    Ctx.SubstEq env U target σ σ destination :=
  typed.sourceChain henv hTarget (.single (contextLevels henv typed.wf equal))

/-- Only the finite source scope is inspected, so an arbitrary substitution's
unused tail contributes no universe well-formedness premise. -/
theorem EqUpToLevels.substScoped
    (equal : EqUpToLevels U left right) (scope : left.ClosedN count)
    (values : ∀ i < count, EqUpToLevels U (σ i) (τ i)) :
    EqUpToLevels U (left.subst σ) (right.subst τ) := by
  induction equal generalizing count σ τ with
  | bvar => exact values _ scope
  | const first second levels => exact .const first second levels
  | elim first second levels => exact .elim first second levels
  | sort first second levels => exact .sort first second levels
  | app fn arg ihf iha => exact .app (ihf scope.1 values) (iha scope.2 values)
  | proj child ih => exact .proj (ih scope values)
  | lam domain body ihA ihB | forallE domain body ihA ihB =>
    constructor
    · exact ihA scope.1 values
    · apply ihB scope.2
      intro i hi
      cases i with
      | zero => exact .bvar
      | succ i => exact (values i (Nat.lt_of_succ_lt_succ hi)).weakN

/-- The actual source substitution supplies reflexive level evidence for
all variables used by the original open equation body. -/
theorem Ctx.SubstEq.nativeValueLevels
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (typed : Ctx.SubstEq env U target σ σ source) :
    ∀ i < source.length, EqUpToLevels U (σ i) (σ i) := by
  intro i bound
  obtain ⟨type, lookup⟩ := Lookup.ofLt bound
  exact (EqUpToLevels.refl (CtxStrong.strong henv hTarget).levelWF
    ((typed.lookup lookup).strong henv hTarget)).1

end Lean4Lean.VEnv
