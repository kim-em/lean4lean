import Lean4Lean.Theory.Typing.AnchoredConstructorDisplay
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.AnchoredSourceFuture

/-! Constructor eta provenance comes from the actual original typing-rule
children. Both substituted copies retain their own explicit eta/unit-like
step; a typed formation bridge aligns the right copy's assigned type.
-/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- The original structure-eta rule supplies both endpoint typings. These
finite origins do not assert that a neutral record takes a machine step. -/
theorem ConstructorOrigin.pairedStructEta
    {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
    {source target : List VExpr} {σ τ : Subst}
    (henv : env.Ordered) (targetFormed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {info : VProjectionInfo} {name : Name} {params : List VExpr} {levels : List VLevel}
    {major : VExpr}
    (registered : env.projections name info)
    (paramCount : params.length = info.nparams) (unindexed : info.nindices = 0)
    (majorTyped : env.IsDefEqStrong U source major major (mkApps (.const name levels) params))
    (expansionTyped : env.IsDefEqStrong U source
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => .proj name index major)))
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => .proj name index major)))
      (mkApps (.const name levels) params)) :
    ConstructorOrigin env U registry target
      ((mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => .proj name index major))).subst σ)
      (major.subst σ) ((mkApps (.const name levels) params).subst σ) ∧
    ConstructorOrigin env U registry target
      ((mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => .proj name index major))).subst τ)
      (major.subst τ) ((mkApps (.const name levels) params).subst σ) := by
  have original : ConstructorOrigin env U registry source
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => .proj name index major))) major
      (mkApps (.const name levels) params) :=
    .symm (.eta registered paramCount unindexed majorTyped.defeq expansionTyped.defeq)
  have first := ConstructorOrigin.substitute targetFormed substitutions.left original
  have second := ConstructorOrigin.substitute targetFormed
    (substitutions.right henv targetFormed) original
  obtain ⟨level, formation⟩ := majorTyped.defeq.isType henv substitutions.wf
  have types := formation.substDF henv substitutions.wf targetFormed substitutions
  exact ⟨first, .convert (.single types.symm) second⟩

/-- Unit-like equality is retained as its actual registered zero-field rule,
including when both source endpoints are neutral. -/
theorem ConstructorOrigin.pairedUnitLike
    {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
    {source target : List VExpr} {σ τ : Subst}
    (henv : env.Ordered) (targetFormed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    {info : VProjectionInfo} {name : Name} {params : List VExpr} {levels : List VLevel}
    {left right : VExpr}
    (registered : env.projections name info)
    (paramCount : params.length = info.nparams) (unindexed : info.nindices = 0)
    (noFields : info.numFields = 0)
    (leftTyped : env.IsDefEqStrong U source left left (mkApps (.const name levels) params))
    (rightTyped : env.IsDefEqStrong U source right right (mkApps (.const name levels) params)) :
    ConstructorOrigin env U registry target (left.subst σ) (right.subst σ)
      ((mkApps (.const name levels) params).subst σ) ∧
    ConstructorOrigin env U registry target (left.subst τ) (right.subst τ)
      ((mkApps (.const name levels) params).subst σ) := by
  have original : ConstructorOrigin env U registry source left right
      (mkApps (.const name levels) params) :=
    .unitLike registered paramCount unindexed noFields leftTyped.defeq rightTyped.defeq
  have first := ConstructorOrigin.substitute targetFormed substitutions.left original
  have second := ConstructorOrigin.substitute targetFormed
    (substitutions.right henv targetFormed) original
  obtain ⟨level, formation⟩ := leftTyped.defeq.isType henv substitutions.wf
  have types := formation.substDF henv substitutions.wf targetFormed substitutions
  exact ⟨first, .convert (.single types.symm) second⟩

end Lean4Lean.AnchoredSemantics
