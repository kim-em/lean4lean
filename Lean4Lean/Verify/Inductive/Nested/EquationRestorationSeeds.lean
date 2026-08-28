import Lean4Lean.Verify.Inductive.Equation.Canonical
import Lean4Lean.Verify.Inductive.Recursor.Rules

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The `WF` field of the exact generated equation witness already contains
the open RHS typing needed before restoration.  Inverting its literal lambda
and forall wrappers also recovers the exact generated equation context; no
body-typing premise is supplied by a later nested-restoration caller. -/
theorem RecursorPhasesResult.GeneratedEquationWitness.openRhsTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {rule : VDefEq}
    (G : H.GeneratedEquationWitness Us owner howner i hctor rule) :
    OnCtx G.translation.domains.reverse
        (H.outVEnv.IsType rule.uvars) ∧
      H.outVEnv.HasType rule.uvars G.translation.domains.reverse
        G.translation.rhsBody G.translation.typeBody := by
  have Hclosed : H.outVEnv.HasType rule.uvars []
      (VExpr.wrapLams G.translation.domains G.translation.rhsBody)
      (VExpr.wrapForalls G.translation.domains
        G.translation.typeBody) := by
    simpa only [← G.translation.rhs_wrapped,
      ← G.translation.type_wrapped] using G.wf.2
  simpa using VEnv.HasType.wrapLams_inv H.outVEnvWF
    (show OnCtx [] (H.outVEnv.IsType rule.uvars) from trivial) Hclosed

/-- Symmetric LHS extraction from the same generated equation witness. -/
theorem RecursorPhasesResult.GeneratedEquationWitness.openLhsTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {rule : VDefEq}
    (G : H.GeneratedEquationWitness Us owner howner i hctor rule) :
    H.outVEnv.HasType rule.uvars G.translation.domains.reverse
      G.translation.lhsBody G.translation.typeBody := by
  have Hclosed : H.outVEnv.HasType rule.uvars []
      (VExpr.wrapLams G.translation.domains G.translation.lhsBody)
      (VExpr.wrapForalls G.translation.domains
        G.translation.typeBody) := by
    simpa only [← G.translation.lhs_wrapped,
      ← G.translation.type_wrapped] using G.wf.1
  simpa using (VEnv.HasType.wrapLams_inv H.outVEnvWF
    (show OnCtx [] (H.outVEnv.IsType rule.uvars) from trivial) Hclosed).2

/-- Generated equation bodies remain typed after installing the restored
recursors and any later suffix. -/
theorem RecursorPhasesResult.GeneratedEquationWitness.openTypingAfter
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {rule : VDefEq} {laterEnv : VEnv}
    (G : H.GeneratedEquationWitness Us owner howner i hctor rule)
    (henv : H.outVEnv ≤ laterEnv) :
    OnCtx G.translation.domains.reverse
        (laterEnv.IsType rule.uvars) ∧
      laterEnv.HasType rule.uvars G.translation.domains.reverse
        G.translation.lhsBody G.translation.typeBody ∧
      laterEnv.HasType rule.uvars G.translation.domains.reverse
        G.translation.rhsBody G.translation.typeBody := by
  rcases G.openRhsTyping with ⟨hctx, hrhs⟩
  exact ⟨OnCtx.mono (VEnv.IsType.mono henv) hctx,
    (G.openLhsTyping).mono henv, hrhs.mono henv⟩

/-- The staged generated-rule payload determines an exact RHS certificate
before any nested restoration is interpreted.  This exposes the independent
old-recursor guardedness seed used by the restoration proof, rather than
reusing guardedness of a rule already judged against the final recursor
names. -/
theorem BoundGeneratedRecursorRule.iotaRhsCertificate_ofStagedTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Htr : H.StagedIotaRuleTranslation trEnv Us Δ semanticEnv decl block
      owner ctor rule) :
    Nonempty (IotaRhsCertificate (block.recursors.map (·.name))
      Htr.equation.shape.domains
      (Htr.equation.shape.ctorArgs.drop decl.nparams)
      Htr.recursiveArgs Htr.equation.shape.rhsBody) :=
  H.iotaRhsCertificateFor Htr.equation.domains_length
    Htr.equation.rhs_residual Htr.equation.field_args Htr.args
    Htr.fields_recursor_free Htr.recursive_results

/-- In particular, the exact generated RHS body is guarded by the old
generated recursor names. -/
theorem BoundGeneratedRecursorRule.stagedRhsGuarded
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Htr : H.StagedIotaRuleTranslation trEnv Us Δ semanticEnv decl block
      owner ctor rule) :
    Nonempty (∃ fieldVars,
      Htr.equation.shape.rhsBody.GuardedIota
        (block.recursors.map (·.name)) fieldVars 0) := by
  rcases H.iotaRhsCertificate_ofStagedTranslation Htr with ⟨Hrhs⟩
  exact ⟨Hrhs.fieldVars, Hrhs.guarded⟩

end VerifyInductive
end Lean4Lean
