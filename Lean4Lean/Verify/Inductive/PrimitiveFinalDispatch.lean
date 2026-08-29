import Lean4Lean.Verify.Inductive.PrimitiveFinalEnvironment
import Lean4Lean.Verify.Inductive.PrimitiveDispatch

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Primitive post-lowering execution reaches the complete safety-indexed
model.  The nested result is the certified primitive no-op, so the production
path is exactly the source-aligned primitive checker. -/
theorem Environment.addInductiveAfterLowering.primitiveFinalEnvironmentEqReadyOrAbsentWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env) (hEq : EqReadyOrAbsent env ves)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (htypes : res.types = types)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      true fuel res).WF fun outEnv =>
        exists decl : VInductDecl, exists ves' : VEnvs,
          ves'.WF outEnv /\ EqReadyOrAbsent outEnv ves' /\
          forall safety, ves.venv safety <= ves'.venv safety := by
  let c := primitiveAddInductiveContext env lparams isUnsafe fuel
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  have Hshape' : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe) := by
    simpa [c, primitiveAddInductiveContext] using Hshape
  have hnonempty : 0 < types.toArray.size := by
    rcases Hshape with ⟨_, _, _, hbool | ⟨binderName, binderInfo, hnat⟩⟩
    · simp [hbool]
    · simp [hnat]
  have hnotPartial : c.safety ≠ .partial := by
    simp [c, primitiveAddInductiveContext]
  have wf' : ves.WF c.env := by
    simpa [c, primitiveAddInductiveContext] using wf
  let Hc : ContextWF c := by
    simpa [c, primitiveAddInductiveContext, initialContext] using
      ContextWF.initial wf .safe lparams true fuel
  have hsource : Hc.venv = ves.venv .safe := rfl
  have hctx : Hc.mlctx.vlctx = [] := rfl
  have Hrun := AddInductive.run.primitiveFinalEnvironmentEqReadyOrAbsentWF
    (c := c) (ves := ves) nparams 0 Hc wf' hsource hEq Hshape'
    hctx hnonempty hnotPartial
  unfold Environment.addInductiveAfterLowering
  rw [haux, htypes]
  simpa [c, primitiveAddInductiveContext] using Hrun

/-- End-to-end primitive branch of `Environment.addInductive`, including
source checks and certified no-op nested lowering. -/
theorem Environment.addInductive.primitiveFinalEnvironmentEqReadyOrAbsentWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env) (hEq : EqReadyOrAbsent env ves)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe true fuel).WF
      fun outEnv => exists decl : VInductDecl, exists ves' : VEnvs,
        ves'.WF outEnv /\ EqReadyOrAbsent outEnv ves' /\
        forall safety, ves.venv safety <= ves'.venv safety := by
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hlowering := ElimNestedInductive.run'.primitiveNoopWF env
    fuel.inductiveFuel lparams nparams types isUnsafe Hshape
  have Hcombined := Hsources.bind fun _ _ =>
    Hlowering.bind fun res Hres =>
      Environment.addInductiveAfterLowering.primitiveFinalEnvironmentEqReadyOrAbsentWF env
        lparams nparams types isUnsafe fuel res ves wf hEq Hshape
        Hres.1 Hres.2
  simpa [Environment.addInductive] using Hcombined

/-- Checked declaration dispatch for canonical primitive Bool/Nat preserves
the complete environment model across both phases of `Eq` bootstrap. -/
theorem addInductiveDeclaration.primitiveFinalEnvironmentEqReadyOrAbsentWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env) (hEq : EqReadyOrAbsent env ves)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        exists decl : VInductDecl, exists ves' : VEnvs,
          ves'.WF outEnv /\ EqReadyOrAbsent outEnv ves' /\
          forall safety, ves.venv safety <= ves'.venv safety := by
  have Hrun := Environment.addInductive.primitiveFinalEnvironmentEqReadyOrAbsentWF env
    lparams nparams types isUnsafe fuel ves wf hEq Hshape
  have hcheck := (checkPrimitiveInductive_eq_true_iff env lparams nparams
    types isUnsafe).mpr Hshape
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun

end VerifyInductive
end Lean4Lean
