import Lean4Lean.Verify.Inductive.PrimitiveLowering

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The exact checker context selected by the production primitive branch. -/
def primitiveAddInductiveContext (env : Environment) (lparams : List Name)
    (isUnsafe : Bool) (fuel : FuelConfig) : AddInductive.Context :=
  { env := env, lparams := lparams,
    safety := if isUnsafe then .unsafe else .safe,
    allowPrimitive := true, fuel := fuel }

/-- Once primitive lowering has returned its atomic no-op certificate, the
production post-lowering pipeline is exactly the verified primitive
`AddInductive.run`; the nested-restoration branch is definitionally absent. -/
theorem Environment.addInductiveAfterLowering.primitiveClosedWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result)
    (skeleton : VInductDeclSkeleton) (envTypes : VEnv)
    (Hc : ContextWF
      (primitiveAddInductiveContext env lparams isUnsafe fuel))
    (Hclosed : MutualInductivesClosed env)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv lparams nparams types
      isUnsafe skeleton envTypes)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (hctx : Hc.mlctx.vlctx = [])
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
    (hproj : ProjectionConstPreservation)
    (htypes : res.types = types)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      true fuel res).WF fun outEnv =>
        VerifiedPrimitiveInductiveRunResult
          (primitiveAddInductiveContext env lparams isUnsafe fuel)
          skeleton envTypes types 0 outEnv := by
  let c := primitiveAddInductiveContext env lparams isUnsafe fuel
  have hisUnsafe : isUnsafe = false := Hshape.2.2.1
  subst isUnsafe
  have Hdecl' : TrInductDeclSkeletonHeaders Hc.venv c.lparams
      skeleton.nparams types.toArray.toList (c.safety != .safe)
      skeleton envTypes := by
    simpa [c, primitiveAddInductiveContext, Hdecl.nparams] using Hdecl
  have Hshape' : PrimitiveInductiveShape c.lparams skeleton.nparams
      types.toArray.toList (c.safety != .safe) := by
    simpa [c, primitiveAddInductiveContext, Hdecl.nparams] using Hshape
  have hnonempty : 0 < types.toArray.size := by
    rcases Hshape with ⟨_, _, _, hbool | ⟨binderName, binderInfo, hnat⟩⟩
    · simp [hbool]
    · simp [hnat]
  have hnotPartial : c.safety ≠ .partial := by
    simp [c, primitiveAddInductiveContext]
  have Hrun := AddInductive.run.primitiveClosedWF (c := c)
    (skeleton := skeleton) 0 Hc Hclosed Hdecl' Hshape' hctx hnonempty
    hnotPartial
    hloopUArgsReplay hproj
  unfold Environment.addInductiveAfterLowering
  rw [haux, htypes]
  simpa [c, primitiveAddInductiveContext, Hdecl.nparams] using Hrun

/-- End-to-end primitive branch of `Environment.addInductive`: source
checking and nested lowering are executed, their successful result is proved
to be the atomic no-op, and verification rejoins the completed primitive
header/constructor/recursor path. -/
theorem Environment.addInductive.primitiveClosedWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (skeleton : VInductDeclSkeleton) (envTypes : VEnv)
    (Hc : ContextWF
      (primitiveAddInductiveContext env lparams isUnsafe fuel))
    (Hclosed : MutualInductivesClosed env)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv lparams nparams types
      isUnsafe skeleton envTypes)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (hctx : Hc.mlctx.vlctx = [])
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
    (hproj : ProjectionConstPreservation) :
    (Environment.addInductive env lparams nparams types isUnsafe true fuel).WF
      (VerifiedPrimitiveInductiveRunResult
        (primitiveAddInductiveContext env lparams isUnsafe fuel)
        skeleton envTypes types 0) := by
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hlowering := ElimNestedInductive.run'.primitiveNoopWF env
    fuel.inductiveFuel lparams nparams types isUnsafe Hshape
  have Hcombined := Hsources.bind fun _ _ =>
    Hlowering.bind fun res Hres =>
      Environment.addInductiveAfterLowering.primitiveClosedWF env lparams
        nparams types isUnsafe fuel res skeleton envTypes Hc Hclosed Hdecl
        Hshape hctx
        hloopUArgsReplay hproj Hres.1 Hres.2
  simpa [Environment.addInductive] using Hcombined

/-- Non-vacuous declaration-dispatch theorem for the production primitive
Bool/Nat branch.  Successful `checkPrimitiveInductive` dispatch, lowering,
installation, recursor/equation generation, and the independent `AddInduct`
judgment are all composed here. -/
theorem addInductiveDeclaration.primitiveWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (skeleton : VInductDeclSkeleton) (envTypes : VEnv)
    (Hc : ContextWF
      (primitiveAddInductiveContext env lparams isUnsafe fuel))
    (Hclosed : MutualInductivesClosed env)
    (Hdecl : TrInductDeclSkeletonHeaders Hc.venv lparams nparams types
      isUnsafe skeleton envTypes)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (hctx : Hc.mlctx.vlctx = [])
    (hloopUArgsReplay : RecursorLoopUArgsCompletedAlphaCompat)
    (hproj : ProjectionConstPreservation) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun _ =>
        ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
          ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
            VEnv.AddInduct Hc'.venv decl finalVEnv := by
  have Hrun := Environment.addInductive.primitiveClosedWF env lparams
    nparams types isUnsafe fuel skeleton envTypes Hc Hclosed Hdecl Hshape
    hctx hloopUArgsReplay hproj
  have Hmodel := Hrun.mono fun _ Hout => Hout.addInductCanonical hproj
  have hcheck := (checkPrimitiveInductive_eq_true_iff env lparams nparams
    types isUnsafe).mpr Hshape
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hmodel

end VerifyInductive
end Lean4Lean
