import Lean4Lean.Verify.Inductive.PrimitiveSemanticAddInduct
import Lean4Lean.Verify.Inductive.PrimitiveDispatch

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Primitive post-lowering execution with the declaration and abstract
header environment synthesized by the successful executable checks. -/
theorem Environment.addInductiveAfterLowering.primitiveSemanticWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result)
    (Hc : ContextWF
      (primitiveAddInductiveContext env lparams isUnsafe fuel))
    (Hclosed : MutualInductivesClosed env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (hctx : Hc.mlctx.vlctx = [])
    (htypes : res.types = types)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      true fuel res).WF fun outEnv =>
        VerifiedSemanticPrimitiveInductiveRunResult
          (primitiveAddInductiveContext env lparams isUnsafe fuel)
          nparams types 0 outEnv := by
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
  have Hrun := AddInductive.run.primitiveSemanticWF (c := c) nparams 0
    Hc Hclosed Hshape' hctx hnonempty hnotPartial
  unfold Environment.addInductiveAfterLowering
  rw [haux, htypes]
  simpa [c, primitiveAddInductiveContext] using Hrun

/-- End-to-end primitive branch of `Environment.addInductive`, with no
preselected abstract declaration data. -/
theorem Environment.addInductive.primitiveSemanticWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (Hc : ContextWF
      (primitiveAddInductiveContext env lparams isUnsafe fuel))
    (Hclosed : MutualInductivesClosed env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (hctx : Hc.mlctx.vlctx = []) :
    (Environment.addInductive env lparams nparams types isUnsafe true fuel).WF
      (VerifiedSemanticPrimitiveInductiveRunResult
        (primitiveAddInductiveContext env lparams isUnsafe fuel)
        nparams types 0) := by
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hlowering := ElimNestedInductive.run'.primitiveNoopWF env
    fuel.inductiveFuel lparams nparams types isUnsafe Hshape
  have Hcombined := Hsources.bind fun _ _ =>
    Hlowering.bind fun res Hres =>
      Environment.addInductiveAfterLowering.primitiveSemanticWF env lparams
        nparams types isUnsafe fuel res Hc Hclosed Hshape hctx
        Hres.1 Hres.2
  simpa [Environment.addInductive] using Hcombined

/-- Non-vacuous production declaration dispatch for canonical primitive
Bool/Nat, refining the independent `AddInduct` judgment without caller
skeleton or header-environment witnesses. -/
theorem addInductiveDeclaration.primitiveSemanticWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (Hc : ContextWF
      (primitiveAddInductiveContext env lparams isUnsafe fuel))
    (Hclosed : MutualInductivesClosed env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (hctx : Hc.mlctx.vlctx = []) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun _ =>
        ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
          c'.env = (primitiveAddInductiveContext env lparams isUnsafe fuel).env ∧
          c'.safety =
            (primitiveAddInductiveContext env lparams isUnsafe fuel).safety ∧
          c'.lparams =
            (primitiveAddInductiveContext env lparams isUnsafe fuel).lparams ∧
          ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
            VEnv.AddInduct Hc'.venv decl finalVEnv := by
  have Hrun := Environment.addInductive.primitiveSemanticWF env lparams
    nparams types isUnsafe fuel Hc Hclosed Hshape hctx
  have Hmodel := Hrun.mono fun _ Hout => Hout.addInductCanonical
  have hcheck := (checkPrimitiveInductive_eq_true_iff env lparams nparams
    types isUnsafe).mpr Hshape
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hmodel

end VerifyInductive
end Lean4Lean
