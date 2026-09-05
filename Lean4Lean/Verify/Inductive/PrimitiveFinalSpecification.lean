import Lean4Lean.Verify.Inductive.PrimitiveFinalEnvironment
import Lean4Lean.Verify.Inductive.PrimitiveDispatch
import Lean4Lean.Verify.Inductive.PrimitiveSpecification

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The primitive execution path retains its independent source judgment and
complete final model without any equality-bootstrap premise. -/
theorem VerifiedSemanticPrimitiveInductiveRunResultSourceAligned.extendSafeWithSpecification
    {ves : VEnvs}
    (Hrun : VerifiedSemanticPrimitiveInductiveRunResultSourceAligned source
      (ves.venv .safe) nparams types numNested outEnv)
    (wf : ves.WF source.env) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (InductiveSpecificationResult (ves.venv .safe)
        source.lparams nparams types (source.safety != .safe)
        (ves'.venv .safe)) := by
  rcases Hrun with
    ⟨c', stats, depth, _commonParams, _commonLevel, Hc', henv, hsafety,
      hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hshape,
      Hphases⟩
  have wf' : ves.WF c'.env := by simpa [henv] using wf
  have Hphases' : SemanticPrimitiveRunWithStatsResult c' stats nparams
      depth (ves.venv .safe) types.toArray (c'.safety != .safe) outEnv := by
    simpa [hvenv, hsafety] using Hphases
  have Hshape' : PrimitiveInductiveShape c'.lparams nparams
      types.toArray.toList (c'.safety != .safe) := by
    simpa [hsafety] using Hshape
  rcases Hphases'.extendSafeExact wf' Hshape' with
    ⟨ves', decl, envTypes, envCtors, wf'', hle, hcore, hadd⟩
  refine ⟨ves', wf'', hle, ⟨?_⟩⟩
  exact {
    decl := decl
    envTypes := envTypes
    envCtors := envCtors
    source := by simpa [hlparams, hsafety] using hcore
    extension := hadd
  }

/-- Complete primitive `AddInductive.run` refinement without an
equality-bootstrap premise. -/
theorem AddInductive.run.primitiveFinalSpecificationModelWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
    (hsource : Hc.venv = ves.venv .safe)
    (Hshape : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe))
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        Nonempty (InductiveSpecificationResult (ves.venv .safe) c.lparams
          nparams types (c.safety != .safe) (ves'.venv .safe)) := by
  have Hrun := AddInductive.run.primitiveSemanticSourceAlignedWF
    nparams numNested Hc wf.inductivesClosed Hshape hctx hnonempty
    HnotPartial
  exact Hrun.mono fun outEnv Hresult => by
    have Hresult' : VerifiedSemanticPrimitiveInductiveRunResultSourceAligned
        c (ves.venv .safe) nparams types numNested outEnv := by
      simpa [hsource] using Hresult
    exact Hresult'.extendSafeWithSpecification wf

/-- Primitive post-lowering refinement with no equality-bootstrap premise. -/
theorem Environment.addInductiveAfterLowering.primitiveFinalSpecificationModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WF env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (htypes : res.types = types)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      true fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (InductiveSpecificationResult (ves.venv .safe) lparams
            nparams types isUnsafe (ves'.venv .safe)) := by
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
  have Hrun := AddInductive.run.primitiveFinalSpecificationModelWF
    (c := c) (ves := ves) nparams 0 Hc wf' hsource Hshape' hctx
    hnonempty hnotPartial
  unfold Environment.addInductiveAfterLowering
  rw [haux, htypes]
  simpa [c, primitiveAddInductiveContext] using Hrun

/-- End-to-end primitive refinement without an equality-bootstrap premise. -/
theorem Environment.addInductive.primitiveFinalSpecificationModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe true fuel).WF
      fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (InductiveSpecificationResult (ves.venv .safe) lparams
            nparams types isUnsafe (ves'.venv .safe)) := by
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hlowering := ElimNestedInductive.run'.primitiveNoopWF env
    fuel.inductiveFuel lparams nparams types isUnsafe Hshape
  have Hcombined := Hsources.bind fun _ _ =>
    Hlowering.bind fun res Hres =>
      Environment.addInductiveAfterLowering.primitiveFinalSpecificationModelWF
        env lparams nparams types isUnsafe fuel res ves wf Hshape
        Hres.1 Hres.2
  simpa [Environment.addInductive] using Hcombined

/-- Checked primitive declaration refinement without an equality-bootstrap
premise. -/
theorem addInductiveDeclaration.primitiveFinalSpecificationModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WF env)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WF outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          Nonempty (InductiveSpecificationResult (ves.venv .safe) lparams
            nparams types isUnsafe (ves'.venv .safe)) := by
  have Hrun := Environment.addInductive.primitiveFinalSpecificationModelWF
    env lparams nparams types isUnsafe fuel ves wf Hshape
  have hcheck := (checkPrimitiveInductive_eq_true_iff env lparams nparams
    types isUnsafe).mpr Hshape
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun

end VerifyInductive
end Lean4Lean
