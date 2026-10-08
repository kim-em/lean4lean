import Lean4Lean.Verify.Inductive.Primitive.Run
import Lean4Lean.Verify.Inductive.Rules.RuleTranslations
import Lean4Lean.Verify.Inductive.Prelude.EqReady
import Lean4Lean.Verify.Inductive.Primitive.Context
import Lean4Lean.Verify.Inductive.Install.Result

/-!
# The primitive inductive extension

The end of the primitive path of section 3.1 of `docs/inductives/DESIGN.md`: a successful
run on `Bool` or `Nat` yields well-formed models of the output that extend the source models,
together with the source `AddInduct` (`SourceAddInduct`,
`addInductiveDeclaration.primitiveExtensionModelWF`).
None of these theorems has a premise about the prelude `Eq`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A successful primitive Bool/Nat run extends the complete environment
model without any premise about the prelude declaration of `Eq`. -/
theorem PrimitiveInstallation.extendSafeExact
    {ves : VEnvs}
    (Hrun : PrimitiveInstallation c stats nparams depth
      (ves.venv .safe) indTypes (c.safety != .safe) outEnv)
    (wf : ves.WFCore c.env) (htels : ∀ safety, CtorTelescopes safety c.env (ves.venv safety))
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      (c.safety != .safe)) :
    exists ves' : VEnvs, exists decl : VInductDecl,
      exists envTypes envCtors : VEnv,
      ves'.WFCore outEnv /\
      (forall safety, ves.venv safety <= ves'.venv safety) /\
      TrInductDeclCore (ves.venv .safe) c.lparams nparams indTypes.toList
        (c.safety != .safe) decl envTypes envCtors /\
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) /\
      VEnvs.CtorTelescopesPreserved c.env outEnv ves ves' := by
  rcases Hrun with ⟨decl, _ctorEnv, R, ⟨Hrecursors⟩⟩
  have hsafety : c.safety = .safe := by
    have hnotUnsafe : (c.safety != .safe) = false := Hshape.2.2.1
    simpa using hnotUnsafe
  have hnonempty : indTypes.toList ≠ [] := by
    rcases Hshape with ⟨_, _, _, hbool | ⟨binderName, binderInfo, hnat⟩⟩
    · simp [hbool]
    · simp [hnat]
  rcases Hrecursors.generatedRuleTranslation with ⟨T⟩
  let Hcert0 := Hrecursors.blockCertificate T.rules T.rulesWF
  let Hcert := Hcert0.sf_mono (safety := .safe) (by
    rw [hsafety]
    exact DefinitionSafety.le_rfl)
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  have hdecl : decl.WF (ves.venv .safe) :=
    R.formation.declWF Htranslated.sourceWF
  have hcompile : decl.CompilesTo (ves.venv .safe) Hcert.block := by
    simpa [Hcert, Hcert0, BlockCertificate.sf_mono, BlockInstallation.sf_mono,
      BlockCertificate.block] using
      (T.compilation hnonempty).compilesTo
  have Hsemantics : CtorParamsAgree .safe outEnv
      Hcert.installedVEnv := by
    simpa [Hcert, Hcert0, BlockCertificate.sf_mono, BlockInstallation.sf_mono,
      BlockCertificate.installedVEnv] using
    Hrecursors.constructorTyping
      (wf.ctorParamsAgree (safety := .safe)) T.rules
  rcases Hcert.extendSafeExact wf htels hdecl hcompile
      Hrecursors.inductInfosFromDecl T.newRecursorsAligned
      Hrecursors.closed
      (Hrecursors.constructorOwnersPresent wf.constructorOwners) Hsemantics
      (fun safety => Hrecursors.blockEliminatorsReplay T.rules T.rulesWF
        (wf.mono (DefinitionSafety.le_safe (a := safety)))) with
    ⟨ves', wf', hle, hadd, hfinal⟩
  have hH : R.headerVEnv ≤ ves'.venv (if false then .unsafe else .safe) := by
    refine (Hcert.typesLe ?_).trans hfinal
    rw [R.headerValues]
    exact R.core.typesAdded
  refine ⟨ves', decl, R.headerVEnv, R.ctorVEnv, wf', hle, R.core, hadd,
    VEnvs.CtorTelescopesPreserved.ofOrigin (isUnsafe := false) hle wf'.mono hH fun hfind => ?_⟩
  rcases Hrecursors.ctorOrigin hfind with h | ⟨hu, hc⟩
  · exact .inl h
  · refine .inr ⟨?_, hc⟩
    rw [hu, hsafety]; rfl

end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The primitive execution path retains its independent source judgment and
complete model of the output without any premise about the prelude `Eq`. -/
theorem PrimitiveRunResult.extendSafeWithSpecification
    {ves : VEnvs}
    (Hrun : PrimitiveRunResult source
      (ves.venv .safe) nparams types numNested outEnv)
    (wf : ves.WFCore source.env) (htels : ∀ safety, CtorTelescopes safety source.env (ves.venv safety)) :
    ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      VEnvs.CtorTelescopesPreserved source.env outEnv ves ves' ∧
      Nonempty (SourceAddInduct (ves.venv .safe)
        source.lparams nparams types (source.safety != .safe)
        (ves'.venv .safe)) := by
  rcases Hrun with
    ⟨c', stats, depth, _commonParams, _commonLevel, Hc', henv, hsafety,
      hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hshape,
      Hphases⟩
  have wf' : ves.WFCore c'.env := by simpa [henv] using wf
  have hcorner' : ∀ safety, CtorTelescopes safety c'.env (ves.venv safety) := by
    rw [henv]; exact htels
  have Hphases' : PrimitiveInstallation c' stats nparams
      depth (ves.venv .safe) types.toArray (c'.safety != .safe) outEnv := by
    simpa [hvenv, hsafety] using Hphases
  have Hshape' : PrimitiveInductiveShape c'.lparams nparams
      types.toArray.toList (c'.safety != .safe) := by
    simpa [hsafety] using Hshape
  rcases Hphases'.extendSafeExact wf' hcorner' Hshape' with
    ⟨ves', decl, envTypes, envCtors, wf'', hle, hcore, hadd, hcert⟩
  refine ⟨ves', wf'', hle, henv ▸ hcert, ⟨?_⟩⟩
  exact {
    decl := decl
    envTypes := envTypes
    envCtors := envCtors
    source := by simpa [hlparams, hsafety] using hcore
    extension := hadd
  }

/-- Complete primitive `AddInductive.run` refinement without a premise about
the prelude `Eq`. -/
theorem AddInductive.run.primitiveExtensionModelWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WFCore c.env) (htels : ∀ safety, CtorTelescopes safety c.env (ves.venv safety))
    (hsource : Hc.venv = ves.venv .safe)
    (Hshape : PrimitiveInductiveShape c.lparams nparams
      types.toArray.toList (c.safety != .safe))
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial) :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        VEnvs.CtorTelescopesPreserved c.env outEnv ves ves' ∧
        Nonempty (SourceAddInduct (ves.venv .safe) c.lparams
          nparams types (c.safety != .safe) (ves'.venv .safe)) := by
  have Hrun := AddInductive.run.primitiveSourceAlignedWF
    nparams numNested Hc wf.inductivesClosed Hshape hctx hnonempty
    HnotPartial
  exact Hrun.mono fun outEnv Hresult => by
    have Hresult' : PrimitiveRunResult
        c (ves.venv .safe) nparams types numNested outEnv := by
      simpa [hsource] using Hresult
    exact Hresult'.extendSafeWithSpecification wf htels

/-- Primitive post-lowering refinement with no premise about the prelude `Eq`. -/
theorem Environment.addInductiveAfterLowering.primitiveExtensionModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result)
    (ves : VEnvs) (wf : ves.WFCore env) (htels : ∀ safety, CtorTelescopes safety env (ves.venv safety))
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (htypes : res.types = types)
    (haux : res.aux2nested.size = 0) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      true fuel res).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          VEnvs.CtorTelescopesPreserved env outEnv ves ves' ∧
          Nonempty (SourceAddInduct (ves.venv .safe) lparams
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
  have wf' : ves.WFCore c.env := by
    simpa [c, primitiveAddInductiveContext] using wf
  let Hc : ContextWF c := by
    simpa [c, primitiveAddInductiveContext, initialContext] using
      ContextWF.initial wf .safe lparams true fuel htels
  have hsource : Hc.venv = ves.venv .safe := rfl
  have hctx : Hc.mlctx.vlctx = [] := rfl
  have Hrun := AddInductive.run.primitiveExtensionModelWF
    (c := c) (ves := ves) nparams 0 Hc wf' (by simpa [c, primitiveAddInductiveContext] using htels) hsource Hshape' hctx
    hnonempty hnotPartial
  unfold Environment.addInductiveAfterLowering
  rw [haux, htypes]
  simpa [c, primitiveAddInductiveContext] using Hrun

/-- End-to-end primitive refinement without a premise about the prelude `Eq`. -/
theorem Environment.addInductive.primitiveExtensionModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WFCore env) (htels : ∀ safety, CtorTelescopes safety env (ves.venv safety))
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Environment.addInductive env lparams nparams types isUnsafe true fuel).WF
      fun outEnv =>
        ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          VEnvs.CtorTelescopesPreserved env outEnv ves ves' ∧
          Nonempty (SourceAddInduct (ves.venv .safe) lparams
            nparams types isUnsafe (ves'.venv .safe)) := by
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hlowering := ElimNestedInductive.run'.primitiveNoopWF env
    fuel.inductiveFuel lparams nparams types isUnsafe Hshape
  have Hcombined := Hsources.bind fun _ _ =>
    Hlowering.bind fun res Hres =>
      Environment.addInductiveAfterLowering.primitiveExtensionModelWF
        env lparams nparams types isUnsafe fuel res ves wf htels Hshape
        Hres.1 Hres.2
  simpa [Environment.addInductive] using Hcombined

/-- Checked primitive declaration refinement without a premise about the
prelude `Eq`. -/
theorem addInductiveDeclaration.primitiveExtensionModelWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (fuel : FuelConfig)
    (ves : VEnvs) (wf : ves.WFCore env) (htels : ∀ safety, CtorTelescopes safety env (ves.venv safety))
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (Lean4Lean.addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun outEnv =>
        ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
          (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
          VEnvs.CtorTelescopesPreserved env outEnv ves ves' ∧
          Nonempty (SourceAddInduct (ves.venv .safe) lparams
            nparams types isUnsafe (ves'.venv .safe)) := by
  have Hrun := Environment.addInductive.primitiveExtensionModelWF
    env lparams nparams types isUnsafe fuel ves wf htels Hshape
  have hcheck := (checkPrimitiveInductive_eq_true_iff env lparams nparams
    types isUnsafe).mpr Hshape
  simpa [Lean4Lean.addDecl, hcheck, bind, Except.bind] using Hrun

end VerifyInductive
end Lean4Lean
