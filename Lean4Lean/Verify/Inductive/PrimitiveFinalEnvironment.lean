import Lean4Lean.Verify.Inductive.PrimitiveSemanticRun
import Lean4Lean.Verify.Inductive.CompletedRuleTranslation
import Lean4Lean.Verify.Inductive.Run.EqCanonical

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A successful primitive Bool/Nat run extends the complete environment
model without any premise about the bootstrap state of `Eq`. -/
theorem SemanticPrimitiveRunWithStatsResult.extendSafeExact
    {ves : VEnvs}
    (Hrun : SemanticPrimitiveRunWithStatsResult c stats nparams depth
      (ves.venv .safe) indTypes (c.safety != .safe) outEnv)
    (wf : ves.WFCore c.env) (hcorner : ∀ safety, ProjectionCorner safety c.env (ves.venv safety))
    (Hshape : PrimitiveInductiveShape c.lparams nparams indTypes.toList
      (c.safety != .safe)) :
    exists ves' : VEnvs, exists decl : VInductDecl,
      exists envTypes envCtors : VEnv,
      ves'.WFCore outEnv /\
      (forall safety, ves.venv safety <= ves'.venv safety) /\
      TrInductDeclCore (ves.venv .safe) c.lparams nparams indTypes.toList
        (c.safety != .safe) decl envTypes envCtors /\
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) /\
      VEnvs.CertPres c.env outEnv ves ves' := by
  rcases Hrun with ⟨decl, _ctorEnv, R, ⟨Hrecursors⟩⟩
  have hsafety : c.safety = .safe := by
    have hnotUnsafe : (c.safety != .safe) = false := Hshape.2.2.1
    simpa using hnotUnsafe
  have hnonempty : indTypes.toList ≠ [] := by
    rcases Hshape with ⟨_, _, _, hbool | ⟨binderName, binderInfo, hnat⟩⟩
    · simp [hbool]
    · simp [hnat]
  rcases Hrecursors.canonicalCompletedRuleTranslation with ⟨T⟩
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
    simpa [Hcert, Hcert0, CompletedBlockCertificate.sf_mono, CompletedStagedBlock.sf_mono,
      CompletedBlockCertificate.block] using
      (T.compilation hnonempty).compilesTo
  have Hsemantics : InductiveConstructorsSemanticallyCoherent .safe outEnv
      Hcert.finalVEnv := by
    simpa [Hcert, Hcert0, CompletedBlockCertificate.sf_mono, CompletedStagedBlock.sf_mono,
      CompletedBlockCertificate.finalVEnv] using
    Hrecursors.completedConstructorSemantics
      (wf.constructorSemantics (safety := .safe)) T.rules
  rcases Hcert.extendSafeExact wf hcorner hdecl hcompile
      Hrecursors.productionInductiveOrigins T.recursorProvenance
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
    VEnvs.CertPres.ofOrigin (isUnsafe := false) hle wf'.mono hH fun hfind => ?_⟩
  rcases Hrecursors.ctorOrigin hfind with h | ⟨hu, hc⟩
  · exact .inl h
  · refine .inr ⟨?_, hc⟩
    rw [hu, hsafety]; rfl

end VerifyInductive
end Lean4Lean
