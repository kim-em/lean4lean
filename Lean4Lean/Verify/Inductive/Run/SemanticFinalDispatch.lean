import Lean4Lean.Verify.Inductive.Run.SemanticFinalEnvironment
import Lean4Lean.Verify.Inductive.Run.SemanticSpecification

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A source-aligned ordinary checker result extends the complete
safety-indexed abstract environment. The result is independent of whether
the source environment has already bootstrapped canonical equality. -/
theorem VerifiedSemanticInductiveRunResultSourceAligned.extendWithSpecification
    {ves : VEnvs}
    (Hrun : VerifiedSemanticInductiveRunResultSourceAligned source sourceEnv
      nparams types numNested outEnv)
    (wf : ves.WFCore source.env) (hcorner : ∀ safety, CtorTelescopes safety source.env (ves.venv safety))
    (hsource : sourceEnv = ves.venv source.safety)
    (hnotPartial : source.safety ≠ .partial)
    (hnonempty : types ≠ []) :
    ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      VEnvs.CertPres source.env outEnv ves ves' ∧
      Nonempty (InductiveSpecificationResult sourceEnv source.lparams nparams types
        (source.safety != .safe)
        (ves'.venv (if source.safety != .safe then .unsafe else .safe))) := by
  rcases Hrun with
    ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
      hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hphases⟩
  have wf' : ves.WFCore c'.env := by
    rw [henv]
    exact wf
  have hcorner' : ∀ safety, CtorTelescopes safety c'.env (ves.venv safety) := by
    rw [henv]; exact hcorner
  have hnonempty' : types.toArray.toList ≠ [] := by
    simpa using hnonempty
  cases hs : source.safety with
  | «unsafe» =>
      have hcSafety : c'.safety = .unsafe := hsafety.trans hs
      have hcVEnv : Hc'.venv = ves.venv .unsafe := by
        exact hvenv.trans (hsource.trans (congrArg ves.venv hs))
      have hproduction :
          (source.safety != .safe) = (c'.safety != .safe) :=
        congrArg (fun safety => safety != .safe) hsafety.symm
      rcases SemanticRunWithStatsResult.extendUnsafeExact Hphases wf' hcorner'
          hcSafety hcVEnv hproduction hnonempty' with
        ⟨ves', decl, envTypes, envCtors, wf'', hle, hcore, hadd, hcert⟩
      refine ⟨ves', wf'', hle, henv ▸ hcert, ?_⟩
      have hspec : InductiveSpecificationResult (ves.venv .unsafe)
          c'.lparams nparams types (source.safety != .safe)
          (ves'.venv .unsafe) := {
        decl := decl
        envTypes := envTypes
        envCtors := envCtors
        source := by simpa using hcore
        extension := hadd
      }
      exact ⟨by simpa [hs, hlparams, hsource] using hspec⟩
  | safe =>
      have hcSafety : c'.safety = .safe := hsafety.trans hs
      have hcVEnv : Hc'.venv = ves.venv .safe := by
        exact hvenv.trans (hsource.trans (congrArg ves.venv hs))
      rcases SemanticRunWithStatsResult.extendSafeExact Hphases wf' hcorner'
          hcSafety hcVEnv hnonempty' with
        ⟨ves', decl, envTypes, envCtors, wf'', hle, hcore, hadd, hcert⟩
      refine ⟨ves', wf'', hle, henv ▸ hcert, ?_⟩
      have hspec : InductiveSpecificationResult (ves.venv .safe)
          c'.lparams nparams types (source.safety != .safe)
          (ves'.venv .safe) := {
        decl := decl
        envTypes := envTypes
        envCtors := envCtors
        source := by simpa using hcore
        extension := hadd
      }
      exact ⟨by simpa [hs, hlparams, hsource] using hspec⟩
  | «partial» =>
      exact (hnotPartial hs).elim

/-- Complete ordinary refinement retaining the independent source judgment,
without any equality-bootstrap premise. -/
theorem AddInductive.run.semanticFinalSpecificationModelWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WFCore c.env) (hcorner : ∀ safety, CtorTelescopes safety c.env (ves.venv safety))
    (hsource : Hc.venv = ves.venv c.safety)
    (Hclosed : MutualInductivesClosed c.env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : types ≠ [])
    (HnotPartial : c.safety ≠ .partial)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.allowPrimitive = c.allowPrimitive →
      c'.fuel = c.fuel →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth numNested
        types.toArray (c.safety != .safe) Hc') :
    (AddInductive.run nparams types numNested c).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WFCore outEnv ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        VEnvs.CertPres c.env outEnv ves ves' ∧
        Nonempty (OrdinaryInductiveSpecificationResult Hc.venv c.lparams
          nparams types (c.safety != .safe)
          (ves'.venv (if c.safety != .safe then .unsafe else .safe))) := by
  have hsize : 0 < types.toArray.size := by
    cases htypes : types with
    | nil => simp [htypes] at hnonempty
    | cons _ _ => simp [htypes]
  exact (AddInductive.run.semanticSourceAlignedWF nparams numNested Hc
    Hclosed wf.envGF hctx hsize HnotPartial Hinputs).mono fun _ Hrun => by
      exact Hrun.extendWithSpecification wf hcorner hsource HnotPartial hnonempty

end VerifyInductive
end Lean4Lean
