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
    (wf : ves.WF source.env)
    (hsource : sourceEnv = ves.venv source.safety)
    (hnotPartial : source.safety ≠ .partial)
    (hnonempty : types ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      Nonempty (InductiveSpecificationResult sourceEnv source.lparams nparams types
        (source.safety != .safe)
        (ves'.venv (if source.safety != .safe then .unsafe else .safe))) := by
  rcases Hrun with
    ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
      hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hphases⟩
  have wf' : ves.WF c'.env := by
    rw [henv]
    exact wf
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
      rcases SemanticRunWithStatsResult.extendUnsafeExact Hphases wf'
          hcSafety hcVEnv hproduction hnonempty' with
        ⟨ves', decl, envTypes, envCtors, wf'', hle, hcore, hadd⟩
      refine ⟨ves', wf'', hle, ?_⟩
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
      rcases SemanticRunWithStatsResult.extendSafeExact Hphases wf'
          hcSafety hcVEnv hnonempty' with
        ⟨ves', decl, envTypes, envCtors, wf'', hle, hcore, hadd⟩
      refine ⟨ves', wf'', hle, ?_⟩
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

/-- Environment-preservation projection of `extendWithSpecification`. -/
theorem VerifiedSemanticInductiveRunResultSourceAligned.extend
    {ves : VEnvs}
    (Hrun : VerifiedSemanticInductiveRunResultSourceAligned source sourceEnv
      nparams types numNested outEnv)
    (wf : ves.WF source.env)
    (hsource : sourceEnv = ves.venv source.safety)
    (hnotPartial : source.safety ≠ .partial)
    (hnonempty : types ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rcases Hrun.extendWithSpecification wf hsource hnotPartial hnonempty with
    ⟨ves', wf', hle, _spec⟩
  exact ⟨ves', wf', hle⟩

/-- Canonical equality is preserved by the generic source-aligned extension
when it is present in the source model. -/
theorem VerifiedSemanticInductiveRunResultSourceAligned.extendOfQuotReady
    (Hrun : VerifiedSemanticInductiveRunResultSourceAligned source sourceEnv
      nparams types numNested outEnv)
    (wf : ves.WF source.env)
    (hEq : CanonicalEqEnvs ves)
    (hsource : sourceEnv = ves.venv source.safety)
    (hnotPartial : source.safety ≠ .partial)
    (hnonempty : types ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rcases Hrun.extend wf hsource hnotPartial hnonempty with
    ⟨ves', wf', hle⟩
  exact ⟨ves', wf', hEq.mono hle, hle⟩

/-- Complete ordinary refinement at the final environment boundary without
an equality-bootstrap premise. -/
theorem AddInductive.run.semanticFinalModelWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
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
      ∃ ves' : VEnvs, ves'.WF outEnv ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  have hsize : 0 < types.toArray.size := by
    cases htypes : types with
    | nil => simp [htypes] at hnonempty
    | cons _ _ => simp [htypes]
  exact (AddInductive.run.semanticSourceAlignedWF nparams numNested Hc
    Hclosed hctx hsize HnotPartial Hinputs).mono fun _ Hrun =>
      Hrun.extend wf hsource HnotPartial hnonempty

/-- Complete ordinary refinement retaining the independent source judgment,
without any equality-bootstrap premise. -/
theorem AddInductive.run.semanticFinalSpecificationModelWF
    {ves : VEnvs}
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
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
      ∃ ves' : VEnvs, ves'.WF outEnv ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        Nonempty (OrdinaryInductiveSpecificationResult Hc.venv c.lparams
          nparams types (c.safety != .safe)
          (ves'.venv (if c.safety != .safe then .unsafe else .safe))) := by
  have hsize : 0 < types.toArray.size := by
    cases htypes : types with
    | nil => simp [htypes] at hnonempty
    | cons _ _ => simp [htypes]
  exact (AddInductive.run.semanticSourceAlignedWF nparams numNested Hc
    Hclosed hctx hsize HnotPartial Hinputs).mono fun _ Hrun => by
      exact Hrun.extendWithSpecification wf hsource HnotPartial hnonempty

/-- Complete ordinary `AddInductive.run` refinement at the final environment
boundary.  The executable run supplies the abstract declaration and every
installation certificate; the caller supplies only persistent environment
invariants and the explicitly isolated shared metatheory properties. -/
theorem AddInductive.run.semanticFinalWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
    (hEq : CanonicalEqEnvs ves)
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
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  have hsize : 0 < types.toArray.size := by
    cases htypes : types with
    | nil => simp [htypes] at hnonempty
    | cons _ _ => simp [htypes]
  exact (AddInductive.run.semanticSourceAlignedWF nparams numNested Hc
    Hclosed hctx hsize HnotPartial Hinputs).mono fun _ Hrun =>
      Hrun.extendOfQuotReady wf hEq hsource HnotPartial hnonempty

/-- Complete ordinary refinement without projecting away the independent
source judgment.  The final safety-indexed model, the exact source
translation, and `AddInduct` are all derived from the same successful
executable run. -/
theorem AddInductive.run.semanticFinalSpecificationWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (wf : ves.WF c.env)
    (hEq : CanonicalEqEnvs ves)
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
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        Nonempty (OrdinaryInductiveSpecificationResult Hc.venv c.lparams
          nparams types (c.safety != .safe)
          (ves'.venv (if c.safety != .safe then .unsafe else .safe))) := by
  have hsize : 0 < types.toArray.size := by
    cases htypes : types with
    | nil => simp [htypes] at hnonempty
    | cons _ _ => simp [htypes]
  exact (AddInductive.run.semanticSourceAlignedWF nparams numNested Hc
    Hclosed hctx hsize HnotPartial Hinputs).mono fun _ Hrun => by
      rcases Hrun.extendWithSpecification wf hsource HnotPartial hnonempty with
        ⟨ves', wf', hle, Hspec⟩
      exact ⟨ves', wf', hEq.mono hle, hle, Hspec⟩

end VerifyInductive
end Lean4Lean
