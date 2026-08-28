import Lean4Lean.Verify.Inductive.Run.SemanticRun

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Close the completed skeleton-free post-analysis phases against the
independent ordinary-inductive specification.  The generated equation batch
is recovered canonically from the retained recursor phase. -/
theorem SemanticRunWithStatsResult.addInductCanonical
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (hnonempty : indTypes.toList ≠ [])
    (hproj : ProjectionConstPreservation) :
    ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
      VEnv.AddInduct sourceEnv decl finalVEnv := by
  rcases Hrun with
    ⟨decl, headerEnv, ctorEnv, Hheaders, R, ⟨Hrecursors⟩⟩
  rcases Hrecursors.canonicalOrdinaryRuleTranslation hproj with ⟨T⟩
  exact ⟨decl, Hrecursors.outVEnv.addDefEqRules T.rules,
    Hrecursors.addInductOfOrdinaryCompilation T.rules T.rulesWF hnonempty
      T.compilation⟩

/-- The complete executable ordinary checker refines `VEnv.AddInduct`
without a caller-supplied declaration skeleton, constructor targets, or
equation rules.  Source-context alignment is retained for composition with
nested lowering/restoration and the final environment boundary. -/
theorem VerifiedSemanticInductiveRunResult.addInductCanonical
    (Hrun : VerifiedSemanticInductiveRunResult source nparams types
      numNested outEnv)
    (hnonempty : types ≠ [])
    (hproj : ProjectionConstPreservation) :
    ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
      c'.env = source.env ∧
      c'.safety = source.safety ∧
      c'.lparams = source.lparams ∧
      ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
        VEnv.AddInduct Hc'.venv decl finalVEnv := by
  rcases Hrun with
    ⟨c', stats, depth, commonParams, commonLevel, Hc', henv, hsafety,
      hlparams, Hsemantic, Hphases⟩
  have hnonempty' : types.toArray.toList ≠ [] := by
    simpa using hnonempty
  rcases Hphases.addInductCanonical hnonempty' hproj with
    ⟨decl, finalVEnv, Hadd⟩
  exact ⟨c', Hc', henv, hsafety, hlparams, decl, finalVEnv, Hadd⟩

/-- End-to-end skeleton-free refinement theorem for an ordinary executable
`AddInductive.run`. -/
theorem AddInductive.run.semanticAddInductWF
    (nparams numNested : Nat)
    (Hc : ContextWF c)
    (Hclosed : MutualInductivesClosed c.env)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < types.toArray.size)
    (HnotPartial : c.safety ≠ .partial)
    (hproj : ProjectionConstPreservation)
    (Hinputs : ∀ {c' : AddInductive.Context}
      {stats : AddInductive.InductiveStats} {depth : Nat}
      {commonParams : List VExpr} {commonLevel : VLevel},
      (Hc' : ContextWF c') →
      (Hsemantic :
        checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
          Hc'.venv c'.lparams nparams commonParams commonLevel
            types.toArray.toList) →
      SemanticRunVerificationInputs c' stats nparams depth numNested
        types.toArray (c.safety != .safe) Hc') :
    (AddInductive.run nparams types numNested c).WF fun _ =>
      ∃ c' : AddInductive.Context, ∃ Hc' : ContextWF c',
        c'.env = c.env ∧
        c'.safety = c.safety ∧
        c'.lparams = c.lparams ∧
        ∃ decl : VInductDecl, ∃ finalVEnv : VEnv,
          VEnv.AddInduct Hc'.venv decl finalVEnv := by
  have htypes : types ≠ [] := by
    simpa using List.ne_nil_of_length_pos
      (by simpa using hnonempty : 0 < types.length)
  exact (AddInductive.run.semanticWF nparams numNested Hc Hclosed hctx
    hnonempty HnotPartial hproj Hinputs).mono fun _ Hrun =>
      Hrun.addInductCanonical htypes hproj

end VerifyInductive
end Lean4Lean
