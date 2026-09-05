import Lean4Lean.Verify.Inductive.Run.SemanticAddInduct

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The independent ordinary-inductive judgment produced by a successful
checker run, including the translation of the exact source syntax.  Keeping
the source translation beside `AddInduct` prevents a final-environment model
from silently being attributed to a different (for example, lowered)
declaration. -/
structure InductiveSpecificationResult
    (sourceEnv : VEnv) (lparams : List Name) (nparams : Nat)
    (sourceTypes : List InductiveType) (isUnsafe : Bool)
    (finalVEnv : VEnv) where
  decl : VInductDecl
  envTypes : VEnv
  envCtors : VEnv
  source : TrInductDeclCore sourceEnv lparams nparams sourceTypes isUnsafe
    decl envTypes envCtors
  extension : VEnv.AddInduct sourceEnv decl finalVEnv

/-- Ordinary runs and primitive-bootstrap runs share the same independent
source judgment; this alias documents the ordinary use site. -/
abbrev OrdinaryInductiveSpecificationResult := InductiveSpecificationResult

/-- A completed ordinary semantic run refines the independent source
translation and environment-extension judgments simultaneously. -/
theorem SemanticRunWithStatsResult.independentSpecification
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (hnonempty : indTypes.toList ≠ []) :
    ∃ finalVEnv, Nonempty (OrdinaryInductiveSpecificationResult sourceEnv
      c.lparams nparams indTypes.toList isUnsafe finalVEnv) := by
  rcases Hrun with
    ⟨decl, headerEnv, ctorEnv, Hheaders, R, ⟨Hrecursors⟩⟩
  rcases Hrecursors.canonicalOrdinaryRuleTranslation with ⟨T⟩
  exact ⟨(Hrecursors.blockCertificate T.rules T.rulesWF).finalVEnv, ⟨{
    decl := decl
    envTypes := Hheaders.context.venv
    envCtors := R.declared.venvCtors
    source := R.core
    extension := Hrecursors.addInductOfOrdinaryCompilation T.rules
      T.rulesWF hnonempty T.compilation }⟩⟩

/-- Declaration-facing source alignment retains the exact original syntax in
the independent specification result. -/
theorem VerifiedSemanticInductiveRunResultSourceAligned.independentSpecification
    (Hrun : VerifiedSemanticInductiveRunResultSourceAligned source sourceEnv
      nparams types numNested outEnv)
    (hnonempty : types ≠ []) :
    ∃ finalVEnv, Nonempty (OrdinaryInductiveSpecificationResult sourceEnv
      source.lparams nparams types (source.safety != .safe) finalVEnv) := by
  rcases Hrun with
    ⟨c', stats, depth, commonParams, commonLevel, Hc', _henv, _hsafety,
      hlparams, _hallowPrimitive, _hfuel, hvenv, _Hsemantic, Hphases⟩
  have hnonempty' : types.toArray.toList ≠ [] := by
    simpa using hnonempty
  have Hspec := Hphases.independentSpecification hnonempty'
  simpa only [hlparams, hvenv] using Hspec

end VerifyInductive
end Lean4Lean
