import Lean4Lean.Verify.Inductive.Nested.FreshTraceLemmas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Turn an abstract inductive installation obtained from exact nested
restoration into the concrete implementation-refinement boundary. Source
lookup preservation, final production/abstract alignment, and delta
conservativity are consequences of the restoration trace; declaration origin
metadata is the only boundary-specific input. -/
theorem RestoredNestedDeclarationsResult.addInductConcrete
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (Habstract : VEnv.AddInduct sourceVEnv decl targetVEnv)
    (Hchecking : CheckingEnv safety out.2 targetVEnv)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Horigins : ProductionInductiveOrigins sourceProdEnv.constants
      out.2.constants decl) :
    AddInduct safety sourceProdEnv.constants sourceVEnv decl
      out.2.constants targetVEnv := by
  rcases H.freshTraceNondelta hsourceWF with
    ⟨entries, Hfresh, hnondelta⟩
  cases Habstract with
  | intro Hdecl Hcompile Hblock Hinstall =>
      apply AddInduct.intro _ Hdecl Hcompile Hblock Hinstall Horigins
      · intro name ci hfind
        exact Hfresh.preservesSourceMapFind hsourceWF hfind
      · intro _HsourceAligned
        exact Hchecking.aligned
      · exact Hfresh.deltaConservative hsourceWF hnondelta

end VerifyInductive
end Lean4Lean
