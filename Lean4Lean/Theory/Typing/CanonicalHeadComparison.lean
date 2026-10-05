import Lean4Lean.Theory.Typing.CanonicalDataHeadCompatibility
import Lean4Lean.Theory.Typing.CanonicalTraceAmalgamation

/-!
Produce a common Pi display from independently witnessed canonical traces.

The initial proof frames may differ. Syntax-directed trace comparison first
identifies the generated telescopes after the initial forward embeddings.
Typed telescope amalgamation then identifies the corresponding fresh slots,
producing literal domain and codomain agreement in one actual common context.
No Pi inversion, type uniqueness, or semantic retraction is used.

This covers the head-machine fragment defined in `CanonicalHeadTrace`. It
does not assert that every well-typed expression has a trace, or supply the
native guards needed to justify a trace as an object-language equality.
-/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData
open SharedProofInterleaving

/-- The common context is constructed from the two initial histories and
actual typing of the complete trace telescopes. The final Pi components
agree literally under its forward embeddings, including under the Pi binder.

The shared initial telescope may contain data binders. Private proof variables
from the two initial histories remain distinct, while matching trace slots
are identified. The returned common target retains literal proof-insertion
histories from both final displays, so later dependent worlds can be pushed
forward without replacing those histories by arbitrary split embeddings. -/
theorem canonicalPiDisplay_common
    {registry : CanonicalHead.Registry} (hscoped : registry.Scoped)
    {env : VEnv} {U : Nat} (henv : env.Ordered)
    {base shared leftTarget rightTarget : List VExpr} {leftMap rightMap : Lift}
    (I : SharedProofInterleaving env U base shared leftTarget leftMap)
    (J : SharedProofInterleaving env U base shared rightTarget rightMap)
    {expression leftDomain leftBody rightDomain rightBody : VExpr}
    {leftAdded rightAdded : List VExpr}
    (hleft : CanonicalDataHead.Trace registry (expression.lift' leftMap) leftAdded
      (.forallE leftDomain leftBody))
    (hright : CanonicalDataHead.Trace registry (expression.lift' rightMap) rightAdded
      (.forallE rightDomain rightBody))
    (hL : OnCtx (leftAdded ++ leftTarget) (env.IsType U))
    (hR : OnCtx (rightAdded ++ rightTarget) (env.IsType U)) :
    ∃ D : CommonTarget env U (leftAdded ++ leftTarget) (rightAdded ++ rightTarget)
        (leftMap.consN leftAdded.length) (rightMap.consN rightAdded.length),
      leftDomain.lift' D.left.liftMap = rightDomain.lift' D.right.liftMap ∧
      leftBody.lift' D.left.liftMap.cons = rightBody.lift' D.right.liftMap.cons := by
  let C := I.commonTarget J henv
  have hsource : (expression.lift' leftMap).lift' C.left.liftMap =
      (expression.lift' rightMap).lift' C.right.liftMap := by
    rw [← lift'_comp, ← lift'_comp, C.agreement]
  have hleft' := hleft.rename hscoped C.left.liftMap
  have hright' := hright.rename hscoped C.right.liftMap
  rw [← hsource] at hright'
  obtain ⟨hadded, hdomain, hbody⟩ := hleft'.pi_unique hright'
  obtain ⟨D, hdL, hdR⟩ := C.synchronizeTelescope henv leftAdded rightAdded hL hR hadded
  exact ⟨D, by rwa [hdL, hdR], by rwa [hdL, hdR]⟩

/-- Successful canonical Pi and sort exposures of one source cannot disagree
about the head constructor, even when their initial proof frames differ. -/
theorem canonicalPiDisplay_ne_sort
    {registry : CanonicalHead.Registry} (hscoped : registry.Scoped)
    {env : VEnv} {U : Nat} (henv : env.Ordered)
    {base shared leftTarget rightTarget : List VExpr} {leftMap rightMap : Lift}
    (I : SharedProofInterleaving env U base shared leftTarget leftMap)
    (J : SharedProofInterleaving env U base shared rightTarget rightMap)
    {expression domain body : VExpr} {level : VLevel}
    {leftAdded rightAdded : List VExpr}
    (hleft : CanonicalDataHead.Trace registry (expression.lift' leftMap) leftAdded
      (.forallE domain body))
    (hright : CanonicalDataHead.Trace registry (expression.lift' rightMap) rightAdded
      (.sort level)) : False := by
  let C := I.commonTarget J henv
  have hsource : (expression.lift' leftMap).lift' C.left.liftMap =
      (expression.lift' rightMap).lift' C.right.liftMap := by
    rw [← lift'_comp, ← lift'_comp, C.agreement]
  have hleft' := hleft.rename hscoped C.left.liftMap
  have hright' := hright.rename hscoped C.right.liftMap
  rw [← hsource] at hright'
  have h := (hleft'.terminal_unique hright'
    (CanonicalDataHead.step_pi ..) (CanonicalDataHead.step_sort ..)).2
  cases h

end Lean4Lean.VEnv
