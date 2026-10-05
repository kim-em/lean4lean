import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFundamental
import Lean4Lean.Theory.Typing.AnchoredNativeSyntaxTransport

/-! Future native tuples use the literal mapped capture lists. Their
substitutions agree with weakened substitutions on the finite telescope;
the unused identity tails need not agree. Actual source certificates are
transported by that finite agreement. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Fits.realizePrefix
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat}
    {σ τ σ' τ' : Subst} {available : Valuation}
    (scope : CtxClosed source)
    (fits : Fits env U registry source target locals σ τ available)
    (left : ∀ i < source.length, σ i = σ' i)
    (right : ∀ i < source.length, τ i = τ' i) :
    Fits env U registry source target locals σ' τ' available := by
  constructor
  intro index need member sourceType lookup
  obtain ⟨entry⟩ := fits.entry index need member sourceType lookup
  have formed := scope.lookup lookup
  refine ⟨⟨entry.support, entry.footprint, entry.certificate.realizePrefix formed σ' left,
    entry.available, entry.typed, ?_⟩⟩
  simpa only [left index lookup.lt, right index lookup.lt,
    subst_congr_closedN formed left] using entry.related

theorem PairedFits.realizePrefix
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat}
    {σ τ σ' τ' : Subst} {available : Valuation}
    (scope : CtxClosed source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (left : ∀ i < source.length, σ i = σ' i)
    (right : ∀ i < source.length, τ i = τ' i) :
    PairedFits env U registry source target locals σ' τ' available :=
  ⟨fits.forward.realizePrefix scope left right, fits.backward.realizePrefix scope right left⟩

theorem PairedFits.nativeFuture
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {source target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    {locals : List Nat} {left right : List VExpr} {available : Valuation}
    (hSource : OnCtx source (env.IsType U))
    (leftLength : left.length = source.length) (rightLength : right.length = source.length)
    (fits : PairedFits env U registry source target locals
      (nativeCaptureSubst left) (nativeCaptureSubst right) available) :
    PairedFits env U registry source future locals
      (nativeCaptureSubst (left.map (·.lift' ρ)))
      (nativeCaptureSubst (right.map (·.lift' ρ))) (Valuation.rename ρ available) := by
  exact (fits.future henv insertion).realizePrefix (CtxWF.closed henv hSource)
    (fun i hi => nativeCaptureSubst_rename_prefix left ρ (leftLength ▸ hi))
    (fun i hi => nativeCaptureSubst_rename_prefix right ρ (rightLength ▸ hi))

end Lean4Lean.AnchoredSource.Adapted

namespace Lean4Lean.VEnv.Ctx.SubstEq
open VExpr AnchoredSource.Adapted
set_option backward.isDefEq.respectTransparency false

theorem nativeFuture
    {env : VEnv} {U : Nat} (henv : env.Ordered)
    {source target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    {left right : List VExpr}
    (leftLength : left.length = source.length) (rightLength : right.length = source.length)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst left) (nativeCaptureSubst right) source) :
    Ctx.SubstEq env U future (nativeCaptureSubst (left.map (·.lift' ρ)))
      (nativeCaptureSubst (right.map (·.lift' ρ))) source := by
  exact native_substEq_prefix henv (raw.weakenTarget henv insertion.weakening)
    (fun i hi => nativeCaptureSubst_rename_prefix left ρ (leftLength ▸ hi))
    (fun i hi => nativeCaptureSubst_rename_prefix right ρ (rightLength ▸ hi))

end Lean4Lean.VEnv.Ctx.SubstEq
