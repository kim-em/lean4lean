import Lean4Lean.Theory.Typing.AnchoredBoundedVariable
import Lean4Lean.Theory.Typing.AnchoredNativeFitsFuture
import Lean4Lean.Theory.Typing.AnchoredNativeTypeCertificate
import Lean4Lean.Theory.Typing.AnchoredNativeDepthFuture
import Lean4Lean.Theory.Typing.AnchoredNativeDepthRenaming

/-! Native argument futures preserve the actual certificate bound. Closed
header certificates are likewise reused without spending current-head fuel. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat} {env : VEnv} {U : Nat}
  {registry : CanonicalHead.Registry} {source target extended : List VExpr}
  {locals : List Nat} {σ τ σ' τ' : Subst} {available : Valuation} {ρ : Lift}

theorem Fits.future (henv : env.Ordered)
    (insertion : FutureInsertion env U target extended ρ)
    (fits : Fits current fuel env U registry source target locals σ τ available) :
    Fits current fuel env U registry source extended locals (σ.lift_r ρ) (τ.lift_r ρ)
      (Valuation.rename ρ available) := by
  constructor
  intro index need member sourceType lookup
  obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
  obtain ⟨entry, bounded⟩ := fits.entry index original selected sourceType lookup
  refine ⟨⟨entry.support.rename ρ, Footprint.rename ρ entry.footprint,
    entry.certificate.future henv insertion, entry.available.rename ρ,
    Profile.rename_hasType_iff.mpr entry.typed, ?_⟩, ?_⟩
  · simpa only [Need.rename, Subst.lift_r, lift'_subst] using
      entry.related.future henv insertion
  · simpa only [CodeCert.nativeDepth_future] using bounded

theorem Fits.realizePrefix (scope : CtxClosed source)
    (fits : Fits current fuel env U registry source target locals σ τ available)
    (left : ∀ i < source.length, σ i = σ' i)
    (right : ∀ i < source.length, τ i = τ' i) :
    Fits current fuel env U registry source target locals σ' τ' available := by
  constructor
  intro index need member sourceType lookup
  obtain ⟨entry, bounded⟩ := fits.entry index need member sourceType lookup
  have formed := scope.lookup lookup
  refine ⟨⟨entry.support, entry.footprint, entry.certificate.realizePrefix formed σ' left,
    entry.available, entry.typed, ?_⟩, ?_⟩
  · simpa only [left index lookup.lt, right index lookup.lt,
      subst_congr_closedN formed left] using entry.related
  · simpa only [CodeCert.nativeDepth_realizePrefix] using bounded

theorem PairedFits.future (henv : env.Ordered)
    (insertion : FutureInsertion env U target extended ρ)
    (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    PairedFits current fuel env U registry source extended locals (σ.lift_r ρ) (τ.lift_r ρ)
      (Valuation.rename ρ available) :=
  ⟨fits.forward.future henv insertion, fits.backward.future henv insertion⟩

theorem PairedFits.realizePrefix (scope : CtxClosed source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (left : ∀ i < source.length, σ i = σ' i)
    (right : ∀ i < source.length, τ i = τ' i) :
    PairedFits current fuel env U registry source target locals σ' τ' available :=
  ⟨fits.forward.realizePrefix scope left right, fits.backward.realizePrefix scope right left⟩

theorem PairedFits.nativeFuture (henv : env.Ordered)
    (insertion : FutureInsertion env U target extended ρ)
    {left right : List VExpr} (hSource : OnCtx source (env.IsType U))
    (leftLength : left.length = source.length) (rightLength : right.length = source.length)
    (fits : PairedFits current fuel env U registry source target locals
      (nativeCaptureSubst left) (nativeCaptureSubst right) available) :
    PairedFits current fuel env U registry source extended locals
      (nativeCaptureSubst (left.map (·.lift' ρ)))
      (nativeCaptureSubst (right.map (·.lift' ρ))) (Valuation.rename ρ available) := by
  exact (fits.future henv insertion).realizePrefix (CtxWF.closed henv hSource)
    (fun i hi => nativeCaptureSubst_rename_prefix left ρ (leftLength ▸ hi))
    (fun i hi => nativeCaptureSubst_rename_prefix right ρ (rightLength ▸ hi))

end Lean4Lean.AnchoredSource.Adapted.Staged

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem codeDepth_expression_mp
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {p : Profile n}
    {f g : Footprint} {e e' : VExpr} (current : Name → Bool)
    (expression : e = e') (footprint : f = g)
    (equal : CodeCert env U registry target locals σ e p f =
      CodeCert env U registry target locals σ e' p g)
    (certificate : CodeCert env U registry target locals σ e p f) :
    (equal.mp certificate).nativeDepth current = certificate.nativeDepth current := by
  cases expression; cases footprint; cases equal; rfl

@[simp] theorem CodeCert.nativeDepth_closedSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {oldLocals : List Nat} {oldRealization : Subst}
    {expression : VExpr} {support : Profile n}
    (current : Name → Bool)
    (certificate : CodeCert env U registry target oldLocals oldRealization expression support [])
    (closed : expression.Closed) (locals : List Nat) (realization : Subst) :
    (certificate.closedSource closed locals realization).nativeDepth current =
      certificate.nativeDepth current := by
  simp only [CodeCert.closedSource, codeDepth_expression_mp, lift'_refl, Footprint.sourceLift, List.map_nil, CodeCert.nativeDepth_mp, CodeCert.nativeDepth_mpr,
    CodeCert.nativeDepth_renameSource, CodeCert.nativeDepth_realizePrefix]

theorem CodeCert.closedTypeCodeBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {realization : Subst} {expression : VExpr} {support : Profile n}
    (closed : expression.Closed)
    (original : Staged.Joint current fuel env U registry []
      expression expression (.sort level))
    (certificate : CodeCert env U registry target locals realization expression support [])
    (bounded : certificate.nativeDepth current ≤ fuel) :
    TypeRelated env U registry target expression expression support := by
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ h; cases h
  have fits : Staged.PairedFits current fuel env U registry [] target locals
      realization realization (fun _ => []) := by
    constructor <;> constructor <;> intro _ _ _ _ lookup <;> cases lookup
  have transfer : Staged.Transfer current fuel env U registry target locals realization realization
      (fun _ => []) expression expression (.sort level) :=
    (original target locals realization realization (fun _ => []) emptyClosed hTarget .nil fits).1
  have code := transfer.code henv hscoped hTarget certificate bounded (by intro _ _ h; cases h)
  have realized : expression.subst realization = expression := closed.subst_eq (by intro i hi; omega)
  simpa only [realized] using code

end Lean4Lean.AnchoredSource.Adapted
