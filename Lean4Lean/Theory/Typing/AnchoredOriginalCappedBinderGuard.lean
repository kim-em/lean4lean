import Lean4Lean.Theory.Typing.AnchoredOriginalCappedBinderPeel

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- One actual binder guard is sufficient. Its certificate remains available
in the full merged suffix, while the cap identifies its exact admitted input. -/
structure CappedBinderGuard
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (σ τ : Subst) (available : Valuation) where
  rank : Nat
  input : Profile rank
  support : Profile rank
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target (.ref domain) (graph.locals base.locals)
    σ.tail true support footprint
  resources : footprint.Available (fun index => available (index + 1))
  typed : input.HasType support
  related : Related env U registry target σ.head τ.head (A.subst σ.tail) input support
  cap : commonCaps 0 = Need.Fits input

private def binderGuardInvariant
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available) : Prop :=
  match graph with
  | .bind previous domain _ _ => Nonempty (CappedBinderGuard base commonCaps previous domain σ τ available)
  | _ => True

private theorem binderGuardInvariant_merge
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    (first : binderGuardInvariant base commonCaps graph left) :
    binderGuardInvariant base commonCaps graph (.merge left right) := by
  cases graph <;> try trivial
  obtain ⟨guard⟩ := first
  exact ⟨{ guard with resources := fun index need member => List.mem_append_left _ (guard.resources index need member) }⟩

private theorem CappedCaptureGenerated.binderGuardInvariant
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame) :
    binderGuardInvariant base commonCaps graph frame := by
  induction generated with
  | merge _ _ first _ => exact binderGuardInvariant_merge first
  | identity => trivial
  | empty => trivial
  | tail => trivial
  | bind generated domain annotation displayed certificate resources typed arguments needs bounded covered _ =>
    exact ⟨⟨_, _, _, _, generated.generated.locals_eq ▸ certificate, resources, typed, arguments, rfl⟩⟩
  | reserveCapture => trivial
  | reserveBind _ _ ih => exact ih
  | capture => trivial
  | group => trivial
  | scopedGroup => trivial
  | historyGroup => trivial
  | weaken => trivial

theorem CappedCaptureGenerated.binderGuard
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {displayed : A.subst raw = annotation}
    {frame : RawOriginalRichFrame sourceEnv env U registry target (.cons context domain)
      locals σ τ available}
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight
      (.bind graph domain annotation displayed) frame) :
    Nonempty (CappedBinderGuard base commonCaps graph domain σ τ available) :=
  generated.binderGuardInvariant

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
