import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGeneration

/-! Keep all frame indices with their actual positive generation when a
realization transports substitutions. Equality of these finite packages can
transport hereditary properties; heterogeneous equality of the generation
alone does not expose equality of its indexed raw frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false

abbrev WorldGenerationFramePack
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    (strata : EquationStratification env) (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target)
    (caps : CaptureCaps) {common : List VExpr} (left right : Subst)
    {sourceEnv : VEnv} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} {raw : Subst}
    (graph : OriginalCaptureMap (common := common) context raw)
    (controls : OriginalWorldControls strata sourceEnv) :=
  Σ' (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available),
    WorldGenerated strata P base caps left right graph frame controls

def WorldGenerated.framePack
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base caps left right graph frame controls) :
    WorldGenerationFramePack strata P base caps left right graph controls :=
  ⟨locals, σ, τ, available, frame, generated⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
