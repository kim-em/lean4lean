import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGraph

/-! Source-display provenance includes the environments of nominal capture
owners, independently of whether a captured slot currently has a query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false

def OriginalCaptureMap.Ambient
    (env : VEnv) {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw) : Prop :=
  sourceEnv ≤ env ∧ match graph with
  | .empty _ | .identity _ => True
  | .tail previous => previous.Ambient env
  | .capture previous _ ownerMap _ _ => previous.Ambient env ∧ ownerMap.Ambient env
  | .bind previous .. => previous.Ambient env
  | .weaken previous _ => previous.Ambient env

theorem OriginalCaptureMap.Ambient.below
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (ambient : graph.Ambient env) : sourceEnv ≤ env := by
  rw [OriginalCaptureMap.Ambient.eq_def] at ambient
  exact ambient.1

theorem OriginalCaptureMap.Ambient.identity
    (context : ContextDerivation sourceEnv U source) (below : sourceEnv ≤ env) :
    (OriginalCaptureMap.identity context).Ambient env := ⟨below, trivial⟩

theorem OriginalCaptureMap.Ambient.empty
    (below : sourceEnv ≤ env) (common : List VExpr) :
    (OriginalCaptureMap.empty (sourceEnv := sourceEnv) (U := U) common).Ambient env := ⟨below, trivial⟩

theorem OriginalCaptureMap.Ambient.capture
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (previous : graph.Ambient env)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerMap : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerAmbient : ownerMap.Ambient env)
    (owner : EndpointState ownerEnv U ownerSource expression assigned)
    (provenance : EndpointProvenance ownerContext owner) :
    (OriginalCaptureMap.capture graph domain ownerMap owner provenance).Ambient env :=
  ⟨previous.below, previous, ownerAmbient⟩

theorem OriginalCaptureMap.Ambient.weaken
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (ambient : graph.Ambient env)
    (insertion : Ctx.Lift' ρ common next) :
    (graph.weaken insertion).Ambient env := ⟨ambient.below, ambient⟩

theorem OriginalCaptureMap.Ambient.tail
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {graph : OriginalCaptureMap (common := common) (.cons context domain) raw}
    (ambient : graph.Ambient env) : graph.tail.Ambient env := ⟨ambient.below, ambient⟩

theorem OriginalCaptureMap.Ambient.bind
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (ambient : graph.Ambient env)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (annotation : VExpr) (displayed : A.subst raw = annotation) :
    (graph.bind domain annotation displayed).Ambient env := ⟨ambient.below, ambient⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
