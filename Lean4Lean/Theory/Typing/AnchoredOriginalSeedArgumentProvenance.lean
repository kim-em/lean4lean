import Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail

/-! Operative history seeds are retained actual application arguments. This
specific original child has a strict cost decrease; arbitrary non-root
locations do not provide that invariant. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false

inductive HeaderOwner.Argument
    {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType} : HeaderOwner field major → Prop where
  | inl
      {context : List VExpr}
      {domain : EndpointState sourceEnv U context A (.sort u)}
      {body : EndpointState sourceEnv U (A :: context) B (.sort v)}
      {function : EndpointState sourceEnv U context f (.forallE A B)}
      {argument : EndpointState sourceEnv U context a A}
      {result : EndpointState sourceEnv U context (B.inst a) (.sort v)}
      {hu : u.WF U} {hv : v.WF U}
      (location : Located field (.app hu hv domain body function argument result)) :
      Argument (.inl ⟨context, a, A, argument, .appArgument location⟩)
  | inr
      {context : List VExpr}
      {domain : EndpointState sourceEnv U context A (.sort u)}
      {body : EndpointState sourceEnv U (A :: context) B (.sort v)}
      {function : EndpointState sourceEnv U context f (.forallE A B)}
      {argument : EndpointState sourceEnv U context a A}
      {result : EndpointState sourceEnv U context (B.inst a) (.sort v)}
      {hu : u.WF U} {hv : v.WF U}
      (location : Located major (.app hu hv domain body function argument result)) :
      Argument (.inr ⟨context, a, A, argument, .appArgument location⟩)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
