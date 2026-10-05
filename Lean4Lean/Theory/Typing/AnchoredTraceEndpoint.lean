import Lean4Lean.Theory.Typing.AnchoredTraceCode
import Lean4Lean.Theory.Typing.AnchoredTraceCodeLeft
import Lean4Lean.Theory.Typing.AnchoredMinimalSupport
import Lean4Lean.Theory.Typing.CanonicalHeadApplication

/-! The two concrete endpoint shapes required by native expansion: an actual
canonical trace through the chosen front, or an unchanged base term lifted
through it. Both shapes are preserved by dependent application and renaming.
-/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

inductive TraceEndpoint (registry : CanonicalHead.Registry) (front : List VExpr) :
    VExpr → VExpr → Prop where
  | traced (trace : CanonicalDataHead.Trace registry expression front result) :
      TraceEndpoint registry front expression result
  | lifted : TraceEndpoint registry front expression
      (expression.lift' (.skipN .refl front.length))

theorem TraceEndpoint.rename
    (hscoped : registry.Scoped) (ρ : Lift)
    (H : TraceEndpoint registry front expression result) :
    TraceEndpoint registry (renameAdded ρ front)
      (expression.lift' ρ) (result.lift' (ρ.consN front.length)) := by
  cases H with
  | traced trace => exact .traced (trace.rename hscoped ρ)
  | lifted =>
    have maps : (Lift.skipN .refl front.length).comp (ρ.consN front.length) =
        ρ.comp (.skipN .refl (renameAdded ρ front).length) := by
      simp only [renameAdded_length, Lift.skipN_comp_consN, Lift.refl_comp,
        Lift.comp_skipN, Lift.comp]
    simpa only [← lift'_comp, maps] using
      (TraceEndpoint.lifted (registry := registry) (front := renameAdded ρ front)
        (expression := expression.lift' ρ))

theorem TraceEndpoint.app
    (H : TraceEndpoint registry front expression result) (argument : VExpr) :
    TraceEndpoint registry front (.app expression argument)
      (.app result (argument.liftN front.length)) := by
  cases H with
  | traced trace => exact .traced (trace.app argument)
  | lifted =>
    simpa only [lift', show argument.lift' (.skipN .refl front.length) =
      argument.liftN front.length from lift'_consN_skipN (k := 0)] using
      (TraceEndpoint.lifted (registry := registry) (front := front)
        (expression := .app expression argument))

/-- Expand code capabilities for all four actual endpoint combinations. Raw
conversion paths are supplied by casting the actual typed trace equalities at
the universe furnished by the retained type capability. -/
theorem TypeRelated.prependEndpoints
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ front : List VExpr} {left right leftResult rightResult : VExpr}
    {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (wf : profile.WF)
    (leftTrace : TraceEndpoint registry front left leftResult)
    (rightTrace : TraceEndpoint registry front right rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftPath : TypeConversion env U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult)
    (rightPath : TypeConversion env U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult)
    (related : TypeRelated env U registry (front ++ Γ) leftResult rightResult
      (profile.rename (.skipN .refl front.length))) :
    TypeRelated env U registry Γ left right profile := by
  cases leftTrace with
  | traced leftTrace =>
    cases rightTrace with
    | traced rightTrace =>
      exact TypeRelated.prependTrace henv hscoped leftTrace rightTrace generated leftPath rightPath related
    | lifted =>
      exact TypeRelated.prependLeftTrace henv hscoped leftTrace generated leftPath related
  | lifted =>
    cases rightTrace with
    | traced rightTrace =>
      have reversed := related.symm henv (Profile.rename_wf_iff.mpr wf)
      exact (TypeRelated.prependLeftTrace henv hscoped rightTrace generated rightPath reversed).symm henv wf
    | lifted => exact related.absorb henv hscoped generated

end Lean4Lean.AnchoredSemantics
