import Lean4Lean.Theory.Typing.CanonicalDataHeadApplication
import Lean4Lean.Theory.Typing.CanonicalDataHeadLevels
import Lean4Lean.Theory.Typing.CanonicalDataHeadTraceSubstitution
import Lean4Lean.Theory.Typing.TypedWorldMixed
import Lean4Lean.Theory.Typing.NativeCaptureTransport

/-! Raw typed code displays, shared by Pi/sort and data-family code clauses.
These declarations depend on no anchored profile or semantic relation. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv

/-- A literal typed trace and generated proof insertion, followed by a finite
terminal context conversion. Fresh proof slots retain actual inhabitants.
The terminal conversion changes declaration types, never variable positions. -/
structure Exposure (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (expression : VExpr) (Δ : List VExpr) (ρ : Lift)
    (head : VExpr) where
  added : List VExpr
  result : VExpr
  postMap : Lift
  trace : CanonicalDataHead.Trace registry expression added result
  generated : ProofInsertion env U Γ (added ++ Γ) (.skipN .refl added.length)
  postContext : List VExpr := Δ
  post : ProofInsertion env U (added ++ Γ) postContext postMap
  terminal : ContextChain env U postContext Δ := by exact .refl
  map_eq : (Lift.skipN .refl added.length).comp postMap = ρ
  result_eq : result.lift' postMap = head
  sound : TypeConversion env U Δ (expression.lift' ρ) head
  headType : env.IsType U Δ head

namespace Exposure

theorem insertion (henv : env.Ordered)
    (E : Exposure env U registry Γ expression Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := by
  have literal := E.generated.comp E.post henv
  rw [E.map_eq] at literal
  exact .comp (.proof literal) (.context E.terminal)

theorem targetWF (henv : env.Ordered)
    (E : Exposure env U registry Γ expression Δ ρ head) : OnCtx Δ (env.IsType U) :=
  E.terminal.targetWF henv (E.post.targetWF henv)

end Exposure


end Lean4Lean.AnchoredSemantics
