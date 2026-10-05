import Lean4Lean.Theory.Typing.AnchoredRhsApplicationPath
import Lean4Lean.Theory.Typing.CanonicalHeadApplication

/-! The actual canonical trace of a finite RHS application path. This keeps
the generated proof front explicit. It does not identify its private proof
variables with the independently transported semantic path. -/
namespace Lean4Lean.AnchoredSemantics.RhsApplicationPath
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

def front : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom →
    List VExpr → List VExpr
  | .done, added => added
  | .app (ρ := ρ) display _ _ _ _ _ tail, added =>
    tail.front (renameAdded (display.map.comp ρ) added)
  | .unpad tail, added => tail.front added

theorem front_length
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (added : List VExpr) : (path.front added).length = added.length := by
  induction path generalizing added with
  | done => rfl
  | app _ _ _ _ _ _ _ ih => simp only [front, ih, renameAdded_length]
  | unpad _ ih => exact ih added

/-- The exact front of the actual application trace is inhabited in the
original path's final world, independently of the semantic replay diagram. -/
theorem frontInsertion
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (frame : ProofInsertion env U Γ (added ++ Γ) (.skipN .refl added.length)) :
    ProofInsertion env U Ω (path.front added ++ Ω) (.skipN .refl added.length) := by
  induction path generalizing added with
  | done => exact frame
  | @app n Γ type A B domain rows key support output Δ ρ x y m Ω finalType finalAtom
      display literal row typed future admitted tail ih =>
    have displayFrame := display.leftExposure.generated.comp display.leftExposure.post henv
    rw [display.leftExposure.map_eq] at displayFrame
    have displayFrame' : ProofInsertion env U Γ display.context display.map := by
      simpa only [literal] using displayFrame
    have forward := displayFrame'.toFuture.comp future henv
    have next := frame.renameFront added forward henv |>.1
    simpa only [front, renameAdded_length] using
      ih (added := renameAdded (display.map.comp ρ) added)
        (by simpa only [renameAdded_length] using next)
  | unpad tail ih => exact ih frame

def rightAfterFront : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom →
    Nat → VExpr → VExpr
  | .done, _, expression => expression
  | .app (ρ := ρ) (y := y) display _ _ _ _ _ tail, count, expression =>
    tail.rightAfterFront count
      (.app (expression.lift' ((display.map.comp ρ).consN count)) (y.liftN count))
  | .unpad tail, count, expression => tail.rightAfterFront count expression

def leftAfterFront : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom →
    Nat → VExpr → VExpr
  | .done, _, expression => expression
  | .app (ρ := ρ) (x := x) display _ _ _ _ _ tail, count, expression =>
    tail.leftAfterFront count
      (.app (expression.lift' ((display.map.comp ρ).consN count)) (x.liftN count))
  | .unpad tail, count, expression => tail.leftAfterFront count expression

theorem traceRight
    {registry : CanonicalHead.Registry}
    (hscoped : registry.Scoped)
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (trace : CanonicalDataHead.Trace registry expression added result) :
    CanonicalDataHead.Trace registry (path.rightAction expression) (path.front added)
      (path.rightAfterFront added.length result) := by
  induction path generalizing expression added result with
  | done => exact trace
  | @app n Γ type A B domain rows key support output Δ ρ x y m Ω finalType finalAtom
      display literal row typed future admitted tail ih =>
    have application := (trace.rename hscoped (display.map.comp ρ)).app y
    simpa only [renameAdded_length, rightAction, front, rightAfterFront] using ih application
  | unpad tail ih => exact ih trace

theorem traceLeft
    {registry : CanonicalHead.Registry}
    (hscoped : registry.Scoped)
    (path : RhsApplicationPath env U registry n Γ type atom m Ω finalType finalAtom)
    (trace : CanonicalDataHead.Trace registry expression added result) :
    CanonicalDataHead.Trace registry (path.leftAction expression) (path.front added)
      (path.leftAfterFront added.length result) := by
  induction path generalizing expression added result with
  | done => exact trace
  | @app n Γ type A B domain rows key support output Δ ρ x y m Ω finalType finalAtom
      display literal row typed future admitted tail ih =>
    have application := (trace.rename hscoped (display.map.comp ρ)).app x
    simpa only [renameAdded_length, leftAction, front, leftAfterFront] using ih application
  | unpad tail ih => exact ih trace

end Lean4Lean.AnchoredSemantics.RhsApplicationPath
