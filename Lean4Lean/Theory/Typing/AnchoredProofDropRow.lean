import Lean4Lean.Theory.Typing.AnchoredFunctionDisplayReplay

/-! The function-row step of proof-slot contraction. The auxiliary square
contains only raw worlds, a typed retraction, and literal syntax equations.
It does not contain a semantic operation. Its production from a concrete
proof history is a separate obligation; this is not a closed DROP theorem. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

structure ProofDropRowSquare
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {n : Nat} {Γsmall Γlarge : List VExpr}
    {smallType largeType smallA smallB largeA largeB : VExpr}
    {smallDomain largeDomain : Profile n}
    {smallRows largeRows : List (Key n × Profile n)}
    (small : PiWitness env U registry (relations env U registry n)
      Γsmall smallType smallType smallA smallB smallDomain smallRows)
    (large : PiWitness env U registry (relations env U registry n)
      Γlarge largeType largeType largeA largeB largeDomain largeRows)
    (retract : Subst) (smallKey largeKey : Key n) (smallOutput largeOutput : Atom n)
    (smallResult largeResult : Profile n)
    (Δ : List VExpr) (ρ : Lift) where
  oldWorld : List VExpr
  oldMap : Lift
  oldFuture : FutureInsertion env U large.context oldWorld oldMap
  largerWorld : List VExpr
  contextChange : ContextChain env U oldWorld largerWorld
  frame : SplitTypedEmbedding env U Δ largerWorld
  insertion : ProofInsertion env U Δ largerWorld frame.liftMap
  keys : largeKey.rename (large.map.comp oldMap) =
    (smallKey.rename (small.map.comp ρ)).rename frame.liftMap
  output : largeOutput.rename (large.map.comp oldMap) =
    (smallOutput.rename (small.map.comp ρ)).rename frame.liftMap
  support : largeResult.rename (large.map.comp oldMap) =
    (smallResult.rename (small.map.comp ρ)).rename frame.liftMap
  operands : ∀ expression : VExpr,
    (expression.lift' (large.map.comp oldMap)).subst frame.retract =
      (expression.subst retract).lift' (small.map.comp ρ)
  body : (large.leftBody.lift' oldMap.cons).subst frame.retract.lift =
    small.leftBody.lift' ρ.cons

/-- Strict lower-rank contraction discharges the arbitrary-future-argument
case. Arguments are lifted by the section before querying the old behavior,
so the chosen retraction returns them literally, including new data binders. -/
theorem FunctionRowBehavior.dropWith
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered)
    (lowerDrop : ∀ {Γ Δ : List VExpr} (frame : SplitTypedEmbedding env U Γ Δ),
      ProofInsertion env U Γ Δ frame.liftMap →
      ∀ {left right type : VExpr} {value support : Profile n},
        Related env U registry Δ left right type
          (value.rename frame.liftMap) (support.rename frame.liftMap) →
        Related env U registry Γ (left.subst frame.retract) (right.subst frame.retract)
          (type.subst frame.retract) value support)
    {Γsmall Γlarge : List VExpr} {left right smallType largeType : VExpr}
    {smallA smallB largeA largeB : VExpr} {smallDomain largeDomain : Profile n}
    {smallRows largeRows : List (Key n × Profile n)}
    (small : PiWitness env U registry (relations env U registry n)
      Γsmall smallType smallType smallA smallB smallDomain smallRows)
    (large : PiWitness env U registry (relations env U registry n)
      Γlarge largeType largeType largeA largeB largeDomain largeRows)
    {retract : Subst} {smallKey largeKey : Key n}
    {smallOutput largeOutput : Atom n} {smallResult largeResult : Profile n}
    (squares : ∀ Δ ρ, FutureInsertion env U small.context Δ ρ →
      Nonempty (ProofDropRowSquare env U registry small large retract
        smallKey largeKey smallOutput largeOutput smallResult largeResult Δ ρ))
    (old : FunctionRowBehavior env U registry Γlarge left right largeType
      largeKey largeOutput largeResult large) :
    FunctionRowBehavior env U registry Γsmall
      (left.subst retract) (right.subst retract) smallType
      smallKey smallOutput smallResult small := by
  intro Δ ρ future x y admitted
  obtain ⟨square⟩ := squares Δ ρ future
  have lifted := admitted.future henv square.insertion.toFuture
  have oldAdmission : Admitted env U registry square.largerWorld
      (largeKey.rename (large.map.comp square.oldMap))
      (x.lift' square.frame.liftMap) (y.lift' square.frame.liftMap) := by
    rw [square.keys]
    exact lifted
  have originalAdmission := (square.contextChange.symm henv).admitted henv oldAdmission
  obtain ⟨first, second, cross⟩ := old square.oldWorld square.oldMap square.oldFuture
    (x.lift' square.frame.liftMap) (y.lift' square.frame.liftMap) originalAdmission
  have first := square.contextChange.term henv first
  have second := square.contextChange.term henv second
  have cross := square.contextChange.term henv cross
  rw [square.output, square.support, ← Profile.rename_singleton] at first second cross
  have first := lowerDrop square.frame square.insertion first
  have second := lowerDrop square.frame square.insertion second
  have cross := lowerDrop square.frame square.insertion cross
  have body (argument : VExpr) :
      (((large.leftBody.lift' square.oldMap.cons).inst
        (argument.lift' square.frame.liftMap)).subst square.frame.retract) =
      (small.leftBody.lift' ρ.cons).inst argument := by
    rw [subst_inst, square.body, square.frame.leftInv]
  have application (expression argument : VExpr) :
      (VExpr.app (expression.lift' (large.map.comp square.oldMap))
        (argument.lift' square.frame.liftMap)).subst square.frame.retract =
      .app ((expression.subst retract).lift' (small.map.comp ρ)) argument := by
    simp only [subst, square.operands, square.frame.leftInv]
  simpa only [body, application] using And.intro first (And.intro second cross)

end Lean4Lean.AnchoredSemantics
