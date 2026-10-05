import Lean4Lean.Theory.Typing.AnchoredProjectionFieldReification
import Lean4Lean.Theory.Typing.AnchoredNativeForwardLevels

/-! A retained declaration template may use the frozen observation's universe
packet. Restore the original projection rule's actual packet without changing
its finite source requirements or appealing to a new semantic induction. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem CodeCert.instLevelsScoped
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {source target : List VExpr}
    (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ : Subst} {template : VExpr}
    (scope : template.ClosedN source.length)
    (values : Ctx.SubstEq env U target σ σ source)
    {seed actual : List VLevel}
    (seedWF : ∀ level ∈ seed, level.WF U)
    (actualWF : ∀ level ∈ actual, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seed actual)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ (template.instL seed) support footprint)
    (formed : env.IsType U target ((template.instL seed).subst σ)) :
    Nonempty (CodeCert env U registry target locals σ (template.instL actual) support footprint) := by
  have equal := EqUpToLevels.instL_expr template seedWF actualWF equivalent
  exact certificate.levels henv hTarget equal
    (equal.substScoped scope.instL (values.nativeValueLevels henv hTarget))
    ⟨_, formed.choose_spec⟩

end Lean4Lean.AnchoredSource.Adapted
