import Lean4Lean.Theory.Typing.AnchoredConstructorIntroduction
import Lean4Lean.Theory.Typing.AnchoredDataAbsorption
import Lean4Lean.Theory.Typing.AnchoredTraceTermZero

/-! Constructor observations follow finite typed constructor provenance.
Eta and unit-like steps keep the original argument admissions, declaration
headers and exact family descriptor; no parameter demand is reconstructed. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

def RankedData.ConstructorWitness.prependOrigins
    (henv : env.Ordered)
    (leftOrigin : ConstructorOrigin env U registry Γ left' left type)
    (rightOrigin : ConstructorOrigin env U registry Γ right' right type)
    (witness : RankedData.ConstructorWitness env U registry lower Γ left right type demand) :
    RankedData.ConstructorWitness env U registry lower Γ left' right' type demand :=
  { witness with
    leftExposure := witness.leftExposure.prepend henv leftOrigin
    rightExposure := witness.rightExposure.prepend henv rightOrigin }

theorem RankedData.ConstructorRelation.prependOrigins
    (henv : env.Ordered)
    (leftOrigin : ConstructorOrigin env U registry Γ left' left type)
    (rightOrigin : ConstructorOrigin env U registry Γ right' right type)
    (related : RankedData.ConstructorRelation env U registry lower Γ left right type demand) :
    RankedData.ConstructorRelation env U registry lower Γ left' right' type demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := related Δ ρ future
  exact ⟨witness.prependOrigins henv (.weaken future.weakening leftOrigin)
    (.weaken future.weakening rightOrigin)⟩

theorem Related.constructorOrigins
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {left right left' right' type : VExpr} {demand : ConstructorData (Profile n)}
    {support : Profile (n + 1)}
    (leftOrigin : ConstructorOrigin env U registry Γ left' left type)
    (rightOrigin : ConstructorOrigin env U registry Γ right' right type)
    (related : Related env U registry Γ left right type
      (Profile.singleton (n := n + 1) (.ctor demand)) support) :
    Related env U registry Γ left' right' type
      (Profile.singleton (n := n + 1) (.ctor demand)) support := by
  apply Related.constructor henv hscoped (related.singleton_typed formed)
    (related.typeCode henv hscoped formed (by intro empty; cases empty))
  exact (related.constructorRelation henv hscoped formed).prependOrigins henv leftOrigin rightOrigin

/-- Both directions apply to an arbitrary frozen constructor demand and its
unchanged support. In particular, registered structure eta can expand or
contract a neutral endpoint without inventing a machine trace for it. -/
theorem Related.constructor_origin_iff
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} (formed : OnCtx Γ (env.IsType U))
    {left right left' right' type : VExpr} {demand : ConstructorData (Profile n)}
    {support : Profile (n + 1)}
    (leftOrigin : ConstructorOrigin env U registry Γ left' left type)
    (rightOrigin : ConstructorOrigin env U registry Γ right' right type) :
    Related env U registry Γ left right type
        (Profile.singleton (n := n + 1) (.ctor demand)) support ↔
      Related env U registry Γ left' right' type
        (Profile.singleton (n := n + 1) (.ctor demand)) support :=
  ⟨fun related => related.constructorOrigins henv hscoped formed leftOrigin rightOrigin,
    fun related => related.constructorOrigins henv hscoped formed leftOrigin.symm rightOrigin.symm⟩

end Lean4Lean.AnchoredSemantics
