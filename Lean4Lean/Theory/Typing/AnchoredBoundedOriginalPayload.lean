import Lean4Lean.Theory.Typing.AnchoredBoundedConversion
import Lean4Lean.Theory.Typing.AnchoredNativeFormationPayload

/-! The original Strong induction motive at a fixed declaration-stage fuel.
The literal endpoint Pi trees retain both original raw formation and the
same-fuel semantic result. Conversion does not replace these trees with
freshly synthesized typing derivations. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- The source environment is the actual original declaration stage; the
semantic environment is fixed at the final target. -/
def OriginalTypePayload (current : Name → Bool) (fuel : Nat)
    (sourceEnv finalEnv : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (expression type : VExpr) : Prop :=
  IsDefEqStrong sourceEnv U Γ expression expression type ∧
    Joint current fuel finalEnv U registry Γ expression expression type

structure OriginalPayload (current : Name → Bool) (fuel : Nat)
    (sourceEnv finalEnv : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {Γ : List VExpr} {left right type : VExpr}
    (_original : IsDefEqStrong sourceEnv U Γ left right type) : Prop where
  joint : Joint current fuel finalEnv U registry Γ left right type
  leftFormation : SourcePiFormation
    (OriginalTypePayload current fuel sourceEnv finalEnv U registry) Γ left
  rightFormation : SourcePiFormation
    (OriginalTypePayload current fuel sourceEnv finalEnv U registry) Γ right

namespace OriginalPayload
variable {current : Name → Bool} {fuel : Nat} {sourceEnv finalEnv : VEnv}
  {U : Nat} {registry : CanonicalHead.Registry}

theorem leftType (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    {H : IsDefEqStrong sourceEnv U Γ left right type}
    (payload : OriginalPayload current fuel sourceEnv finalEnv U registry H) :
    OriginalTypePayload current fuel sourceEnv finalEnv U registry Γ left type :=
  ⟨H.hasType.1, payload.joint.left henv hscoped⟩

theorem rightType (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    {H : IsDefEqStrong sourceEnv U Γ left right type}
    (payload : OriginalPayload current fuel sourceEnv finalEnv U registry H) :
    OriginalTypePayload current fuel sourceEnv finalEnv U registry Γ right type :=
  ⟨H.hasType.2, payload.joint.right henv hscoped⟩

theorem symm {H : IsDefEqStrong sourceEnv U Γ left right type}
    (payload : OriginalPayload current fuel sourceEnv finalEnv U registry H) :
    OriginalPayload current fuel sourceEnv finalEnv U registry H.symm :=
  ⟨payload.joint.symm, payload.rightFormation, payload.leftFormation⟩

/-- The middle observation may acquire a larger finite grade and a different
raw demand. Its explicit adapter and certificate are consumed at the same
fuel by the second original child; the outer Pi trees are retained literally. -/
theorem trans (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    {H₁ : IsDefEqStrong sourceEnv U Γ left middle type}
    {H₂ : IsDefEqStrong sourceEnv U Γ middle right type}
    (first : OriginalPayload current fuel sourceEnv finalEnv U registry H₁)
    (second : OriginalPayload current fuel sourceEnv finalEnv U registry H₂) :
    OriginalPayload current fuel sourceEnv finalEnv U registry (H₁.trans H₂) :=
  ⟨Joint.trans henv hscoped first.joint second.joint,
    first.leftFormation, second.rightFormation⟩

/-- Conversion interprets the ACTUAL returned certificate through the original
source-type equality child. The certificate remains bounded even when its
profile was raised or united by the term child. -/
theorem defeqDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped) (hu : u.WF U)
    {HT : IsDefEqStrong sourceEnv U Γ A B (.sort u)}
    {He : IsDefEqStrong sourceEnv U Γ e e' A}
    (type : OriginalPayload current fuel sourceEnv finalEnv U registry HT)
    (term : OriginalPayload current fuel sourceEnv finalEnv U registry He) :
    OriginalPayload current fuel sourceEnv finalEnv U registry (.defeqDF hu HT He) :=
  ⟨Joint.convert henv hscoped type.joint term.joint,
    term.leftFormation, term.rightFormation⟩

theorem bvar (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (lookup : Lookup Γ index A) (hu : u.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    (domain : OriginalPayload current fuel sourceEnv finalEnv U registry HA) :
    OriginalPayload current fuel sourceEnv finalEnv U registry (.bvar lookup hu HA) :=
  ⟨Joint.bvar henv hscoped lookup domain.joint, trivial, trivial⟩

end OriginalPayload

/-- Native natural/declared domain readers consume retained original Pi
payloads at the SAME fuel. The roots may have different earlier source stages;
no semantic call is made on the raw formation proofs returned by inversion. -/
theorem NativeIndexTemplates.originalDomainsBounded
    {current : Name → Bool} {fuel : Nat}
    {naturalEnv declaredEnv finalEnv : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {data : InductiveSignature.NativeRecursorData}
    {program : InductiveSignature.NativeRecursorData.SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    {naturalRoot : IsDefEqStrong naturalEnv U []
      (templates.recursorType.instL program.levels) (templates.recursorType.instL program.levels)
      (.sort naturalLevel)}
    {declaredRoot : IsDefEqStrong declaredEnv U []
      (program.equation.type.instL program.levels) (program.equation.type.instL program.levels)
      (.sort declaredLevel)}
    (natural : OriginalPayload current fuel naturalEnv finalEnv U registry naturalRoot)
    (declared : OriginalPayload current fuel declaredEnv finalEnv U registry declaredRoot) :
    ((∃ level, OriginalTypePayload current fuel naturalEnv finalEnv U registry
        templates.naturalContext templates.naturalDomain (.sort level)) ∧
      SourcePiFormation (OriginalTypePayload current fuel naturalEnv finalEnv U registry)
        templates.naturalContext templates.naturalDomain) ∧
    ((∃ level, OriginalTypePayload current fuel declaredEnv finalEnv U registry
        templates.declaredContext templates.declaredDomain (.sort level)) ∧
      SourcePiFormation (OriginalTypePayload current fuel declaredEnv finalEnv U registry)
        templates.declaredContext templates.declaredDomain) :=
  templates.sourceDomains ⟨naturalLevel, naturalRoot, natural.joint⟩ natural.leftFormation
    ⟨declaredLevel, declaredRoot, declared.joint⟩ declared.leftFormation

end Lean4Lean.AnchoredSource.Adapted.Staged
