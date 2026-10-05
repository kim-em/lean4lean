import Lean4Lean.Theory.Typing.SourcePiFormation
import Lean4Lean.Theory.Typing.AnchoredNativeFormationPayload
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedAppJoint
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaJoint
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceBetaJoint
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaJoint
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceVariableRule
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSortRule
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceProofIrrel

/-! Original-child formation payloads for relative declaration-stage induction.

The raw derivation lives in the predecessor source environment; its semantic
joint theorem lives in the final target environment. Literal Pi components
retain both together. The registered-rule routing lemmas deliberately require
the current node's semantic result: they do not prove constant/native adequacy.
-/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

/-- A component's original raw typing and its already-established semantics. -/
def OriginalTypePayload (sourceEnv finalEnv : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (Γ : List VExpr) (expression type : VExpr) : Prop :=
  IsDefEqStrong sourceEnv U Γ expression expression type ∧
    GradedJoint finalEnv U registry Γ expression expression type

/-- The induction payload is indexed by the actual original Strong derivation.
Formation trees concern the literal endpoints, even if their assigned type was
converted. They never invoke adequacy on the raw typings stored in the tree. -/
structure OriginalPayload (sourceEnv finalEnv : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) {Γ : List VExpr} {left right type : VExpr}
    (_original : IsDefEqStrong sourceEnv U Γ left right type) : Prop where
  joint : GradedJoint finalEnv U registry Γ left right type
  leftFormation : SourcePiFormation (OriginalTypePayload sourceEnv finalEnv U registry) Γ left
  rightFormation : SourcePiFormation (OriginalTypePayload sourceEnv finalEnv U registry) Γ right

namespace OriginalPayload
variable {sourceEnv finalEnv : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

/-- Diagonal semantics comes from the original child's joint theorem; only the
raw half uses Strong's local endpoint-typing operation. -/
theorem leftType (henv : finalEnv.Ordered) (hscoped : registry.Scoped) {H : IsDefEqStrong sourceEnv U Γ left right type}
    (payload : OriginalPayload sourceEnv finalEnv U registry H) :
    OriginalTypePayload sourceEnv finalEnv U registry Γ left type :=
  ⟨H.hasType.1, payload.joint.left henv hscoped⟩

theorem rightType (henv : finalEnv.Ordered) (hscoped : registry.Scoped) {H : IsDefEqStrong sourceEnv U Γ left right type}
    (payload : OriginalPayload sourceEnv finalEnv U registry H) :
    OriginalTypePayload sourceEnv finalEnv U registry Γ right type :=
  ⟨H.hasType.2, payload.joint.right henv hscoped⟩

theorem symm {H : IsDefEqStrong sourceEnv U Γ left right type}
    (payload : OriginalPayload sourceEnv finalEnv U registry H) :
    OriginalPayload sourceEnv finalEnv U registry H.symm :=
  ⟨payload.joint.symm, payload.rightFormation, payload.leftFormation⟩

theorem trans (henv : finalEnv.Ordered) (hscoped : registry.Scoped) {H₁ : IsDefEqStrong sourceEnv U Γ left middle type}
    {H₂ : IsDefEqStrong sourceEnv U Γ middle right type}
    (first : OriginalPayload sourceEnv finalEnv U registry H₁)
    (second : OriginalPayload sourceEnv finalEnv U registry H₂) :
    OriginalPayload sourceEnv finalEnv U registry (H₁.trans H₂) :=
  ⟨GradedJoint.trans henv hscoped first.joint second.joint,
    first.leftFormation, second.rightFormation⟩

theorem bvar (henv : finalEnv.Ordered) (hscoped : registry.Scoped) (lookup : Lookup Γ index A) (hu : u.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    (domain : OriginalPayload sourceEnv finalEnv U registry HA) :
    OriginalPayload sourceEnv finalEnv U registry (.bvar lookup hu HA) :=
  ⟨GradedJoint.bvar henv hscoped lookup domain.joint, trivial, trivial⟩

theorem sortDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped) (hu : u.WF U) (hv : v.WF U) (equal : u ≈ v) :
    OriginalPayload sourceEnv finalEnv U registry
      (IsDefEqStrong.sortDF (Γ := Γ) hu hv equal) :=
  ⟨GradedJoint.sortDF henv hscoped hu hv equal, trivial, trivial⟩

theorem forallEDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A' (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B' (.sort v)}
    {HB' : IsDefEqStrong sourceEnv U (A' :: Γ) B B' (.sort v)}
    (domain : OriginalPayload sourceEnv finalEnv U registry HA)
    (body : OriginalPayload sourceEnv finalEnv U registry HB)
    (body' : OriginalPayload sourceEnv finalEnv U registry HB') :
    OriginalPayload sourceEnv finalEnv U registry (.forallEDF hu hv HA HB HB') := by
  exact ⟨GradedJoint.forallEDF henv hscoped domain.joint body.joint body'.joint
      (HA.defeq.mono hle) (HB.defeq.mono hle) (HB'.defeq.mono hle),
    .pi (domain.leftType henv hscoped) (body.leftType henv hscoped)
      domain.leftFormation body.leftFormation,
    .pi (domain.rightType henv hscoped) (body'.rightType henv hscoped)
      domain.rightFormation body'.rightFormation⟩

theorem appDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {HF : IsDefEqStrong sourceEnv U Γ f f' (.forallE A B)}
    {Ha : IsDefEqStrong sourceEnv U Γ a a' A}
    {HBa : IsDefEqStrong sourceEnv U Γ (B.inst a) (B.inst a') (.sort v)}
    (domain : OriginalPayload sourceEnv finalEnv U registry HA)
    (body : OriginalPayload sourceEnv finalEnv U registry HB)
    (function : OriginalPayload sourceEnv finalEnv U registry HF)
    (argument : OriginalPayload sourceEnv finalEnv U registry Ha)
    (result : OriginalPayload sourceEnv finalEnv U registry HBa) :
    OriginalPayload sourceEnv finalEnv U registry (.appDF hu hv HA HB HF Ha HBa) :=
  ⟨GradedJoint.appDF henv hscoped domain.joint body.joint function.joint argument.joint
    result.joint (HA.defeq.mono hle) (HB.defeq.mono hle) (Ha.defeq.mono hle),
    trivial, trivial⟩

theorem lamDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A' (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {HB' : IsDefEqStrong sourceEnv U (A' :: Γ) B B (.sort v)}
    {He : IsDefEqStrong sourceEnv U (A :: Γ) e e' B}
    {He' : IsDefEqStrong sourceEnv U (A' :: Γ) e e' B}
    (domain : OriginalPayload sourceEnv finalEnv U registry HA)
    (bodyType : OriginalPayload sourceEnv finalEnv U registry HB)
    (bodyType' : OriginalPayload sourceEnv finalEnv U registry HB')
    (body : OriginalPayload sourceEnv finalEnv U registry He)
    (body' : OriginalPayload sourceEnv finalEnv U registry He') :
    OriginalPayload sourceEnv finalEnv U registry (.lamDF hu hv HA HB HB' He He') :=
  ⟨GradedJoint.lamDF henv hscoped domain.joint bodyType.joint bodyType'.joint body.joint
    body'.joint (HA.defeq.mono hle) (HB.defeq.mono hle) (HB'.defeq.mono hle)
    (He.defeq.mono hle) (He'.defeq.mono hle), trivial, trivial⟩

theorem defeqDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped) (hu : u.WF U)
    {HT : IsDefEqStrong sourceEnv U Γ A B (.sort u)}
    {He : IsDefEqStrong sourceEnv U Γ e e' A}
    (type : OriginalPayload sourceEnv finalEnv U registry HT)
    (term : OriginalPayload sourceEnv finalEnv U registry He) :
    OriginalPayload sourceEnv finalEnv U registry (.defeqDF hu HT He) :=
  ⟨GradedJoint.convert henv hscoped type.joint term.joint,
    term.leftFormation, term.rightFormation⟩

theorem beta (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {He : IsDefEqStrong sourceEnv U (A :: Γ) e e B}
    {Ha : IsDefEqStrong sourceEnv U Γ a a A}
    {HBa : IsDefEqStrong sourceEnv U Γ (B.inst a) (B.inst a) (.sort v)}
    {Hea : IsDefEqStrong sourceEnv U Γ (e.inst a) (e.inst a) (B.inst a)}
    (domain : OriginalPayload sourceEnv finalEnv U registry HA)
    (bodyType : OriginalPayload sourceEnv finalEnv U registry HB)
    (body : OriginalPayload sourceEnv finalEnv U registry He)
    (argument : OriginalPayload sourceEnv finalEnv U registry Ha)
    (instantiated : OriginalPayload sourceEnv finalEnv U registry Hea) :
    OriginalPayload sourceEnv finalEnv U registry (.beta hu hv HA HB He Ha HBa Hea) :=
  ⟨GradedJoint.beta henv hscoped domain.joint argument.joint body.joint bodyType.joint
    instantiated.joint (HA.defeq.mono hle) (HB.defeq.mono hle) (He.defeq.mono hle)
    (Ha.defeq.mono hle) (HBa.defeq.mono hle), trivial, instantiated.leftFormation⟩

theorem eta (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {HBlift : IsDefEqStrong sourceEnv U (A.lift :: A :: Γ) (B.liftN 1 1) (B.liftN 1 1) (.sort v)}
    {He : IsDefEqStrong sourceEnv U Γ e e (.forallE A B)}
    {Helift : IsDefEqStrong sourceEnv U (A :: Γ) e.lift e.lift (.forallE A.lift (B.liftN 1 1))}
    {HAlift : IsDefEqStrong sourceEnv U (A :: Γ) A.lift A.lift (.sort u)}
    (domain : OriginalPayload sourceEnv finalEnv U registry HA)
    (bodyType : OriginalPayload sourceEnv finalEnv U registry HB)
    (term : OriginalPayload sourceEnv finalEnv U registry He) :
    OriginalPayload sourceEnv finalEnv U registry (.eta hu hv HA HB HBlift He Helift HAlift) :=
  ⟨GradedJoint.eta henv hscoped domain.joint bodyType.joint term.joint
    (HA.defeq.mono hle) (HB.defeq.mono hle) (He.defeq.mono hle),
    trivial, term.leftFormation⟩

theorem proofIrrel (henv : finalEnv.Ordered)
    {HP : IsDefEqStrong sourceEnv U Γ P P (.sort .zero)}
    {Hp : IsDefEqStrong sourceEnv U Γ p p P}
    {Hq : IsDefEqStrong sourceEnv U Γ q q P}
    (proposition : OriginalPayload sourceEnv finalEnv U registry HP)
    (left : OriginalPayload sourceEnv finalEnv U registry Hp)
    (right : OriginalPayload sourceEnv finalEnv U registry Hq) :
    OriginalPayload sourceEnv finalEnv U registry (.proofIrrel HP Hp Hq) :=
  ⟨GradedJoint.proofIrrel henv proposition.joint left.joint right.joint,
    left.leftFormation, right.leftFormation⟩

/-- A constant head has no literal Pi subtree. Its semantics is the separate
constant-stage obligation, not a consequence of this routing lemma. -/
theorem constDF {H : IsDefEqStrong sourceEnv U Γ (.const name levels) (.const name levels') type}
    (joint : GradedJoint finalEnv U registry Γ (.const name levels) (.const name levels') type) :
    OriginalPayload sourceEnv finalEnv U registry H := ⟨joint, trivial, trivial⟩

/-- Abstract case heads likewise have no literal Pi subtree. -/
theorem elimDF {H : IsDefEqStrong sourceEnv U Γ (.elim block owner levels)
      (.elim block owner levels') type}
    (joint : GradedJoint finalEnv U registry Γ (.elim block owner levels)
      (.elim block owner levels') type) :
    OriginalPayload sourceEnv finalEnv U registry H := ⟨joint, trivial, trivial⟩

theorem projDF {H : IsDefEqStrong sourceEnv U Γ (.proj name index major)
      (.proj name index major') type}
    (joint : GradedJoint finalEnv U registry Γ (.proj name index major)
      (.proj name index major') type) :
    OriginalPayload sourceEnv finalEnv U registry H := ⟨joint, trivial, trivial⟩

/-- Registration's computation proof still has to supply `joint`. Formation
routing uses the two endpoint-typing children in the original ambient context. -/
theorem extra (registered : sourceEnv.defeqs df)
    (levelsWF : ∀ level ∈ levels, level.WF U) (length : levels.length = df.uvars)
    (hu : u.WF U)
    {HT : IsDefEqStrong sourceEnv U [] (df.type.instL levels) (df.type.instL levels) (.sort u)}
    {HL : IsDefEqStrong sourceEnv U [] (df.lhs.instL levels) (df.lhs.instL levels) (df.type.instL levels)}
    {HR : IsDefEqStrong sourceEnv U [] (df.rhs.instL levels) (df.rhs.instL levels) (df.type.instL levels)}
    {HLΓ : IsDefEqStrong sourceEnv U Γ (df.lhs.instL levels) (df.lhs.instL levels) (df.type.instL levels)}
    {HRΓ : IsDefEqStrong sourceEnv U Γ (df.rhs.instL levels) (df.rhs.instL levels) (df.type.instL levels)}
    (left : OriginalPayload sourceEnv finalEnv U registry HLΓ)
    (right : OriginalPayload sourceEnv finalEnv U registry HRΓ)
    (joint : GradedJoint finalEnv U registry Γ (df.lhs.instL levels)
      (df.rhs.instL levels) (df.type.instL levels)) :
    OriginalPayload sourceEnv finalEnv U registry
      (.extra registered levelsWF length hu HT HL HR HLΓ HRΓ) :=
  ⟨joint, left.leftFormation, right.leftFormation⟩

theorem elimIota {schema : InductiveSignature.CaseSchema}
    {owner : Fin schema.signature.families.size}
    (registered : sourceEnv.eliminators block schema)
    (equations : schema.genericEquations block owner = some rules)
    (member : df ∈ rules) (closed : InductiveSignature.CaseSchema.RuleClosed df)
    (permission : schema.Permission U owner levels target) (hu : u.WF U)
    {HT : IsDefEqStrong sourceEnv U Γ (df.type.instL (target :: levels))
      (df.type.instL (target :: levels)) (.sort u)}
    {HL : IsDefEqStrong sourceEnv U Γ (df.lhs.instL (target :: levels))
      (df.lhs.instL (target :: levels)) (df.type.instL (target :: levels))}
    {HR : IsDefEqStrong sourceEnv U Γ (df.rhs.instL (target :: levels))
      (df.rhs.instL (target :: levels)) (df.type.instL (target :: levels))}
    (left : OriginalPayload sourceEnv finalEnv U registry HL)
    (right : OriginalPayload sourceEnv finalEnv U registry HR)
    (joint : GradedJoint finalEnv U registry Γ (df.lhs.instL (target :: levels))
      (df.rhs.instL (target :: levels)) (df.type.instL (target :: levels))) :
    OriginalPayload sourceEnv finalEnv U registry
      (.elimIota registered equations member closed permission hu HT HL HR) :=
  ⟨joint, left.leftFormation, right.leftFormation⟩

theorem projIota (registered : sourceEnv.projections name info)
    {HP : IsDefEqStrong sourceEnv U Γ
      (.proj name index (mkApps (.const info.ctorName levels) args))
      (.proj name index (mkApps (.const info.ctorName levels) args)) fieldType}
    (member : args[info.nparams + index]? = some field)
    {HF : IsDefEqStrong sourceEnv U Γ field field fieldType}
    (right : OriginalPayload sourceEnv finalEnv U registry HF)
    (joint : GradedJoint finalEnv U registry Γ
      (.proj name index (mkApps (.const info.ctorName levels) args)) field fieldType) :
    OriginalPayload sourceEnv finalEnv U registry (.projIota registered HP member HF) :=
  ⟨joint, trivial, right.leftFormation⟩

private theorem const_apps_formation :
    SourcePiFormation P Γ (mkApps (.const name levels) args) := by
  generalize he : mkApps (.const name levels) args = e
  cases e <;> try trivial
  exact (mkApps_ne_forallE (fn := .const name levels)
    (fun _ _ h => nomatch h) args he).elim

theorem structEta (registered : sourceEnv.projections name info)
    (length : params.length = info.nparams) (noIndices : info.nindices = 0)
    {He : IsDefEqStrong sourceEnv U Γ e e (mkApps (.const name levels) params)}
    {Hctor : IsDefEqStrong sourceEnv U Γ
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj name index e))
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj name index e))
      (mkApps (.const name levels) params)}
    (term : OriginalPayload sourceEnv finalEnv U registry He)
    (joint : GradedJoint finalEnv U registry Γ
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map fun index => .proj name index e)) e
      (mkApps (.const name levels) params)) :
    OriginalPayload sourceEnv finalEnv U registry (.structEta registered length noIndices He Hctor) :=
  ⟨joint, const_apps_formation, term.leftFormation⟩

theorem unitLike (registered : sourceEnv.projections name info)
    (length : params.length = info.nparams) (noIndices : info.nindices = 0)
    (noFields : info.numFields = 0)
    {He : IsDefEqStrong sourceEnv U Γ e e (mkApps (.const name levels) params)}
    {He' : IsDefEqStrong sourceEnv U Γ e' e' (mkApps (.const name levels) params)}
    (left : OriginalPayload sourceEnv finalEnv U registry He)
    (right : OriginalPayload sourceEnv finalEnv U registry He')
    (joint : GradedJoint finalEnv U registry Γ e e' (mkApps (.const name levels) params)) :
    OriginalPayload sourceEnv finalEnv U registry (.unitLike registered length noIndices noFields He He') :=
  ⟨joint, left.leftFormation, right.leftFormation⟩

end OriginalPayload

/-- Instantiate the native telescope reader with genuine predecessor-stage
payloads. No standalone semantic formation hypothesis is introduced for either
selected field domain. The recursor and equation roots may come from different
source stages, while both semantic components use the same final environment. -/
theorem NativeIndexTemplates.originalDomains
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
    (natural : OriginalPayload naturalEnv finalEnv U registry naturalRoot)
    (declared : OriginalPayload declaredEnv finalEnv U registry declaredRoot) :
    ((∃ level, OriginalTypePayload naturalEnv finalEnv U registry
        templates.naturalContext templates.naturalDomain (.sort level)) ∧
      SourcePiFormation (OriginalTypePayload naturalEnv finalEnv U registry)
        templates.naturalContext templates.naturalDomain) ∧
    ((∃ level, OriginalTypePayload declaredEnv finalEnv U registry
        templates.declaredContext templates.declaredDomain (.sort level)) ∧
      SourcePiFormation (OriginalTypePayload declaredEnv finalEnv U registry)
        templates.declaredContext templates.declaredDomain) :=
  templates.sourceDomains ⟨naturalLevel, naturalRoot, natural.joint⟩ natural.leftFormation
    ⟨declaredLevel, declaredRoot, declared.joint⟩ declared.leftFormation

end Lean4Lean.AnchoredSource.Adapted
