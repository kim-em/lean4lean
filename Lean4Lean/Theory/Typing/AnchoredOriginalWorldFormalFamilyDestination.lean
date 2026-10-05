import Lean4Lean.Theory.Typing.ProjectionParameterProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderDoublePi
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistorySponsorship
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank

/-! A formal two-parameter family application in the genuine declaration
stage where the family is installed and its constructor is still fresh.
The original proof is constructed here; its potentially large size is paid
by the strict declaration-stage decrease. Captured worlds keep their actual
separate sponsorship. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000


/-- The family's real original header, viewed immediately after the type
constants were installed. In particular this does not assert that the family
was present in its own header source. -/
def _root_.Lean4Lean.VEnv.ProjectionParameterOrigin.familyTypesOrigin (origin : VEnv.ProjectionParameterOrigin sourceEnv name info) :
    ConstantHeaderOrigin origin.types name origin.family.toVConstant := by
  have member : origin.family.toVConstVal ∈ origin.declaration.typeConstants :=
    List.mem_map.mpr ⟨origin.family, origin.familyMember, rfl⟩
  exact {
    source := origin.base
    ordered := origin.baseOrdered
    formation := origin.familyWF
    sourceBelow := VEnv.addConstVals_le origin.addTypes
    fresh := by simpa only [origin.name_eq] using VEnv.addConstVals_names_fresh origin.addTypes _ member
    constant := by simpa only [origin.name_eq] using VEnv.addConstVals_get origin.addTypes member }


structure FormalFamilyDestination
    {levels : List VLevel} {U : Nat}
    (origin : VEnv.ProjectionParameterOrigin sourceEnv name info)
    (signature : ConstantTelescope (origin.family.type.instL levels))
    (domains : signature.domains = [C, D]) where
  firstLevel : VLevel
  secondLevel : VLevel
  resultLevel : VLevel
  firstLevelWF : firstLevel.WF U
  secondLevelWF : secondLevel.WF U
  resultLevelWF : resultLevel.WF U
  firstOriginal : Derivation origin.types U [] C C (.sort firstLevel)
  secondOriginal : Derivation origin.types U [C] D D (.sort secondLevel)
  resultOriginal : Derivation origin.types U [D, C] signature.result signature.result (.sort resultLevel)
  original : Derivation origin.types U [D, C]
    (.app (.app (.const name levels) (.bvar 1)) (.bvar 0))
    (.app (.app (.const name levels) (.bvar 1)) (.bvar 0)) signature.result

namespace FormalFamilyDestination

variable {sourceEnv : VEnv} {name : Name} {info : VProjectionInfo}
  {levels : List VLevel} {U : Nat} {C D : VExpr}
  {origin : VEnv.ProjectionParameterOrigin sourceEnv name info}
  {signature : ConstantTelescope (origin.family.type.instL levels)}
  {domains : signature.domains = [C, D]}

def firstDomain (destination : FormalFamilyDestination (U := U) origin signature domains) :
    EndpointRef origin.types U [] C (.sort destination.firstLevel) := .left destination.firstOriginal

def secondDomain (destination : FormalFamilyDestination (U := U) origin signature domains) :
    EndpointRef origin.types U [C] D (.sort destination.secondLevel) := .left destination.secondOriginal

def resultFormation (destination : FormalFamilyDestination (U := U) origin signature domains) :
    EndpointRef origin.types U [D,C] signature.result (.sort destination.resultLevel) := .left destination.resultOriginal

def context (destination : FormalFamilyDestination (U := U) origin signature domains) :
    ContextDerivation origin.types U [D, C] :=
  .cons (.cons .nil destination.firstDomain) destination.secondDomain

def node (destination : FormalFamilyDestination (U := U) origin signature domains) :
    EndpointState origin.types U [D, C]
      (.app (.app (.const name levels) (.bvar 1)) (.bvar 0)) signature.result :=
  .ref (.left destination.original)

noncomputable def provenance (destination : FormalFamilyDestination (U := U) origin signature domains) :
    EndpointProvenance destination.context destination.node :=
  .ofLocation .here destination.context

/-- Both native Pis use the same exact domain originals as the formal
capture graph; successor replay therefore stays in the installed type stage. -/
def bodyOriginal (destination : FormalFamilyDestination (U := U) origin signature domains) :
    Derivation origin.types U [C] (.forallE D signature.result) (.forallE D signature.result)
      (.sort (.imax destination.secondLevel destination.resultLevel)) :=
  .forallEDF destination.secondLevelWF destination.resultLevelWF
    destination.secondOriginal destination.resultOriginal destination.resultOriginal

def headerOriginal (destination : FormalFamilyDestination (U := U) origin signature domains) :
    Derivation origin.types U [] (.forallE C (.forallE D signature.result))
      (.forallE C (.forallE D signature.result))
      (.sort (.imax destination.firstLevel (.imax destination.secondLevel destination.resultLevel))) :=
  .forallEDF destination.firstLevelWF ⟨destination.secondLevelWF, destination.resultLevelWF⟩
    destination.firstOriginal destination.bodyOriginal destination.bodyOriginal

def nativeBody (destination : FormalFamilyDestination (U := U) origin signature domains) :
    EndpointState origin.types U [C] (.forallE D signature.result)
      (.sort (.imax destination.secondLevel destination.resultLevel)) :=
  .ref (.left destination.bodyOriginal)

def nativeHeader (destination : FormalFamilyDestination (U := U) origin signature domains) :
    EndpointState origin.types U [] (.forallE C (.forallE D signature.result))
      (.sort (.imax destination.firstLevel (.imax destination.secondLevel destination.resultLevel))) :=
  .pi destination.firstLevelWF ⟨destination.secondLevelWF, destination.resultLevelWF⟩
    (.ref destination.firstDomain) destination.nativeBody

noncomputable def nativeSide
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (common : List VExpr) : OriginalPiTypeRouteSide U common where
  sourceEnv := origin.types
  source := []
  A := C
  B := .forallE D signature.result
  u := destination.firstLevel
  v := .imax destination.secondLevel destination.resultLevel
  hu := destination.firstLevelWF
  hv := ⟨destination.secondLevelWF, destination.resultLevelWF⟩
  domain := .ref destination.firstDomain
  body := destination.nativeBody
  rootSource := []
  rootExpression := .forallE C (.forallE D signature.result)
  rootType := .sort (.imax destination.firstLevel (.imax destination.secondLevel destination.resultLevel))
  root := .left destination.headerOriginal
  initial := .nil
  location := .expose .here
  raw := Subst.id
  graph := closedCaptureGraph .nil common

/-- The declaration context is instantiated by the two actual caller
operands, in the same order as the two positive captures. -/
noncomputable def display
    (destination : FormalFamilyDestination (U := U) origin signature domains)
    (graph : OriginalCaptureMap (common := common) destination.context
      ((Subst.id.cons first).cons second)) :
    OriginalNestedDisplay U common (.app (.app (.const name levels) first) second)
      (signature.result.subst ((Subst.id.cons first).cons second)) where
  sourceEnv := origin.types
  source := [D, C]
  sourceExpression := .app (.app (.const name levels) (.bvar 1)) (.bvar 0)
  sourceType := signature.result
  context := destination.context
  node := destination.node
  provenance := destination.provenance
  raw := (Subst.id.cons first).cons second
  graph := graph
  expression_eq := rfl
  type_eq := rfl

end FormalFamilyDestination

private theorem formalFamilyDestinationExists
    {levels : List VLevel} {U : Nat}
    (origin : VEnv.ProjectionParameterOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelsLength : levels.length = origin.family.uvars)
    (signature : ConstantTelescope (origin.family.type.instL levels))
    (domains : signature.domains = [C, D]) :
    Nonempty (FormalFamilyDestination (U := U) origin signature domains) := by
  let header := origin.familyTypesOrigin
  let exposed := header.doublePiSyntax levelsWF signature domains
  have below := VEnv.addConstVals_le origin.addTypes
  obtain ⟨first⟩ := Derivation.reify (exposed.firstDomain.sound.mono below)
  obtain ⟨second⟩ := Derivation.reify (exposed.secondDomain.sound.mono below)
  obtain ⟨resultFormation⟩ := Derivation.reify (exposed.body.sound.mono below)
  let firstDomain : EndpointRef origin.types U [] C (.sort exposed.cu) := .left first
  let secondDomain : EndpointRef origin.types U [C] D (.sort exposed.dv) := .left second
  let context : ContextDerivation origin.types U [D, C] :=
    .cons (.cons .nil firstDomain) secondDomain
  have firstClosed : C.Closed :=
    exposed.firstDomain.sound.defeq.closedN header.ordered trivial
  have bodyClosed : (VExpr.forallE D signature.result).ClosedN 1 :=
    exposed.firstBody.sound.defeq.closedN header.ordered ⟨trivial, firstClosed⟩
  have firstLookup : Lookup [C] 0 C := by simpa only [firstClosed.lift_eq] using (Lookup.zero (ty := C) (Γ := []))
  have constant : origin.types.HasType U [C] (.const name levels)
      (.forallE C (.forallE D signature.result)) := by
    rw [← doubleHeaderDomain_eq signature domains]
    exact .const header.constant levelsWF levelsLength
  have firstApp := HasType.app constant (HasType.bvar firstLookup)
  have bodyInst : (VExpr.forallE D signature.result).inst (.bvar 0) =
      VExpr.forallE D signature.result := by
    calc
      _ = ((VExpr.forallE D signature.result).liftN 1 1).inst (.bvar 0) :=
        congrArg (fun e => e.inst (.bvar 0)) (bodyClosed.liftN_eq (n := 1) (Nat.le_refl 1)).symm
      _ = _ := instN_bvar0 _ 0
  rw [bodyInst] at firstApp
  have lifted := firstApp.weakN origin.typesOrdered (Ctx.LiftN.one (A := D))
  have final := HasType.app lifted (HasType.bvar (Lookup.zero (ty := D) (Γ := [C])))
  have finalTyped : origin.types.HasType U [D, C]
      (.app (.app (.const name levels) (.bvar 1)) (.bvar 0)) signature.result := by
    simpa only [liftN, liftVar, Nat.lt_irrefl, if_false, Nat.add_zero, instN_bvar0] using final
  obtain ⟨original⟩ := Derivation.reify (finalTyped.strong origin.typesOrdered context.forget.defeq)
  exact ⟨⟨exposed.cu, exposed.dv, exposed.w, exposed.hcu, exposed.hdv, exposed.hw,
    first, second, resultFormation, original⟩⟩

/-- Computes both genuine domain originals and the formal family endpoint;
there is no supplied original proof or semantic family observation. -/
noncomputable def _root_.Lean4Lean.VEnv.ProjectionParameterOrigin.formalFamilyDestination
    {levels : List VLevel} {U : Nat}
    (origin : VEnv.ProjectionParameterOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelsLength : levels.length = origin.family.uvars)
    (signature : ConstantTelescope (origin.family.type.instL levels))
    (domains : signature.domains = [C, D]) :
    FormalFamilyDestination (U := U) origin signature domains :=
  Classical.choice (formalFamilyDestinationExists origin levelsWF levelsLength signature domains)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
