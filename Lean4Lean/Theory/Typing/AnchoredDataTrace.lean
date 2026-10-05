import Lean4Lean.Theory.Typing.AnchoredTraceEndpoint
import Lean4Lean.Theory.Typing.CanonicalDataHeadProjection

/-! Actual constructor displays absorb a concrete trace endpoint and preserve
their literal declaration result and frozen lower-rank argument requests. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

theorem TraceEndpoint.proj {name : Name}
    (lookup : registry.projections name = some info)
    (definitions : registry.definitions info.ctorName = none)
    (natives : registry.natives info.ctorName = none)
    (quotient : registry.quotient = false ∨ info.ctorName ≠ ``Quot.lift)
    (endpoint : TraceEndpoint registry front expression result) :
    TraceEndpoint registry front (.proj name index expression) (.proj name index result) := by
  cases endpoint with
  | traced trace => exact .traced (trace.proj lookup definitions natives quotient)
  | lifted => exact .lifted

def ConstructorExposure.prependTrace
    {Γ Δ front : List VExpr} {expression middle type head : VExpr} {ρ : Lift}
    (henv : env.Ordered)
    (trace : CanonicalDataHead.Trace registry expression front middle)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (equal : env.IsDefEq U (front ++ Γ)
      (expression.lift' (.skipN .refl front.length)) middle (type.lift' (.skipN .refl front.length)))
    (E : ConstructorExposure env U registry (front ++ Γ) middle
      (type.lift' (.skipN .refl front.length)) Δ ρ head) :
    ConstructorExposure env U registry Γ expression type Δ
      ((Lift.skipN .refl front.length).comp ρ) head where
  added := E.added ++ front
  result := E.result
  postMap := E.postMap
  trace := trace.trans E.trace
  generated := by
    simpa only [List.append_assoc, List.length_append, Lift.comp_skipN,
      Lift.comp, Lift.skipN_skipN, Nat.add_comm] using generated.comp E.generated henv
  postContext := E.postContext
  post := by simpa only [List.append_assoc] using E.post
  terminal := E.terminal
  map_eq := by
    simpa only [← Lift.comp_assoc, List.length_append, Lift.comp_skipN,
      Lift.comp, Lift.skipN_skipN, Nat.add_comm] using
      congrArg ((Lift.skipN .refl front.length).comp ·) E.map_eq
  result_eq := E.result_eq
  sound := by
    simpa only [lift'_comp] using ((E.insertion henv).eq henv equal).trans E.sound

noncomputable def ConstructorExposure.prependEndpoint
    {Γ Δ front : List VExpr} {expression middle type head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (endpoint : TraceEndpoint registry front expression middle)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (equal : env.IsDefEq U (front ++ Γ)
      (expression.lift' (.skipN .refl front.length)) middle (type.lift' (.skipN .refl front.length)))
    (E : ConstructorExposure env U registry (front ++ Γ) middle
      (type.lift' (.skipN .refl front.length)) Δ ρ head) :
    ConstructorExposure env U registry Γ expression type Δ
      ((Lift.skipN .refl front.length).comp ρ) head := Classical.choice (by
  cases endpoint with
  | traced trace => exact ⟨E.prependTrace henv trace generated equal⟩
  | lifted => exact E.absorb henv hscoped generated)

def ConstructorDisplay.prependTrace
    {Γ Δ front : List VExpr} {expression middle type head : VExpr} {ρ : Lift}
    (henv : env.Ordered)
    (trace : CanonicalDataHead.Trace registry expression front middle)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (equal : env.IsDefEq U (front ++ Γ)
      (expression.lift' (.skipN .refl front.length)) middle (type.lift' (.skipN .refl front.length)))
    (display : ConstructorDisplay env U registry (front ++ Γ) middle
      (type.lift' (.skipN .refl front.length)) Δ ρ head) :
    ConstructorDisplay env U registry Γ expression type Δ
      ((Lift.skipN .refl front.length).comp ρ) head where
  baseWF := generated.baseWF
  route := MixedInsertion.comp (.proof generated) display.route
  origin := by
    have before := (ConstructorOrigin.ofTrace henv trace generated equal).mixed henv display.route
    simpa only [← lift'_comp] using before.trans display.origin
  sound := by
    simpa only [← lift'_comp] using (display.route.eq henv equal).trans display.sound

noncomputable def ConstructorDisplay.prependEndpoint
    {Γ Δ front : List VExpr} {expression middle type head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (endpoint : TraceEndpoint registry front expression middle)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (equal : env.IsDefEq U (front ++ Γ)
      (expression.lift' (.skipN .refl front.length)) middle (type.lift' (.skipN .refl front.length)))
    (display : ConstructorDisplay env U registry (front ++ Γ) middle
      (type.lift' (.skipN .refl front.length)) Δ ρ head) :
    ConstructorDisplay env U registry Γ expression type Δ
      ((Lift.skipN .refl front.length).comp ρ) head := Classical.choice (by
  cases endpoint with
  | traced trace => exact ⟨display.prependTrace henv trace generated equal⟩
  | lifted => exact display.absorb henv hscoped generated)

noncomputable def RankedData.ConstructorWitness.prependEndpoints
    {lower : Relations n} {Γ front : List VExpr}
    {left right leftResult rightResult type : VExpr} {demand : ConstructorData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftTrace : TraceEndpoint registry front left leftResult)
    (rightTrace : TraceEndpoint registry front right rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftEq : env.IsDefEq U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult (type.lift' (.skipN .refl front.length)))
    (rightEq : env.IsDefEq U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult (type.lift' (.skipN .refl front.length)))
    (W : RankedData.ConstructorWitness env U registry lower (front ++ Γ) leftResult rightResult
      (type.lift' (.skipN .refl front.length)) (demand.rename (.skipN .refl front.length))) :
    RankedData.ConstructorWitness env U registry lower Γ left right type demand where
  headInert := W.headInert
  context := W.context
  map := (Lift.skipN .refl front.length).comp W.map
  leftLevels := W.leftLevels
  rightLevels := W.rightLevels
  leftArguments := W.leftArguments
  rightArguments := W.rightArguments
  leftExposure := W.leftExposure.prependEndpoint henv hscoped leftTrace generated leftEq
  rightExposure := W.rightExposure.prependEndpoint henv hscoped rightTrace generated rightEq
  leftTerminal := W.leftTerminal
  rightTerminal := W.rightTerminal
  leftUniverses := W.leftUniverses
  rightUniverses := W.rightUniverses
  arguments := by
    have args := W.arguments
    change RankedData.Arguments env U lower W.context
      ((demand.arguments.map (DataRequest.rename (.skipN .refl front.length))).map (DataRequest.rename W.map))
      W.leftArguments W.rightArguments at args
    simpa only [List.map_map, Function.comp_def, DataRequest.rename_comp] using args
  leftHeader := W.leftHeader
  rightHeader := W.rightHeader
  leftBridge := by
    have bridge := W.leftBridge
    change RankedData.FamilyRelation env U registry lower W.context W.leftHeader.result
      ((type.lift' (.skipN .refl front.length)).lift' W.map)
      ((demand.family.rename (.skipN .refl front.length)).rename W.map) at bridge
    simpa only [← lift'_comp, FamilyData.rename_comp] using bridge
  rightBridge := by
    have bridge := W.rightBridge
    change RankedData.FamilyRelation env U registry lower W.context W.rightHeader.result
      ((type.lift' (.skipN .refl front.length)).lift' W.map)
      ((demand.family.rename (.skipN .refl front.length)).rename W.map) at bridge
    simpa only [← lift'_comp, FamilyData.rename_comp] using bridge

private theorem frontMap (ρ : Lift) (front : List VExpr) :
    (Lift.skipN .refl front.length).comp (ρ.consN front.length) =
      ρ.comp (.skipN .refl (renameAdded ρ front).length) := by
  simp only [renameAdded_length, Lift.skipN_comp_consN, Lift.refl_comp,
    Lift.comp_skipN, Lift.comp]

theorem RankedData.ConstructorRelation.prependEndpoints
    {lower : Relations n} {Γ front : List VExpr}
    {left right leftResult rightResult type : VExpr} {demand : ConstructorData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftTrace : TraceEndpoint registry front left leftResult)
    (rightTrace : TraceEndpoint registry front right rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftEq : env.IsDefEq U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult (type.lift' (.skipN .refl front.length)))
    (rightEq : env.IsDefEq U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult (type.lift' (.skipN .refl front.length)))
    (H : RankedData.ConstructorRelation env U registry lower (front ++ Γ) leftResult rightResult
      (type.lift' (.skipN .refl front.length)) (demand.rename (.skipN .refl front.length))) :
    RankedData.ConstructorRelation env U registry lower Γ left right type demand := by
  intro Δ ρ future
  obtain ⟨newGenerated, extended⟩ := generated.renameFront front future henv
  obtain ⟨W⟩ := H _ _ extended
  have W' : RankedData.ConstructorWitness env U registry lower (renameAdded ρ front ++ Δ)
      (leftResult.lift' (ρ.consN front.length)) (rightResult.lift' (ρ.consN front.length))
      ((type.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length))
      ((demand.rename ρ).rename (.skipN .refl (renameAdded ρ front).length)) := by
    simpa only [← lift'_comp, ConstructorData.rename_comp, frontMap] using W
  have leftEq' : env.IsDefEq U (renameAdded ρ front ++ Δ)
      ((left.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length))
      (leftResult.lift' (ρ.consN front.length))
      ((type.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length)) := by
    simpa only [← lift'_comp, frontMap] using leftEq.weak' henv extended.weakening
  have rightEq' : env.IsDefEq U (renameAdded ρ front ++ Δ)
      ((right.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length))
      (rightResult.lift' (ρ.consN front.length))
      ((type.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length)) := by
    simpa only [← lift'_comp, frontMap] using rightEq.weak' henv extended.weakening
  exact ⟨W'.prependEndpoints henv hscoped (leftTrace.rename hscoped ρ) (rightTrace.rename hscoped ρ)
    (by simpa only [renameAdded_length] using newGenerated) leftEq' rightEq'⟩

end Lean4Lean.AnchoredSemantics
