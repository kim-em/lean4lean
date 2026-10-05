import Lean4Lean.Theory.Typing.AnchoredExposureAbsorption

/-! Data observations absorb an actual inhabited proof insertion by keeping
their entire private display and composing its map from the original world. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

theorem RankedData.ConstructorWitness.absorb
    {lower : Relations n} {Γ Δ : List VExpr} {ρ : Lift}
    {left right type : VExpr} {demand : ConstructorData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (W : RankedData.ConstructorWitness env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (demand.rename ρ)) :
    Nonempty (RankedData.ConstructorWitness env U registry lower Γ left right type demand) := by
  obtain ⟨leftExposure⟩ := W.leftExposure.absorb henv hscoped I
  obtain ⟨rightExposure⟩ := W.rightExposure.absorb henv hscoped I
  refine ⟨{
    headInert := W.headInert
    context := W.context, map := ρ.comp W.map
    leftLevels := W.leftLevels, rightLevels := W.rightLevels
    leftArguments := W.leftArguments, rightArguments := W.rightArguments
    leftExposure := leftExposure, rightExposure := rightExposure
    leftTerminal := W.leftTerminal, rightTerminal := W.rightTerminal
    leftUniverses := W.leftUniverses, rightUniverses := W.rightUniverses
    arguments := ?_
    leftHeader := W.leftHeader, rightHeader := W.rightHeader
    leftBridge := ?_, rightBridge := ?_ }⟩
  · have arguments := W.arguments
    change RankedData.Arguments env U lower W.context
      ((demand.arguments.map (DataRequest.rename ρ)).map (DataRequest.rename W.map))
      W.leftArguments W.rightArguments at arguments
    simpa only [List.map_map, Function.comp_def, DataRequest.rename_comp] using arguments
  · have bridge := W.leftBridge
    change RankedData.FamilyRelation env U registry lower W.context W.leftHeader.result
      ((type.lift' ρ).lift' W.map) ((demand.family.rename ρ).rename W.map) at bridge
    simpa only [← lift'_comp, FamilyData.rename_comp] using bridge
  · have bridge := W.rightBridge
    change RankedData.FamilyRelation env U registry lower W.context W.rightHeader.result
      ((type.lift' ρ).lift' W.map) ((demand.family.rename ρ).rename W.map) at bridge
    simpa only [← lift'_comp, FamilyData.rename_comp] using bridge

theorem RankedData.RecordWitness.absorb
    {lower : Relations n} {Γ Δ : List VExpr} {ρ : Lift}
    {left right type : VExpr} {demand : RecordData (Profile n)}
    (I : ProofInsertion env U Γ Δ ρ)
    (W : RankedData.RecordWitness env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (demand.rename ρ)) :
    Nonempty (RankedData.RecordWitness env U registry lower Γ left right type demand) := by
  refine ⟨{
    baseWF := I.baseWF, context := W.context, map := ρ.comp W.map
    insertion := MixedInsertion.comp (.proof I) W.insertion
    info := W.info, lookup := W.lookup
    ctorDefinition := W.ctorDefinition, ctorNative := W.ctorNative, ctorQuotient := W.ctorQuotient
    bounded := ?_, typeCode := ?_, leftType := ?_, rightType := ?_
    leftOrigins := ?_, rightOrigins := ?_, fields := ?_ }⟩
  · intro entry member
    exact W.bounded (entry.1, DataRequest.rename ρ entry.2) (List.mem_map.mpr ⟨entry, member, rfl⟩)
  · have code := W.typeCode
    change RankedData.FamilyRelation env U registry lower W.context
      ((type.lift' ρ).lift' W.map) ((type.lift' ρ).lift' W.map)
      ((demand.family.rename ρ).rename W.map) at code
    simpa only [← lift'_comp, FamilyData.rename_comp] using code
  · simpa only [← lift'_comp] using W.leftType
  · simpa only [← lift'_comp] using W.rightType
  · intro entry member
    have origin := W.leftOrigins (entry.1, DataRequest.rename ρ entry.2) (List.mem_map.mpr ⟨entry, member, rfl⟩)
    simpa only [RecordData.rename, RecordData.map, FamilyData.map,
      DataRequest.rename, DataRequest.map, KeyData.map, ← lift'_comp] using origin
  · intro entry member
    have origin := W.rightOrigins (entry.1, DataRequest.rename ρ entry.2) (List.mem_map.mpr ⟨entry, member, rfl⟩)
    simpa only [RecordData.rename, RecordData.map, FamilyData.map,
      DataRequest.rename, DataRequest.map, KeyData.map, ← lift'_comp] using origin
  · have fields := W.fields
    simpa only [RecordData.rename, RecordData.map, FamilyData.map,
      List.map_map, Function.comp_def, DataRequest.rename_comp, DataRequest.rename, DataRequest.map, KeyData.map,
      ← lift'_comp, ← Profile.rename_comp] using fields

theorem RankedData.ConstructorRelation.absorb
    {lower : Relations n} {Γ Δ : List VExpr} {ρ : Lift}
    {left right type : VExpr} {demand : ConstructorData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (I : ProofInsertion env U Γ Δ ρ)
    (H : RankedData.ConstructorRelation env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (demand.rename ρ)) :
    RankedData.ConstructorRelation env U registry lower Γ left right type demand := by
  intro Ω τ future
  obtain ⟨V, i, j, hi, hj, he⟩ := I.pushout future henv
  obtain ⟨W⟩ := H V j hj
  have typed : RankedData.ConstructorWitness env U registry lower V
      ((left.lift' τ).lift' i) ((right.lift' τ).lift' i) ((type.lift' τ).lift' i)
      ((demand.rename τ).rename i) := by
    simpa only [← lift'_comp, ConstructorData.rename_comp, he] using W
  exact typed.absorb henv hscoped hi

theorem RankedData.RecordRelation.absorb
    {lower : Relations n} {Γ Δ : List VExpr} {ρ : Lift}
    {left right type : VExpr} {demand : RecordData (Profile n)}
    (henv : env.Ordered)
    (I : ProofInsertion env U Γ Δ ρ)
    (H : RankedData.RecordRelation env U registry lower Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (demand.rename ρ)) :
    RankedData.RecordRelation env U registry lower Γ left right type demand := by
  intro Ω τ future
  obtain ⟨V, i, j, hi, hj, he⟩ := I.pushout future henv
  obtain ⟨W⟩ := H V j hj
  have typed : RankedData.RecordWitness env U registry lower V
      ((left.lift' τ).lift' i) ((right.lift' τ).lift' i) ((type.lift' τ).lift' i)
      ((demand.rename τ).rename i) := by
    simpa only [← lift'_comp, RecordData.rename_comp, he] using W
  exact typed.absorb hi

theorem Related.constructorRelation
    {Γ : List VExpr} {left right type : VExpr} {demand : ConstructorData (Profile n)}
    {support : Profile (n + 1)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right type
      (Profile.singleton (n := n + 1) (.ctor demand)) support) :
    RankedData.ConstructorRelation env U registry (relations env U registry n) Γ left right type demand := by
  have chosen := related (.ctor demand) (List.mem_singleton_self _) Γ .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at chosen
  rcases chosen with empty | ⟨Δ, ρ, insertion, _, _, values⟩
  · cases empty
  have value := values (Atom.rename ρ (.ctor demand)) (List.mem_singleton_self _)
  exact RankedData.ConstructorRelation.absorb henv hscoped insertion value

theorem Related.recordRelation
    {Γ : List VExpr} {left right type : VExpr} {demand : RecordData (Profile n)}
    {support : Profile (n + 1)}
    (henv : env.Ordered) (_hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right type
      (Profile.singleton (n := n + 1) (.record demand)) support) :
    RankedData.RecordRelation env U registry (relations env U registry n) Γ left right type demand := by
  have chosen := related (.record demand) (List.mem_singleton_self _) Γ .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at chosen
  rcases chosen with empty | ⟨Δ, ρ, insertion, _, _, values⟩
  · cases empty
  have value := values (Atom.rename ρ (.record demand)) (List.mem_singleton_self _)
  exact RankedData.RecordRelation.absorb henv insertion value

end Lean4Lean.AnchoredSemantics
