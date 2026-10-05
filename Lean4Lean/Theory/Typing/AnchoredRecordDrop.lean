import Lean4Lean.Theory.Typing.AnchoredFamilyDrop

/-! Record proof contraction retains finite projection origins and the
frozen support of every selected field. Private components are read back
through an actual typed proof retraction, never by context strengthening. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem RecordWitness.drop (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : LowerDrop env U registry n)
    {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ F.liftMap)
    {left right type : VExpr} {demand : RecordData (Profile n)}
    (W : RecordWitness env U registry (relations env U registry n) Δ left right type
      (demand.rename F.liftMap)) :
    Nonempty (RecordWitness env U registry (relations env U registry n) Γ
      (left.subst F.retract) (right.subst F.retract) (type.subst F.retract) demand) := by
  obtain ⟨D⟩ := DataDropFrame.ofMixed henv F sectionProof W.insertion
  let back := proofReadback W.map F.retract
  let skip : Lift := .skipN .refl (proofCount W.map)
  refine ⟨{
    baseWF := F.baseWF, context := replayContext Γ W.context W.map F.retract, map := skip
    insertion := D.insertion
    info := W.info, lookup := W.lookup
    ctorDefinition := W.ctorDefinition, ctorNative := W.ctorNative, ctorQuotient := W.ctorQuotient
    bounded := ?_, typeCode := ?_
    leftType := ?_, rightType := ?_
    leftOrigins := ?_, rightOrigins := ?_, fields := ?_ }⟩
  · intro entry member
    exact W.bounded (entry.1, entry.2.rename F.liftMap) (List.mem_map.mpr ⟨entry, member, rfl⟩)
  · have code := W.typeCode
    change FamilyRelation env U registry (relations env U registry n) W.context
      (type.lift' W.map) (type.lift' W.map)
      ((demand.family.rename F.liftMap).rename W.map) at code
    have code' : FamilyRelation env U registry (relations env U registry n) W.context
      (type.lift' W.map) (type.lift' W.map)
      (demand.family.rename (F.liftMap.comp W.map)) := by
      simpa only [FamilyData.rename_comp] using code
    simpa only [proofReadback_commute] using D.family henv hscoped lower code'
  · simpa only [proofReadback_commute] using W.leftType.subst henv D.typed D.formed
  · simpa only [proofReadback_commute] using W.rightType.subst henv D.typed D.formed
  · intro entry member
    obtain ⟨origin⟩ := W.leftOrigins (entry.1, entry.2.rename F.liftMap)
      (List.mem_map.mpr ⟨entry, member, rfl⟩)
    have dropped := origin.substitute henv D.formed D.typed
    exact ⟨by simpa only [RecordData.rename, RecordData.map, FamilyData.map, DataRequest.rename,
      DataRequest.map, KeyData.map, proofReadback_commute, F.leftInv] using dropped⟩
  · intro entry member
    obtain ⟨origin⟩ := W.rightOrigins (entry.1, entry.2.rename F.liftMap)
      (List.mem_map.mpr ⟨entry, member, rfl⟩)
    have dropped := origin.substitute henv D.formed D.typed
    exact ⟨by simpa only [RecordData.rename, RecordData.map, FamilyData.map, DataRequest.rename,
      DataRequest.map, KeyData.map, proofReadback_commute, F.leftInv] using dropped⟩
  · have args := W.fields
    have args' : Arguments env U (relations env U registry n) W.context
        ((demand.fields.map Prod.snd).map (DataRequest.rename (F.liftMap.comp W.map)))
        (demand.fields.map (fun entry => .proj demand.family.name entry.1 (left.lift' W.map)))
        (demand.fields.map (fun entry => .proj demand.family.name entry.1 (right.lift' W.map))) := by
      simpa only [RecordData.rename, RecordData.map, FamilyData.map, List.map_map,
        Function.comp_def, DataRequest.rename, DataRequest.map_map, ← lift'_comp,
        ← Profile.rename_comp] using args
    have dropped := D.arguments henv lower args'
    simpa only [List.map_map, Function.comp_def, subst, proofReadback_commute] using dropped

theorem RecordRelation.drop (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : LowerDrop env U registry n)
    {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ F.liftMap)
    {left right type : VExpr} {demand : RecordData (Profile n)}
    (H : RecordRelation env U registry (relations env U registry n) Δ left right type
      (demand.rename F.liftMap)) :
    RecordRelation env U registry (relations env U registry n) Γ
      (left.subst F.retract) (right.subst F.retract) (type.subst F.retract) demand := by
  intro V τ future
  obtain ⟨W, i, j, proof, largerFuture, square, next, nextMap, nextRetract⟩ :=
    F.pushoutChosen sectionProof future henv
  subst i
  obtain ⟨old⟩ := H W j largerFuture
  have old' : RecordWitness env U registry (relations env U registry n) W
      (left.lift' j) (right.lift' j) (type.lift' j) ((demand.rename τ).rename next.liftMap) := by
    simpa only [RecordData.rename_comp, square] using old
  obtain ⟨result⟩ := old'.drop henv hscoped lower next proof
  have commute (e : VExpr) : (e.lift' j).subst next.retract = (e.subst F.retract).lift' τ := by
    rw [subst_lift', nextRetract, lift'_subst]
  exact ⟨by simpa only [commute] using result⟩

end Lean4Lean.AnchoredSemantics.RankedData
