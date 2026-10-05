import Lean4Lean.Theory.Typing.AnchoredFamilyDrop

/-! Constructor proof contraction preserves the actual declaration-derived
result headers and contracts both bridges at their frozen family demand. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem head_subst (name : Name) (levels : List VLevel) (arguments : List VExpr) (σ : Subst) :
    (mkApps (.const name levels) arguments).subst σ =
      mkApps (.const name levels) (arguments.map (·.subst σ)) := by
  suffices ∀ head, (mkApps head arguments).subst σ =
      mkApps (head.subst σ) (arguments.map (·.subst σ)) from this _
  induction arguments with
  | nil => intro head; rfl
  | cons arg rest ih => intro head; exact ih (.app head arg)

theorem ConstructorWitness.drop (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : LowerDrop env U registry n)
    {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ F.liftMap)
    {left right type : VExpr} {demand : ConstructorData (Profile n)}
    (W : ConstructorWitness env U registry (relations env U registry n) Δ left right type
      (demand.rename F.liftMap)) :
    Nonempty (ConstructorWitness env U registry (relations env U registry n) Γ
      (left.subst F.retract) (right.subst F.retract) (type.subst F.retract) demand) := by
  obtain ⟨D⟩ := DataDropFrame.ofMixed henv F sectionProof W.leftExposure.route
  let back := proofReadback W.map F.retract
  let skip : Lift := .skipN .refl (proofCount W.map)
  refine ⟨{
    headInert := W.headInert
    context := replayContext Γ W.context W.map F.retract, map := skip
    leftLevels := W.leftLevels, rightLevels := W.rightLevels
    leftArguments := W.leftArguments.map (·.subst back)
    rightArguments := W.rightArguments.map (·.subst back)
    leftExposure := {
      baseWF := F.baseWF
      route := D.insertion
      origin := by
        simpa only [head_subst, ConstructorData.rename, ConstructorData.map,
          back, skip, proofReadback_commute] using
          ConstructorOrigin.substitute D.formed D.typed W.leftExposure.origin
      sound := by
        simpa only [head_subst, ConstructorData.rename, ConstructorData.map,
          back, skip, proofReadback_commute] using W.leftExposure.sound.subst henv D.typed D.formed }
    rightExposure := {
      baseWF := F.baseWF
      route := D.insertion
      origin := by
        simpa only [head_subst, ConstructorData.rename, ConstructorData.map,
          back, skip, proofReadback_commute] using
          ConstructorOrigin.substitute D.formed D.typed W.rightExposure.origin
      sound := by
        simpa only [head_subst, ConstructorData.rename, ConstructorData.map,
          back, skip, proofReadback_commute] using W.rightExposure.sound.subst henv D.typed D.formed }
    leftTerminal := W.headInert.step _ _, rightTerminal := W.headInert.step _ _
    leftUniverses := W.leftUniverses, rightUniverses := W.rightUniverses
    arguments := ?_
    leftHeader := by simpa only [ConstructorData.rename, ConstructorData.map, FamilyData.map] using
      W.leftHeader.substitute back
    rightHeader := by simpa only [ConstructorData.rename, ConstructorData.map, FamilyData.map] using
      W.rightHeader.substitute back
    leftBridge := ?_, rightBridge := ?_ }⟩
  · have args := W.arguments
    change Arguments env U (relations env U registry n) W.context
      ((demand.arguments.map (DataRequest.rename F.liftMap)).map (DataRequest.rename W.map))
      W.leftArguments W.rightArguments at args
    apply D.arguments henv lower
    simpa only [List.map_map, Function.comp_def, DataRequest.rename_comp] using args
  · have bridge := W.leftBridge
    change FamilyRelation env U registry (relations env U registry n) W.context W.leftHeader.result
      (type.lift' W.map) ((demand.family.rename F.liftMap).rename W.map) at bridge
    rw [FamilyData.rename_comp] at bridge
    simpa only [id_eq, ConstructorResultHeader.result_substitute henv, back, skip, proofReadback_commute] using
      D.family henv hscoped lower bridge
  · have bridge := W.rightBridge
    change FamilyRelation env U registry (relations env U registry n) W.context W.rightHeader.result
      (type.lift' W.map) ((demand.family.rename F.liftMap).rename W.map) at bridge
    rw [FamilyData.rename_comp] at bridge
    simpa only [id_eq, ConstructorResultHeader.result_substitute henv, back, skip, proofReadback_commute] using
      D.family henv hscoped lower bridge

theorem ConstructorRelation.drop (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : LowerDrop env U registry n)
    {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ F.liftMap)
    {left right type : VExpr} {demand : ConstructorData (Profile n)}
    (H : ConstructorRelation env U registry (relations env U registry n) Δ left right type
      (demand.rename F.liftMap)) :
    ConstructorRelation env U registry (relations env U registry n) Γ
      (left.subst F.retract) (right.subst F.retract) (type.subst F.retract) demand := by
  intro V τ future
  obtain ⟨W, i, j, proof, largerFuture, square, next, nextMap, nextRetract⟩ :=
    F.pushoutChosen sectionProof future henv
  subst i
  obtain ⟨old⟩ := H W j largerFuture
  have old' : ConstructorWitness env U registry (relations env U registry n) W
      (left.lift' j) (right.lift' j) (type.lift' j) ((demand.rename τ).rename next.liftMap) := by
    simpa only [ConstructorData.rename_comp, square] using old
  obtain ⟨result⟩ := old'.drop henv hscoped lower next proof
  have commute (e : VExpr) : (e.lift' j).subst next.retract = (e.subst F.retract).lift' τ := by
    rw [subst_lift', nextRetract, lift'_subst]
  exact ⟨by simpa only [commute] using result⟩

end Lean4Lean.AnchoredSemantics.RankedData
