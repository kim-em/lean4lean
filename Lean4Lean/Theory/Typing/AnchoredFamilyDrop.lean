import Lean4Lean.Theory.Typing.AnchoredDataDropFrame
import Lean4Lean.Theory.Typing.CanonicalDataHeadProjection

/-! Family proof contraction retains actual inert declaration heads and
contracts only fixed, protected lower-rank request supports. -/
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

theorem FamilyWitness.drop (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : LowerDrop env U registry n)
    {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ F.liftMap)
    {left right : VExpr} {demand : FamilyData (Profile n)}
    (W : FamilyWitness env U registry (relations env U registry n) Δ left right (demand.rename F.liftMap)) :
    Nonempty (FamilyWitness env U registry (relations env U registry n) Γ
      (left.subst F.retract) (right.subst F.retract) demand) := by
  have total : ProofInsertion env U Δ W.leftExposure.postContext W.map := by
    simpa only [W.leftExposure.map_eq] using W.leftExposure.generated.comp W.leftExposure.post henv
  obtain ⟨D⟩ := DataDropFrame.ofPost henv F sectionProof total W.leftExposure.terminal
  let back := proofReadback W.map F.retract
  let skip : Lift := .skipN .refl (proofCount W.map)
  obtain ⟨el⟩ := W.leftExposure.projectCanonical henv hscoped F.baseWF F.typed
  obtain ⟨er⟩ := W.rightExposure.projectCanonical henv hscoped F.baseWF F.typed
  refine ⟨{
    registryScoped := W.registryScoped, headInert := W.headInert
    context := replayContext Γ W.context W.map F.retract, map := skip
    leftLevel := W.leftLevel, rightLevel := W.rightLevel
    leftRelevance := W.leftRelevance, rightRelevance := W.rightRelevance
    path := ?_
    leftLevels := W.leftLevels, rightLevels := W.rightLevels
    leftArguments := W.leftArguments.map (·.subst back)
    rightArguments := W.rightArguments.map (·.subst back)
    leftType := ?_, rightType := ?_
    leftExposure := by simpa only [head_subst, FamilyData.rename, FamilyData.map, subst, back, skip] using el
    rightExposure := by simpa only [head_subst, FamilyData.rename, FamilyData.map, subst, back, skip] using er
    leftTerminal := W.headInert.step _ _, rightTerminal := W.headInert.step _ _
    leftUniverses := W.leftUniverses, rightUniverses := W.rightUniverses
    arguments := ?_ }⟩
  · simpa only [proofReadback_commute] using W.path.substTarget henv D.formed D.typed
  · simpa only [head_subst, FamilyData.rename, FamilyData.map, subst, back, skip] using W.leftType.subst henv D.typed D.formed
  · simpa only [head_subst, FamilyData.rename, FamilyData.map, subst, back, skip] using W.rightType.subst henv D.typed D.formed
  · have args := W.arguments
    change Arguments env U (relations env U registry n) W.context
      ((demand.arguments.map (DataRequest.rename F.liftMap)).map (DataRequest.rename W.map))
      W.leftArguments W.rightArguments at args
    apply D.arguments henv lower
    simpa only [List.map_map, Function.comp_def, DataRequest.rename_comp] using args

theorem FamilyRelation.drop (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : LowerDrop env U registry n)
    {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ F.liftMap)
    {left right : VExpr} {demand : FamilyData (Profile n)}
    (H : FamilyRelation env U registry (relations env U registry n) Δ left right (demand.rename F.liftMap)) :
    FamilyRelation env U registry (relations env U registry n) Γ
      (left.subst F.retract) (right.subst F.retract) demand := by
  intro V τ future
  obtain ⟨W, i, j, proof, largerFuture, square, next, nextMap, nextRetract⟩ :=
    F.pushoutChosen sectionProof future henv
  subst i
  obtain ⟨old⟩ := H W j largerFuture
  have old' : FamilyWitness env U registry (relations env U registry n) W
      (left.lift' j) (right.lift' j) ((demand.rename τ).rename next.liftMap) := by
    simpa only [FamilyData.rename_comp, square] using old
  obtain ⟨result⟩ := old'.drop henv hscoped lower next proof
  have commute (e : VExpr) : (e.lift' j).subst next.retract = (e.subst F.retract).lift' τ := by
    rw [subst_lift', nextRetract, lift'_subst]
  exact ⟨by simpa only [commute] using result⟩

/-- A displayed family bridge contracts through the same replay frame as
its constructor or record, retaining its exact frozen demand. -/
theorem DataDropFrame.family (henv : env.Ordered) (hscoped : registry.Scoped)
    (lower : LowerDrop env U registry n)
    {F : SplitTypedEmbedding env U Γ Δ} (D : DataDropFrame env U F Ω map)
    {demand : FamilyData (Profile n)} {left right : VExpr}
    (H : FamilyRelation env U registry (relations env U registry n) Ω left right
      (demand.rename (F.liftMap.comp map))) :
    FamilyRelation env U registry (relations env U registry n)
      (replayContext Γ Ω map F.retract)
      (left.subst (proofReadback map F.retract))
      (right.subst (proofReadback map F.retract))
      (demand.rename (.skipN .refl (proofCount map))) := by
  have renamedRefl (d : FamilyData (Profile n)) : d.rename .refl = d := by
    unfold FamilyData.rename
    rw [show (fun e : VExpr => e.lift' .refl) = id from funext (fun _ => lift'_refl),
      show Profile.rename (n := n) .refl = id from funext Profile.rename_refl, FamilyData.map_id]
  have moved := H.future henv D.post
  have changed := moved.mixed henv (.context D.changed)
  have fixed : FamilyRelation env U registry (relations env U registry n) D.commonWorld
      (left.lift' D.postMap) (right.lift' D.postMap)
      ((demand.rename (.skipN .refl (proofCount map))).rename D.frame.liftMap) := by
    simpa only [lift'_refl, renamedRefl, FamilyData.rename_comp,
      Lift.comp_assoc, D.square] using changed
  have dropped := fixed.drop henv hscoped lower D.frame D.sectionProof
  simpa only [D.read] using dropped

end Lean4Lean.AnchoredSemantics.RankedData
