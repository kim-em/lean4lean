import Lean4Lean.Theory.Typing.AnchoredProofDropRawProjection
import Lean4Lean.Theory.Typing.AnchoredProofDropFuture
import Lean4Lean.Theory.Typing.TypedWorldProofSubstitutionExact

/-! The actual paired display producer for protected-profile contraction.
Both exposures use the same canonical readback. The old semantic display
moves only forward before a terminal context conversion and the chosen
proof retraction; no component equality is supplied as an external premise. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem PiWitness.dropProjection
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ F.liftMap)
    {left right A B : VExpr} {domain : Profile n} {rows : List (Key n × Profile n)}
    (W : PiWitness env U registry (relations env U registry n)
      Δ left right (A.lift' F.liftMap) (B.lift' F.liftMap.cons)
      (domain.rename F.liftMap) (Rows.rename F.liftMap rows)) :
    Nonempty (ProofDropPiProjection env U registry F W) := by
  let small := W.dropRaw henv hscoped F
  have total : ProofInsertion env U Δ W.leftExposure.postContext W.map := by
    simpa only [W.leftExposure.map_eq] using
      W.leftExposure.generated.comp W.leftExposure.post henv
  have changed := W.leftExposure.terminal.replayContext henv total F.baseWF F.typed
  obtain ⟨_, readback, _⟩ := total.mapSubstitution_exact henv F.baseWF F.typed
  have typed := readback.targetChain henv changed
  have smallFrame := W.leftExposure.terminal.replayFuture henv total F.baseWF F.typed
  obtain ⟨common, j, previous, G, proof, restrict, square⟩ :=
    F.extendProofWith sectionProof total henv smallFrame
      (proofReadback W.map F.retract) typed (proofReadback_commute W.map F.retract)
  obtain ⟨postWorld, post, terminal⟩ := W.leftExposure.terminal.pushFuture henv previous
  have domains (e : VExpr) : (e.lift' j).subst G.retract =
      e.subst (proofReadback W.map F.retract) := by
    rw [subst_lift', restrict]
  have bodies (e : VExpr) : (e.lift' j.cons).subst G.retract.lift =
      e.subst (proofReadback W.map F.retract).lift := by
    rw [subst_lift', ← Subst.lift_l_lift, restrict]
  let base : ProofDropPiFrame env U registry F.liftMap small W := {
    postWorld := postWorld
    postMap := j
    post := post
    largeWorld := common
    changed := terminal.symm henv
    frame := G
    insertion := proof
    square := by
      change F.liftMap.comp (W.map.comp j) =
        (Lift.skipN .refl (proofCount W.map)).comp G.liftMap
      simpa only [Lift.comp_assoc] using square
    leftDomain := domains W.leftDomain
    rightDomain := domains W.rightDomain }
  apply Nonempty.intro
  apply ProofDropPiProjection.ofFrame henv small base
  · intro e
    change (e.lift' (W.map.comp j)).subst G.retract =
      (e.subst F.retract).lift' (Lift.skipN .refl (proofCount W.map))
    rw [lift'_comp, domains, proofReadback_commute]
  · exact bodies W.leftBody
  · exact bodies W.rightBody

end Lean4Lean.AnchoredSemantics
