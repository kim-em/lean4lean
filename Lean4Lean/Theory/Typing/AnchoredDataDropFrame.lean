import Lean4Lean.Theory.Typing.AnchoredDataProjection
import Lean4Lean.Theory.Typing.AnchoredDataLaws
import Lean4Lean.Theory.Typing.AnchoredMixedTransport

/-! Concrete proof retractions for data displays. The only semantic inputs
are contraction at the already constructed preceding observation rank. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

structure LowerDrop (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (n : Nat) : Prop where
  code : ∀ {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ),
    ProofInsertion env U Γ Δ F.liftMap → ∀ {left right : VExpr} {profile : Profile n},
    TypeRelated env U registry Δ left right (profile.rename F.liftMap) →
    TypeRelated env U registry Γ (left.subst F.retract) (right.subst F.retract) profile
  term : ∀ {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ),
    ProofInsertion env U Γ Δ F.liftMap → ∀ {left right type : VExpr} {value support : Profile n},
    Related env U registry Δ left right type (value.rename F.liftMap) (support.rename F.liftMap) →
    Related env U registry Γ (left.subst F.retract) (right.subst F.retract)
      (type.subst F.retract) value support

structure DataDropFrame (env : VEnv) (U : Nat) {Γ Δ : List VExpr}
    (initial : SplitTypedEmbedding env U Γ Δ) (oldContext : List VExpr) (map : Lift) where
  insertion : MixedInsertion env U Γ (replayContext Γ oldContext map initial.retract)
    (.skipN .refl (proofCount map))
  formed : OnCtx (replayContext Γ oldContext map initial.retract) (env.IsType U)
  typed : Ctx.SubstEq env U (replayContext Γ oldContext map initial.retract)
    (proofReadback map initial.retract) (proofReadback map initial.retract) oldContext
  postWorld : List VExpr
  postMap : Lift
  post : FutureInsertion env U oldContext postWorld postMap
  commonWorld : List VExpr
  changed : ContextChain env U postWorld commonWorld
  frame : SplitTypedEmbedding env U (replayContext Γ oldContext map initial.retract) commonWorld
  sectionProof : ProofInsertion env U (replayContext Γ oldContext map initial.retract) commonWorld frame.liftMap
  square : initial.liftMap.comp (map.comp postMap) =
    (Lift.skipN .refl (proofCount map)).comp frame.liftMap
  readback : Subst.lift_l postMap frame.retract = proofReadback map initial.retract

theorem DataDropFrame.ofPost (henv : env.Ordered)
    {Γ Δ Ω Ξ : List VExpr} {map : Lift}
    (initial : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ initial.liftMap)
    (post : ProofInsertion env U Δ Ω map) (terminal : ContextChain env U Ω Ξ) :
    Nonempty (DataDropFrame env U initial Ξ map) := by
  obtain ⟨small, readback, _⟩ := post.mapSubstitution_exact henv initial.baseWF initial.typed
  have changed := terminal.replayContext henv post initial.baseWF initial.typed
  have typed := readback.targetChain henv changed
  have smallFrame := terminal.replayFuture henv post initial.baseWF initial.typed
  obtain ⟨common, j, previous, G, proof, restrict, square⟩ :=
    initial.extendProofWith sectionProof post henv smallFrame
      (proofReadback map initial.retract) typed (proofReadback_commute map initial.retract)
  obtain ⟨postWorld, next, terminal'⟩ := terminal.pushFuture henv previous
  exact ⟨{
    insertion := by simpa only [Lift.comp] using
      MixedInsertion.comp (.proof small) (.context changed)
    formed := changed.targetWF henv (small.targetWF henv)
    typed := terminal.replayTyped henv post initial.baseWF initial.typed
    postWorld := postWorld, postMap := j, post := next
    commonWorld := common, changed := terminal'.symm henv
    frame := G, sectionProof := proof
    square := by simpa only [Lift.comp_assoc] using square
    readback := restrict }⟩

private theorem normalizeRoute (henv : env.Ordered) (route : MixedInsertion env U Γ Δ ρ)
    (formed : OnCtx Γ (env.IsType U)) :
    ∃ Ω, ProofInsertion env U Γ Ω ρ ∧ ContextChain env U Ω Δ := by
  induction route with
  | proof insertion => exact ⟨_, insertion, .refl⟩
  | context chain => exact ⟨_, .refl formed, chain⟩
  | comp before after first second =>
    obtain ⟨Ω, initial, changed⟩ := first formed
    obtain ⟨V, suffix, final⟩ := second (before.targetWF henv formed)
    obtain ⟨W, suffix', changed'⟩ := changed.pullProof henv suffix
    exact ⟨W, initial.comp suffix' henv, changed'.trans final⟩

theorem DataDropFrame.ofMixed (henv : env.Ordered)
    {Γ Δ Ω : List VExpr} {map : Lift}
    (initial : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ initial.liftMap)
    (post : MixedInsertion env U Δ Ω map) : Nonempty (DataDropFrame env U initial Ω map) := by
  obtain ⟨pre, proof, terminal⟩ := normalizeRoute henv post (sectionProof.targetWF henv)
  exact ofPost henv initial sectionProof proof terminal

theorem DataDropFrame.read (D : DataDropFrame env U initial Ω map) (e : VExpr) :
    (e.lift' D.postMap).subst D.frame.retract = e.subst (proofReadback map initial.retract) := by
  rw [subst_lift', D.readback]

theorem RequestAdmission.drop (henv : env.Ordered) (lower : LowerDrop env U registry n)
    {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ F.liftMap)
    {request : DataRequest (Profile n)} {left right : VExpr}
    (H : RequestAdmission env U (relations env U registry n) Δ (request.rename F.liftMap) left right) :
    RequestAdmission env U (relations env U registry n) Γ request
      (left.subst F.retract) (right.subst F.retract) := by
  obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := H
  have anchor := anchor.subst henv F.typed F.baseWF
  have pair := pair.subst henv F.typed F.baseWF
  have code := lower.code F sectionProof code
  have first := lower.term F sectionProof first
  have last := lower.term F sectionProof last
  exact ⟨by simpa only [DataRequest.rename, DataRequest.map, KeyData.map, F.leftInv] using anchor,
    by simpa only [DataRequest.rename, DataRequest.map, KeyData.map, F.leftInv] using pair,
    Profile.rename_hasType_iff.mp typed,
    Profile.rename_hasType_iff.mp (by simpa only [DataRequest.rename, DataRequest.map, Profile.rename_sort] using formed),
    by simpa only [TypeRelated, DataRequest.rename, DataRequest.map, KeyData.map, F.leftInv] using code,
    by simpa only [Related, DataRequest.rename, DataRequest.map, KeyData.map, F.leftInv] using first,
    by simpa only [Related, DataRequest.rename, DataRequest.map, KeyData.map, F.leftInv] using last⟩

theorem Arguments.drop (henv : env.Ordered) (lower : LowerDrop env U registry n)
    {Γ Δ : List VExpr} (F : SplitTypedEmbedding env U Γ Δ)
    (sectionProof : ProofInsertion env U Γ Δ F.liftMap)
    {requests : List (DataRequest (Profile n))} {left right : List VExpr}
    (H : Arguments env U (relations env U registry n) Δ (requests.map (DataRequest.rename F.liftMap)) left right) :
    Arguments env U (relations env U registry n) Γ requests
      (left.map (·.subst F.retract)) (right.map (·.subst F.retract)) := by
  induction requests generalizing left right with
  | nil => cases H; exact .nil
  | cons request rest ih =>
    cases H with
    | cons head tail => exact .cons (head.drop henv lower F sectionProof) (ih tail)

theorem RequestAdmission.future (henv : env.Ordered)
    {request : DataRequest (Profile n)}
    (future : FutureInsertion env U Γ Δ ρ)
    (H : RequestAdmission env U (relations env U registry n) Γ request left right) :
    RequestAdmission env U (relations env U registry n) Δ (request.rename ρ)
      (left.lift' ρ) (right.lift' ρ) := by
  obtain ⟨anchor, pair, typed, formed, code, first, last⟩ := H
  exact ⟨anchor.weak' henv future.weakening, pair.weak' henv future.weakening,
    Profile.rename_hasType_iff.mpr typed,
    by simpa only [DataRequest.rename, DataRequest.map, Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := ρ)).mpr formed,
    TypeRelated.future henv future code, Related.future henv future first, Related.future henv future last⟩

theorem Arguments.future (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    (H : Arguments env U (relations env U registry n) Γ requests left right) :
    Arguments env U (relations env U registry n) Δ (requests.map (DataRequest.rename ρ))
      (left.map (·.lift' ρ)) (right.map (·.lift' ρ)) := by
  induction H with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.future henv future) ih

theorem DataDropFrame.arguments (henv : env.Ordered) (lower : LowerDrop env U registry n)
    {F : SplitTypedEmbedding env U Γ Δ} (D : DataDropFrame env U F Ω map)
    {requests : List (DataRequest (Profile n))} {left right : List VExpr}
    (H : Arguments env U (relations env U registry n) Ω
      (requests.map (DataRequest.rename (F.liftMap.comp map))) left right) :
    Arguments env U (relations env U registry n) (replayContext Γ Ω map F.retract)
      (requests.map (DataRequest.rename (.skipN .refl (proofCount map))))
      (left.map (·.subst (proofReadback map F.retract)))
      (right.map (·.subst (proofReadback map F.retract))) := by
  have moved := H.future henv D.post
  have laws : LowerTransport env U (relations env U registry n) :=
    ⟨fun route h => route.code henv h, fun route h => route.term henv h⟩
  have changed := moved.transport henv laws (.context D.changed)
  simp only [DataRequest.rename_refl, lift'_refl, List.map_id] at changed
  have guarded : Arguments env U (relations env U registry n) D.commonWorld
      ((requests.map (DataRequest.rename (.skipN .refl (proofCount map)))).map
        (DataRequest.rename D.frame.liftMap))
      (left.map (·.lift' D.postMap)) (right.map (·.lift' D.postMap)) := by
    simpa only [List.map_map, Function.comp_def, DataRequest.rename_comp,
      Lift.comp_assoc, D.square, Lift.comp] using changed
  have dropped := guarded.drop henv lower D.frame D.sectionProof
  simpa only [List.map_map, Function.comp_def, D.read] using dropped

end Lean4Lean.AnchoredSemantics.RankedData
