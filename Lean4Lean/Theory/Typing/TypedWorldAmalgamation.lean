import Lean4Lean.Theory.Typing.TypedWorld

/-! The universal property of the concrete proof/future insertion pushout.
Keeping the chosen substitution, rather than choosing fresh proof witnesses,
is necessary when a semantic retraction identifies particular proof slots. -/
namespace Lean4Lean.VEnv
open VExpr
set_option backward.isDefEq.respectTransparency false

structure InsertionAmalgam (env : VEnv) (U : Nat) (Γ Δ V : List VExpr)
    (ρ τ : Lift) where
  context : List VExpr
  leftMap : Lift
  rightMap : Lift
  proof : ProofInsertion env U V context leftMap
  future : FutureInsertion env U Δ context rightMap
  commute : ρ.comp rightMap = τ.comp leftMap
  merge : ∀ a b : Subst, Subst.lift_l ρ a = Subst.lift_l τ b →
    ∃ c : Subst, Subst.lift_l rightMap c = a ∧ Subst.lift_l leftMap c = b
  typing : ∀ {target : List VExpr} {a b : Subst},
    Ctx.SubstEq env U target (Subst.lift_l rightMap a) (Subst.lift_l rightMap b) Δ →
    Ctx.SubstEq env U target (Subst.lift_l leftMap a) (Subst.lift_l leftMap b) V →
    Ctx.SubstEq env U target a b context
  ext : ∀ {a b : Subst}, Subst.lift_l rightMap a = Subst.lift_l rightMap b →
    Subst.lift_l leftMap a = Subst.lift_l leftMap b → a = b

private theorem subst_ext {σ τ : Subst} (head : σ.head = τ.head)
    (tail : σ.tail = τ.tail) : σ = τ := by
  funext i
  cases i with
  | zero => exact head
  | succ i => exact congrFun tail i

private theorem lift_l_cons_head (ρ : Lift) (σ : Subst) :
    (Subst.lift_l ρ.cons σ).head = σ.head := rfl
private theorem lift_l_cons_tail (ρ : Lift) (σ : Subst) :
    (Subst.lift_l ρ.cons σ).tail = Subst.lift_l ρ σ.tail := rfl

/-- Both substituted typings and literal substitutions amalgamate along the
same concrete insertion history. -/
theorem ProofInsertion.amalgam (H : ProofInsertion env U Γ Δ ρ)
    (K : FutureInsertion env U Γ V τ) (henv : env.Ordered) :
    Nonempty (InsertionAmalgam env U Γ Δ V ρ τ) := by
  generalize heq : ρ.size + τ.size = n
  induction n using Nat.strongRecOn generalizing Γ Δ V ρ τ with
  | ind n ih =>
    cases H with
    | refl hΓ =>
      refine ⟨⟨V, .refl, τ, .refl (K.targetWF henv), K, by simp, ?_, ?_, ?_⟩⟩
      · intro a b equal
        exact ⟨b, equal.symm, rfl⟩
      · intro target a b _ typed
        exact typed
      · intro a b _ equal
        exact equal
    | @skip Γ Δ ρ P q H hP hq =>
      obtain ⟨F⟩ := ih _ (by simp_all only [Lift.size]; omega) H K rfl
      refine ⟨⟨P.lift' F.rightMap :: F.context, F.leftMap.skip, F.rightMap.cons,
        F.proof.skip (hP.weak' henv F.future.weakening) (hq.weak' henv F.future.weakening),
        F.future.cons hP, ?_, ?_, ?_, ?_⟩⟩
      · simpa only [Lift.comp] using congrArg Lift.skip F.commute
      · intro a b equal
        obtain ⟨c, hc, hd⟩ := F.merge a.tail b equal
        refine ⟨c.cons a.head, ?_, ?_⟩
        · apply subst_ext
          · rfl
          · exact hc
        · exact hd
      · intro target a b left right
        cases left with
        | cons tail formed head =>
          refine .cons (F.typing tail right) (hP.weak' henv F.future.weakening) ?_
          simpa only [subst_lift', lift_l_cons_head, lift_l_cons_tail] using head
      · intro a b left right
        apply subst_ext
        · simpa only [lift_l_cons_head] using congrArg Subst.head left
        · apply F.ext
          · exact congrArg Subst.tail left
          · exact right
    | @cons Γ Δ ρ A u H hA =>
      cases K with
      | refl hΓ =>
        refine ⟨⟨A.lift' ρ :: Δ, ρ.cons, .refl, H.cons hA,
          .refl ((H.cons hA).targetWF henv), by simp, ?_, ?_, ?_⟩⟩
        · intro a b equal
          exact ⟨a, rfl, equal⟩
        · intro target a b typed _
          exact typed
        · intro a b equal _
          exact equal
      | @skip _ V τ B v K hB =>
        obtain ⟨F⟩ := ih _ (by simp_all only [Lift.size]; omega) (H.cons hA) K rfl
        refine ⟨⟨B.lift' F.leftMap :: F.context, F.leftMap.cons, F.rightMap.skip,
          F.proof.cons hB, F.future.skip (hB.weak' henv F.proof.weakening),
          ?_, ?_, ?_, ?_⟩⟩
        · simpa only [Lift.comp] using congrArg Lift.skip F.commute
        · intro a b equal
          obtain ⟨c, hc, hd⟩ := F.merge a b.tail equal
          refine ⟨c.cons b.head, hc, ?_⟩
          apply subst_ext
          · rfl
          · exact hd
        · intro target a b left right
          cases right with
          | cons tail formed head =>
            refine .cons (F.typing left tail) (hB.weak' henv F.proof.weakening) ?_
            simpa only [subst_lift', lift_l_cons_head, lift_l_cons_tail] using head
        · intro a b left right
          apply subst_ext
          · simpa only [lift_l_cons_head] using congrArg Subst.head right
          · apply F.ext (a := a.tail) (b := b.tail) left
            exact congrArg Subst.tail right
      | @cons _ V τ _ v K hA' =>
        obtain ⟨F⟩ := ih _ (by simp_all only [Lift.size]; omega) H K rfl
        have hdomain : (A.lift' ρ).lift' F.rightMap = (A.lift' τ).lift' F.leftMap := by
          simpa only [← lift'_comp] using congrArg (A.lift' ·) F.commute
        refine ⟨⟨(A.lift' ρ).lift' F.rightMap :: F.context,
          F.leftMap.cons, F.rightMap.cons, ?_,
          F.future.cons (hA.weak' henv H.weakening), ?_, ?_, ?_, ?_⟩⟩
        · rw [hdomain]
          exact F.proof.cons (hA'.weak' henv K.weakening)
        · simpa only [Lift.comp] using congrArg Lift.cons F.commute
        · intro a b equal
          have heads : a.head = b.head := by
            simpa only [lift_l_cons_head] using congrArg Subst.head equal
          have tails : Subst.lift_l ρ a.tail = Subst.lift_l τ b.tail :=
            congrArg Subst.tail equal
          obtain ⟨c, hc, hd⟩ := F.merge a.tail b.tail tails
          refine ⟨c.cons a.head, ?_, ?_⟩
          · exact subst_ext rfl hc
          · exact subst_ext heads hd
        · intro target a b left right
          cases left with
          | cons leftTail formed head =>
            cases right with
            | cons rightTail _ _ =>
              refine .cons (F.typing leftTail rightTail)
                ((hA.weak' henv H.weakening).weak' henv F.future.weakening) ?_
              simpa only [subst_lift', lift_l_cons_head, lift_l_cons_tail] using head
        · intro a b left right
          apply subst_ext
          · simpa only [lift_l_cons_head] using congrArg Subst.head left
          · exact F.ext (congrArg Subst.tail left) (congrArg Subst.tail right)

private theorem lift_l_lift_r (ρ τ : Lift) (σ : Subst) :
    Subst.lift_l ρ (σ.lift_r τ) = (Subst.lift_l ρ σ).lift_r τ := rfl

private theorem lift_r_comp (σ : Subst) (ρ τ : Lift) :
    (σ.lift_r ρ).lift_r τ = σ.lift_r (ρ.comp τ) := by
  funext i
  exact lift'_comp.symm

/-- Future transport preserves the specified retraction on every old term.
In particular this does not replace the chosen proof-slot identification with
the witnesses stored in the insertion history. -/
theorem SplitTypedEmbedding.pushoutChosen
    (F : SplitTypedEmbedding env U Γ Δ)
    (H : ProofInsertion env U Γ Δ F.liftMap)
    (K : FutureInsertion env U Γ V τ) (henv : env.Ordered) :
    ∃ Ω i j, ProofInsertion env U V Ω i ∧ FutureInsertion env U Δ Ω j ∧
      F.liftMap.comp j = τ.comp i ∧
      ∃ G : SplitTypedEmbedding env U V Ω,
        G.liftMap = i ∧ Subst.lift_l j G.retract = F.retract.lift_r τ := by
  obtain ⟨M⟩ := H.amalgam K henv
  have agree : Subst.lift_l F.liftMap (F.retract.lift_r τ) =
      Subst.lift_l τ Subst.id := by
    funext i
    have hi := F.leftInv (.bvar i)
    change F.retract (F.liftMap.liftVar i) = .bvar i at hi
    change (F.retract (F.liftMap.liftVar i)).lift' τ = .bvar (τ.liftVar i)
    rw [hi]
    rfl
  obtain ⟨σ, left, right⟩ := M.merge (F.retract.lift_r τ) Subst.id agree
  have typed : Ctx.SubstEq env U V σ σ M.context := by
    apply M.typing
    · rw [left]
      exact F.typed.weakenTarget henv K.weakening
    · rw [right]
      exact .id henv (K.targetWF henv)
  have reverse : Ctx.SubstEq env U M.context Subst.id (σ.lift_r M.leftMap) M.context := by
    apply M.typing
    · rw [lift_l_lift_r, left, lift_r_comp, ← M.commute, ← lift_r_comp]
      exact F.rightInv.weakenTarget henv M.future.weakening
    · rw [lift_l_lift_r, right]
      exact M.proof.typedRenaming henv
  let G : SplitTypedEmbedding env U V M.context := {
    liftMap := M.leftMap
    retract := σ
    weakening := M.proof.typedRenaming henv
    typed := typed
    leftInv := by intro e; rw [subst_lift', right, subst_id]
    rightInv := reverse }
  exact ⟨M.context, M.leftMap, M.rightMap, M.proof, M.future, M.commute,
    G, rfl, left⟩

end Lean4Lean.VEnv
