import Lean4Lean.Theory.Typing.SplitTypedEmbedding

/-! Generated context extensions for typed worlds. Proof insertions have
inhabited propositional domains and admit typed retractions. Future insertions
may introduce arbitrary well-formed domains. Both retain existing binders by
literal renaming; their pushout is constructed from these histories alone.
-/

namespace Lean4Lean.Lift

theorem comp_assoc (ρ τ υ : Lift) : (ρ.comp τ).comp υ = ρ.comp (τ.comp υ) := by
  induction υ generalizing ρ τ with
  | refl => rfl
  | skip υ ih => simp only [comp, ih]
  | cons υ ih =>
    cases τ with
    | refl => rfl
    | skip τ => simp only [comp, ih]
    | cons τ => cases ρ <;> simp only [comp, ih]

end Lean4Lean.Lift

namespace Lean4Lean.VEnv
open VExpr

inductive FutureInsertion (env : VEnv) (U : Nat) :
    List VExpr → List VExpr → Lift → Prop where
  | refl (hΓ : OnCtx Γ (env.IsType U)) : FutureInsertion env U Γ Γ .refl
  | skip (previous : FutureInsertion env U Γ Δ ρ)
      (hA : env.HasType U Δ A (.sort u)) : FutureInsertion env U Γ (A :: Δ) ρ.skip
  | cons (previous : FutureInsertion env U Γ Δ ρ)
      (hA : env.HasType U Γ A (.sort u)) :
      FutureInsertion env U (A :: Γ) (A.lift' ρ :: Δ) ρ.cons

inductive ProofInsertion (env : VEnv) (U : Nat) :
    List VExpr → List VExpr → Lift → Prop where
  | refl (hΓ : OnCtx Γ (env.IsType U)) : ProofInsertion env U Γ Γ .refl
  | skip (previous : ProofInsertion env U Γ Δ ρ)
      (hP : env.HasType U Δ P (.sort .zero)) (hq : env.HasType U Δ q P) :
      ProofInsertion env U Γ (P :: Δ) ρ.skip
  | cons (previous : ProofInsertion env U Γ Δ ρ)
      (hA : env.HasType U Γ A (.sort u)) :
      ProofInsertion env U (A :: Γ) (A.lift' ρ :: Δ) ρ.cons

variable {env : VEnv} {U : Nat} {Γ Δ V : List VExpr} {ρ τ : Lift}

theorem ProofInsertion.toFuture (H : ProofInsertion env U Γ Δ ρ) :
    FutureInsertion env U Γ Δ ρ := by
  induction H with
  | refl hΓ => exact .refl hΓ
  | skip _ hP _ ih => exact .skip ih hP
  | cons _ hA ih => exact .cons ih hA

theorem FutureInsertion.weakening (H : FutureInsertion env U Γ Δ ρ) :
    Ctx.Lift' ρ Γ Δ := by
  induction H with
  | refl => exact .refl
  | skip _ _ ih => exact .skip ih
  | cons _ _ ih => exact .cons ih

theorem FutureInsertion.baseWF (H : FutureInsertion env U Γ Δ ρ) :
    OnCtx Γ (env.IsType U) := by
  induction H with
  | refl hΓ => exact hΓ
  | skip _ _ ih => exact ih
  | cons _ hA ih => exact ⟨ih, _, hA⟩

theorem FutureInsertion.targetWF (H : FutureInsertion env U Γ Δ ρ)
    (henv : env.Ordered) : OnCtx Δ (env.IsType U) := by
  induction H with
  | refl hΓ => exact hΓ
  | skip _ hA ih => exact ⟨ih, _, hA⟩
  | cons previous hA ih => exact ⟨ih, _, hA.weak' henv previous.weakening⟩

theorem FutureInsertion.typedRenaming (H : FutureInsertion env U Γ Δ ρ)
    (henv : env.Ordered) :
    Ctx.SubstEq env U Δ (Subst.id.lift_r ρ) (Subst.id.lift_r ρ) Γ :=
  (Ctx.SubstEq.id henv H.baseWF).weakenTarget henv H.weakening

/-- Composition of generated future contexts preserves literal domains. -/
theorem FutureInsertion.comp (H : FutureInsertion env U Γ Δ ρ)
    (K : FutureInsertion env U Δ V τ) (henv : env.Ordered) :
    FutureInsertion env U Γ V (ρ.comp τ) := by
  induction K generalizing Γ ρ with
  | refl => exact H
  | skip _ hA ih => exact (ih H).skip hA
  | @cons Δ V τ A u K hA ih =>
    cases H with
    | refl => simpa only [Lift.refl_comp] using K.cons hA
    | skip H hB => exact (ih H).skip (hB.weak' henv K.weakening)
    | cons H hB => simpa only [Lift.comp, lift'_comp] using (ih H).cons hB

theorem ProofInsertion.weakening (H : ProofInsertion env U Γ Δ ρ) :
    Ctx.Lift' ρ Γ Δ := H.toFuture.weakening

theorem ProofInsertion.baseWF (H : ProofInsertion env U Γ Δ ρ) :
    OnCtx Γ (env.IsType U) := H.toFuture.baseWF

theorem ProofInsertion.targetWF (H : ProofInsertion env U Γ Δ ρ)
    (henv : env.Ordered) : OnCtx Δ (env.IsType U) := H.toFuture.targetWF henv

theorem ProofInsertion.typedRenaming (H : ProofInsertion env U Γ Δ ρ)
    (henv : env.Ordered) :
    Ctx.SubstEq env U Δ (Subst.id.lift_r ρ) (Subst.id.lift_r ρ) Γ :=
  H.toFuture.typedRenaming henv

/-- Composition retains the generated history, including witnesses for every
inserted proof after renaming through the second insertion. -/
theorem ProofInsertion.comp (H : ProofInsertion env U Γ Δ ρ)
    (K : ProofInsertion env U Δ V τ) (henv : env.Ordered) :
    ProofInsertion env U Γ V (ρ.comp τ) := by
  induction K generalizing Γ ρ with
  | refl => exact H
  | skip _ hP hq ih => exact (ih H).skip hP hq
  | @cons Δ V τ A u K hA ih =>
    cases H with
    | refl => simpa only [Lift.refl_comp] using K.cons hA
    | skip H hP hq =>
      exact (ih H).skip (hP.weak' henv K.weakening) (hq.weak' henv K.weakening)
    | cons H hB =>
      simpa only [Lift.comp, lift'_comp] using (ih H).cons hB

private theorem lift_skip (e : VExpr) (ρ : Lift) :
    e.lift' ρ.skip = (e.lift' ρ).lift := by
  rw [lift_eq_lift', ← lift'_comp]
  rfl

/-- Every generated proof insertion has a split typed embedding with exactly
its prescribed renaming. The existential avoids choosing retractions from a
propositional history. -/
theorem ProofInsertion.toEmbedding (H : ProofInsertion env U Γ Δ ρ)
    (henv : env.Ordered) :
    ∃ F : SplitTypedEmbedding env U Γ Δ, F.liftMap = ρ := by
  induction H with
  | refl hΓ => exact ⟨(SplitProofFrame.refl henv hΓ).toTypedEmbedding henv, rfl⟩
  | @cons Γ Δ ρ A u H hA ih =>
    obtain ⟨F, hF⟩ := ih
    have hdomain : (A.lift' ρ).subst F.retract = A := by rw [← hF, F.leftInv]
    have h : ∃ G : SplitTypedEmbedding env U
        ((A.lift' ρ).subst F.retract :: Γ) (A.lift' ρ :: Δ), G.liftMap = ρ.cons :=
      ⟨F.underBinder henv (hA.weak' henv H.weakening), congrArg Lift.cons hF⟩
    rw [hdomain] at h
    exact h
  | @skip Γ Δ ρ P q H hP hq ih =>
    obtain ⟨F, hF⟩ := ih
    subst ρ
    refine ⟨{
      liftMap := F.liftMap.skip
      retract := F.retract.cons (q.subst F.retract)
      weakening := (H.skip hP hq).typedRenaming henv
      typed := .cons F.typed hP (hq.subst henv F.typed F.baseWF)
      leftInv := ?_
      rightInv := ?_
    }, rfl⟩
    · intro e
      rw [lift_skip, lift_subst_cons, F.leftInv]
    · have htail := F.rightInv.skip (B := P) henv
      have ht : Ctx.SubstEq env U (P :: Δ) Subst.id.tail
          ((F.retract.cons (q.subst F.retract)).lift_r F.liftMap.skip).tail Δ := by
        have he : (F.retract.lift_r F.liftMap).lift_r (.skip .refl) =
            ((F.retract.cons (q.subst F.retract)).lift_r F.liftMap.skip).tail := by
          funext i
          change ((F.retract i).lift' F.liftMap).lift' (.skip .refl) =
            (F.retract i).lift' F.liftMap.skip
          rw [← lift'_comp]
          rfl
        rwa [he] at htail
      refine .cons ht hP ?_
      have hq' := (F.roundTrip henv hq).hasType.2
      have heq := IsDefEq.proofIrrel (hP.weak henv)
        (show env.HasType U (P :: Δ) (.bvar 0) P.lift from .bvar .zero)
        (hq'.weak henv)
      change env.IsDefEq U (P :: Δ) (.bvar 0)
        ((q.subst F.retract).lift' F.liftMap.skip) (P.subst Subst.id.tail)
      rw [lift_skip, show P.subst Subst.id.tail = P.lift from by
        rw [← lift_subst, subst_id]]
      exact heq

/-- Generated insertions commute by inserting the renamed proof/data domains.
The equality is between literal renamings, not merely equal actions on a
chosen expression. -/
theorem ProofInsertion.pushout (H : ProofInsertion env U Γ Δ ρ)
    (K : FutureInsertion env U Γ V τ) (henv : env.Ordered) :
    ∃ W i j, ProofInsertion env U V W i ∧ FutureInsertion env U Δ W j ∧
      ρ.comp j = τ.comp i := by
  generalize heq : ρ.size + τ.size = n
  induction n using Nat.strongRecOn generalizing Γ Δ V ρ τ with
  | ind n ih =>
    cases H with
    | refl hΓ =>
      exact ⟨V, .refl, τ, .refl (K.targetWF henv), K, by simp⟩
    | @skip Γ Δ ρ P q H hP hq =>
      obtain ⟨W, i, j, hi, hj, he⟩ := ih _ (by simp_all only [Lift.size]; omega) H K rfl
      exact ⟨P.lift' j :: W, i.skip, j.cons,
        hi.skip (hP.weak' henv hj.weakening) (hq.weak' henv hj.weakening),
        hj.cons hP, by simpa only [Lift.comp] using congrArg Lift.skip he⟩
    | @cons Γ Δ ρ A u H hA =>
      cases K with
      | refl hΓ =>
        exact ⟨A.lift' ρ :: Δ, ρ.cons, .refl, H.cons hA,
          .refl ((H.cons hA).targetWF henv), by simp⟩
      | @skip _ V τ B v K hB =>
        obtain ⟨W, i, j, hi, hj, he⟩ := ih _ (by simp_all only [Lift.size]; omega) (H.cons hA) K rfl
        exact ⟨B.lift' i :: W, i.cons, j.skip, hi.cons hB,
          hj.skip (hB.weak' henv hi.weakening),
          by simpa only [Lift.comp] using congrArg Lift.skip he⟩
      | @cons _ V τ _ v K hA' =>
        obtain ⟨W, i, j, hi, hj, he⟩ := ih _ (by simp_all only [Lift.size]; omega) H K rfl
        have hdomain : (A.lift' ρ).lift' j = (A.lift' τ).lift' i := by
          simpa only [← lift'_comp] using congrArg (A.lift' ·) he
        refine ⟨(A.lift' ρ).lift' j :: W, i.cons, j.cons, ?_,
          hj.cons (hA.weak' henv H.weakening), ?_⟩
        · rw [hdomain]
          exact hi.cons (hA'.weak' henv K.weakening)
        · simpa only [Lift.comp] using congrArg Lift.cons he

/-- Amalgamating two proof histories retains proof histories on both legs.
In particular, subsequent witnessed outputs can compose these certificates. -/
theorem ProofInsertion.pushoutProof (H : ProofInsertion env U Γ Δ ρ)
    (K : ProofInsertion env U Γ V τ) (henv : env.Ordered) :
    ∃ W i j, ProofInsertion env U V W i ∧ ProofInsertion env U Δ W j ∧
      ρ.comp j = τ.comp i := by
  generalize heq : ρ.size + τ.size = n
  induction n using Nat.strongRecOn generalizing Γ Δ V ρ τ with
  | ind n ih =>
    cases H with
    | refl hΓ =>
      exact ⟨V, .refl, τ, .refl (K.targetWF henv), K, by simp⟩
    | @skip Γ Δ ρ P q H hP hq =>
      obtain ⟨W, i, j, hi, hj, he⟩ :=
        ih _ (by simp_all only [Lift.size]; omega) H K rfl
      exact ⟨P.lift' j :: W, i.skip, j.cons,
        hi.skip (hP.weak' henv hj.weakening) (hq.weak' henv hj.weakening),
        hj.cons hP, by simpa only [Lift.comp] using congrArg Lift.skip he⟩
    | @cons Γ Δ ρ A u H hA =>
      cases K with
      | refl hΓ =>
        exact ⟨A.lift' ρ :: Δ, ρ.cons, .refl, H.cons hA,
          .refl ((H.cons hA).targetWF henv), by simp⟩
      | @skip _ V τ P q K hP hq =>
        obtain ⟨W, i, j, hi, hj, he⟩ :=
          ih _ (by simp_all only [Lift.size]; omega) (H.cons hA) K rfl
        exact ⟨P.lift' i :: W, i.cons, j.skip, hi.cons hP,
          hj.skip (hP.weak' henv hi.weakening) (hq.weak' henv hi.weakening),
          by simpa only [Lift.comp] using congrArg Lift.skip he⟩
      | @cons _ V τ _ v K hA' =>
        obtain ⟨W, i, j, hi, hj, he⟩ :=
          ih _ (by simp_all only [Lift.size]; omega) H K rfl
        have hdomain : (A.lift' ρ).lift' j = (A.lift' τ).lift' i := by
          simpa only [← lift'_comp] using congrArg (A.lift' ·) he
        refine ⟨(A.lift' ρ).lift' j :: W, i.cons, j.cons, ?_,
          hj.cons (hA.weak' henv H.weakening), ?_⟩
        · rw [hdomain]
          exact hi.cons (hA'.weak' henv K.weakening)
        · simpa only [Lift.comp] using congrArg Lift.cons he

end Lean4Lean.VEnv
