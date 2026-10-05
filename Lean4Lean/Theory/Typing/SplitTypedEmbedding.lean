import Lean4Lean.Theory.Typing.SplitProofFrame

/-!
Split typed embeddings for dependent contexts in the proposed canonical
exposure argument. Unlike a literal context insertion, the domain of a
retained binder may agree with its reconstructed domain only by typed equality.

`underBinder` derives this domain conversion from the reverse inverse law and
uses `Ctx.SubstEq.lift_at`. Neither Pi injectivity nor type uniqueness is used.
Canonical native trace stability and the equality foundation remain separate
obligations; the records here are constructed from proved proof-frame facts.
-/

namespace Lean4Lean.VEnv
open VExpr

theorem Ctx.SubstEq.weakenTarget (henv : env.Ordered)
    (W : Ctx.SubstEq env U Γ σ σ' source) (L : Ctx.Lift' ρ Γ Δ) :
    Ctx.SubstEq env U Δ (σ.lift_r ρ) (σ'.lift_r ρ) source := by
  induction W with
  | nil => exact .nil
  | cons _ hA hHead ih =>
    refine .cons (Subst.lift_r_tail ▸ Subst.lift_r_tail ▸ ih) hA ?_
    have h := hHead.weak' henv L
    simpa only [lift'_subst, Subst.lift_r_tail, Subst.head, Subst.lift_r] using h

/-- A renaming with a typed retraction and a typed reverse inverse.
The context domains may be definitionally, rather than literally, equal. -/
structure SplitTypedEmbedding (env : VEnv) (U : Nat) (Γ Δ : List VExpr) where
  liftMap : Lift
  retract : Subst
  weakening : Ctx.SubstEq env U Δ (Subst.id.lift_r liftMap)
    (Subst.id.lift_r liftMap) Γ
  typed : Ctx.SubstEq env U Γ retract retract Δ
  leftInv : ∀ e : VExpr, (e.lift' liftMap).subst retract = e
  rightInv : Ctx.SubstEq env U Δ .id (retract.lift_r liftMap) Δ

namespace SplitTypedEmbedding
variable {env : VEnv} {U : Nat} {Γ Δ : List VExpr} {e e' A : VExpr}

theorem baseWF (F : SplitTypedEmbedding env U Γ Δ) : OnCtx Γ (env.IsType U) :=
  F.weakening.wf

theorem targetWF (F : SplitTypedEmbedding env U Γ Δ) : OnCtx Δ (env.IsType U) :=
  F.typed.wf

theorem roundTrip (F : SplitTypedEmbedding env U Γ Δ) (henv : env.Ordered)
    (H : env.IsDefEq U Δ e e' A) :
    env.IsDefEq U Δ e ((e'.subst F.retract).lift' F.liftMap) A := by
  simpa only [subst_id, ← lift'_subst] using
    H.substDF henv F.targetWF F.targetWF F.rightInv

theorem reflect (F : SplitTypedEmbedding env U Γ Δ) (henv : env.Ordered)
    (H : env.IsDefEq U Δ (e.lift' F.liftMap) (e'.lift' F.liftMap)
      (A.lift' F.liftMap)) : env.IsDefEq U Γ e e' A := by
  simpa only [F.leftInv] using H.subst henv F.typed F.baseWF

/-- Compare two realizations of a commonly typed symbolic expression. The
embeddings must identify the same base-variable positions, but their base
contexts and retraction witnesses may differ. Retract the second round trip
using the first realization; no type uniqueness or component inversion is used.

The common symbolic typing is essential. Separate typings of the two
readbacks do not supply this comparison. -/
theorem compareRetractions
    (F : SplitTypedEmbedding env U Γ Δ)
    (G : SplitTypedEmbedding env U Γ' Δ)
    (henv : env.Ordered) (hlift : G.liftMap = F.liftMap)
    (H : env.IsDefEq U Δ e e' A) :
    env.IsDefEq U Γ (e.subst F.retract) (e'.subst G.retract)
      (A.subst F.retract) := by
  have h := (G.roundTrip henv H).subst henv F.typed F.baseWF
  simpa only [hlift, F.leftInv] using h

def underBinder (F : SplitTypedEmbedding env U Γ Δ) (henv : env.Ordered)
    (hA : env.HasType U Δ A (.sort level)) :
    SplitTypedEmbedding env U (A.subst F.retract :: Γ) (A :: Δ) where
  liftMap := F.liftMap.cons
  retract := F.retract.lift
  weakening := by
    have hSource := hA.subst henv F.typed F.baseWF
    have hEq := (F.roundTrip henv hA).symm
    have hEq' : env.IsDefEq U Δ
        ((A.subst F.retract).subst (Subst.id.lift_r F.liftMap)) A (.sort level) := by
      simpa only [← lift'_subst, subst_id] using hEq
    have h := F.weakening.lift_at henv hSource hEq'
    simpa only [Subst.lift_r_lift, id_lift] using h
  typed := F.typed.lift henv hA
  leftInv := by
    intro e
    rw [subst_lift']
    have h : Subst.lift_l F.liftMap.cons F.retract.lift = Subst.id := by
      funext i
      cases i with
      | zero => rfl
      | succ i =>
        have hi := F.leftInv (.bvar i)
        change F.retract (F.liftMap.liftVar i) = .bvar i at hi
        change (F.retract (F.liftMap.liftVar i)).lift = .bvar (i + 1)
        rw [hi]
        simp [lift, liftN, liftVar, Nat.add_comm]
    rw [h, subst_id]
  rightInv := by
    have h := F.rightInv.lift henv hA
    simpa only [subst_id, id_lift, Subst.lift_r_lift] using h

end SplitTypedEmbedding

def SplitProofFrame.toTypedEmbedding (F : SplitProofFrame env U Γ Δ n)
    (henv : env.Ordered) : SplitTypedEmbedding env U Γ Δ where
  liftMap := .skipN .refl n
  retract := F.retract
  weakening := by
    exact (Ctx.SubstEq.id henv F.baseWF).weakenTarget henv
      (Ctx.liftN_iff_lift'.1 F.weakening)
  typed := F.typed
  leftInv := by
    intro e
    rw [show e.lift' (.skipN .refl n) = e.liftN n from lift'_consN_skipN (k := 0)]
    exact F.leftInv e
  rightInv := by
    have h : F.retract.lift_r (.skipN .refl n) = raisedSubst F.retract n := by
      funext i
      exact lift'_consN_skipN (k := 0)
    rw [h]
    exact F.rightInv

/-- Two realizations of one symbolic Pi display give actual component
equalities, with the codomains compared under the first realized domain.
The ordinary Pi binder stays in scope throughout the comparison.

This discharges the readback step after symbolic head alignment. Constructing
that common typed display from native observations remains a separate task. -/
theorem SplitProofFrame.piReadbacks
    (F G : SplitProofFrame env U Γ Δ n) (henv : env.Ordered)
    (hA : env.HasType U Δ A (.sort u))
    (hB : env.HasType U (A :: Δ) B (.sort v)) :
    env.IsDefEq U Γ (A.subst F.retract) (A.subst G.retract) (.sort u) ∧
    env.IsDefEq U (A.subst F.retract :: Γ)
      (B.subst F.retract.lift) (B.subst G.retract.lift) (.sort v) := by
  let F' := F.toTypedEmbedding henv
  let G' := G.toTypedEmbedding henv
  refine ⟨?_, ?_⟩
  · exact F'.compareRetractions G' henv rfl hA
  · exact (F'.underBinder henv hA).compareRetractions
      (G'.underBinder henv hA) henv rfl hB

end Lean4Lean.VEnv
