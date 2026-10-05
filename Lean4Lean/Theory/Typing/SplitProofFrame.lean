import Lean4Lean.Theory.Typing.Strong

/-!
Fresh proof variables with an actual typed retraction to the original context.

This is the conservative context operation needed by the proposed native
replay exposure argument. Each new binder is a proposition already inhabited
in the current context. Its witness is retained in the retraction; generated
syntax may use the fresh variable independently of that witness.

Both inverse laws are proved: retracting a weakened term is a literal
identity, and weakening a retracted term is definitionally equal to the
original term by proof irrelevance. Thus these specific extensions support
context reflection. This does not establish unrestricted strengthening,
canonical native exposure, or Pi injectivity.
-/

namespace Lean4Lean.VEnv
open VExpr

def raisedSubst (σ : Subst) (n : Nat) : Subst := fun i => (σ i).liftN n

theorem subst_raised (e : VExpr) (σ : Subst) (n : Nat) :
    e.subst (raisedSubst σ n) = (e.subst σ).liftN n := by
  rw [← lift'_consN_skipN, lift'_subst]
  congr 1
  funext i
  simp only [raisedSubst, Subst.lift_r, lift'_consN_skipN]

/-- A context extension whose projection has a typed inverse up to proof
irrelevance. The reverse equation is retained as related substitutions;
it is not an unrestricted context-reflection principle. -/
structure SplitProofFrame (env : VEnv) (U : Nat) (Γ Δ : List VExpr) (n : Nat) where
  retract : Subst
  baseWF : OnCtx Γ (env.IsType U)
  targetWF : OnCtx Δ (env.IsType U)
  weakening : Ctx.LiftN n 0 Γ Δ
  typed : Ctx.SubstEq env U Γ retract retract Δ
  leftInv : ∀ e : VExpr, (e.liftN n).subst retract = e
  rightInv : Ctx.SubstEq env U Δ .id (raisedSubst retract n) Δ

namespace SplitProofFrame

variable {env : VEnv} {U n : Nat} {Γ Δ : List VExpr} {P q e e' A : VExpr}

def refl (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U)) :
    SplitProofFrame env U Γ Γ 0 where
  retract := .id
  baseWF := hΓ
  targetWF := hΓ
  weakening := .zero []
  typed := .id henv hΓ
  leftInv := by intro e; simp
  rightInv := by
    have h : raisedSubst Subst.id 0 = Subst.id := by
      funext i
      exact liftN_zero _ 0
    rw [h]
    exact Ctx.SubstEq.id henv hΓ

theorem roundTrip (F : SplitProofFrame env U Γ Δ n) (henv : env.Ordered)
    (H : env.IsDefEq U Δ e e' A) :
    env.IsDefEq U Δ e ((e'.subst F.retract).liftN n) A := by
  simpa only [subst_id, subst_raised] using
    H.substDF henv F.targetWF F.targetWF F.rightInv

/-- Introduce a fresh proof variable. The witness determines only the
retraction; the added context and fresh variable do not depend on it. -/
def cons (F : SplitProofFrame env U Γ Δ n) (henv : env.Ordered)
    (hP : env.HasType U Δ P (.sort .zero)) (hq : env.HasType U Δ q P) :
    SplitProofFrame env U Γ (P :: Δ) (n + 1) where
  retract := F.retract.cons (q.subst F.retract)
  baseWF := F.baseWF
  targetWF := ⟨F.targetWF, _, hP⟩
  weakening := F.weakening.comp (Nat.le_refl 0) (Nat.zero_le n) .one
  typed := .cons F.typed hP (hq.subst henv F.typed F.baseWF)
  leftInv := by
    intro e
    rw [liftN_succ, lift_subst_cons, F.leftInv]
  rightInv := by
    have htail := F.rightInv.skip (B := P) henv
    have ht : Ctx.SubstEq env U (P :: Δ) Subst.id.tail
        (raisedSubst (F.retract.cons (q.subst F.retract)) (n + 1)).tail Δ := by
      have hright : (raisedSubst F.retract n).lift_r (.skip .refl) =
          (raisedSubst (F.retract.cons (q.subst F.retract)) (n + 1)).tail := by
        funext i
        change ((F.retract i).liftN n).lift' (.skip .refl) =
          (F.retract i).liftN (n + 1)
        rw [liftN_succ, lift_eq_lift']
      rwa [hright] at htail
    refine .cons ht hP ?_
    have hq' := (F.roundTrip henv hq).hasType.2
    have heq := IsDefEq.proofIrrel (hP.weak henv)
      (show env.HasType U (P :: Δ) (.bvar 0) P.lift from .bvar .zero)
      (hq'.weak henv)
    change env.IsDefEq U (P :: Δ) (.bvar 0)
      ((q.subst F.retract).liftN (n + 1)) (P.subst Subst.id.tail)
    rw [liftN_succ, show P.subst Subst.id.tail = P.lift from by
      rw [← lift_subst, subst_id]]
    exact heq

/-- Reflection is sound along this particular extension because a typed
retraction is available. No support-based strengthening is used. -/
theorem reflect (F : SplitProofFrame env U Γ Δ n) (henv : env.Ordered)
    (H : env.IsDefEq U Δ (e.liftN n) (e'.liftN n) (A.liftN n)) :
    env.IsDefEq U Γ e e' A := by
  simpa only [F.leftInv] using H.subst henv F.typed F.baseWF


end SplitProofFrame
end Lean4Lean.VEnv
