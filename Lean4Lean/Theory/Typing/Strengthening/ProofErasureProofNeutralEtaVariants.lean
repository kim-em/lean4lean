import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNormalSyntax

/-! # Protected neutral eta marks with erased proof arguments

These syntactic pairs keep the ambient variable and its annotation protected
under local substitution. Beta simulation requires actual typing: an applied
proof-domain mark must receive an argument that erases to the proof marker.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open private lifted_middle from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants
variable {σ τ : Subst} {Guard : ProofShape → Nat → Prop}

/-- Structural pairs with either orientation of eta at a protected ambient
variable. The local depth protects both the annotation and the variable index. -/
inductive ProofNeutralEtaVariant (Guard : ProofShape → Nat → Prop) :
    Nat → ProofShape → ProofShape → Prop where
  | refl : ProofNeutralEtaVariant Guard n a a
  | app : ProofNeutralEtaVariant Guard n f g → ProofNeutralEtaVariant Guard n x y →
      ProofNeutralEtaVariant Guard n (.app f x) (.app g y)
  | proj : ProofNeutralEtaVariant Guard n a b → ProofNeutralEtaVariant Guard n (.proj s i a) (.proj s i b)
  | lam : ProofNeutralEtaVariant Guard n A C → ProofNeutralEtaVariant Guard (n+1) b c →
      ProofNeutralEtaVariant Guard n (.lam A b) (.lam C c)
  | forallE : ProofNeutralEtaVariant Guard n A C → ProofNeutralEtaVariant Guard (n+1) B E →
      ProofNeutralEtaVariant Guard n (.forallE A B) (.forallE C E)
  | etaL : Guard A i → ProofNeutralEtaVariant Guard n
      (.lam (A.liftN n) (.app (.bvar (i+n+1)) .proof)) (.bvar (i+n))
  | etaR : Guard A i → ProofNeutralEtaVariant Guard n
      (.bvar (i+n)) (.lam (A.liftN n) (.app (.bvar (i+n+1)) .proof))

/-- Reversing a pair preserves its ambient neutral origin. -/
theorem ProofNeutralEtaVariant.symm (H : ProofNeutralEtaVariant Guard n a b) : ProofNeutralEtaVariant Guard n b a := by
  induction H with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihb => exact .forallE ihA ihb
  | etaL HG => exact .etaR HG
  | etaR HG => exact .etaL HG

/-- Inserting local binders retains the same protected eta origin. -/
theorem ProofNeutralEtaVariant.liftN (H : ProofNeutralEtaVariant Guard n a b) (hk : k ≤ n) :
    ProofNeutralEtaVariant Guard (n+m) (a.liftN m k) (b.liftN m k) := by
  induction H generalizing k with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app (ihf hk) (ihx hk)
  | proj _ ih => exact .proj (ih hk)
  | lam _ _ ihA ihb =>
    exact .lam (ihA hk) (by simpa only [Nat.add_right_comm] using ihb (show k+1 ≤ _ by omega))
  | forallE _ _ ihA ihb =>
    exact .forallE (ihA hk) (by simpa only [Nat.add_right_comm] using ihb (show k+1 ≤ _ by omega))
  | @etaL A i n HG =>
    simpa only [ProofShape.liftN, lifted_middle _ hk, liftVar,
      if_neg (show ¬ i+n+1 < k+1 by omega),
      if_neg (show ¬ i+(n+1) < k+1 by omega), if_neg (show ¬ i+n < k by omega),
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (ProofNeutralEtaVariant.etaL (n := n+m) HG)
  | @etaR A i n HG =>
    simpa only [ProofShape.liftN, lifted_middle _ hk, liftVar,
      if_neg (show ¬ i+n+1 < k+1 by omega),
      if_neg (show ¬ i+(n+1) < k+1 by omega), if_neg (show ¬ i+n < k by omega),
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (ProofNeutralEtaVariant.etaR (n := n+m) HG)

private theorem lift_images (H : ∀ i, ProofNeutralEtaVariant Guard m (σ i) (τ i)) :
    ∀ i, ProofNeutralEtaVariant Guard (m+1) (σ.lift i) (τ.lift i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (H i).liftN (Nat.zero_le m)

/-- Arbitrary raw templates retain independently related substitution images. -/
theorem ProofNeutralEtaVariant.subst_images (a : ProofShape)
    (H : ∀ i, ProofNeutralEtaVariant Guard m (σ i) (τ i)) :
    ProofNeutralEtaVariant Guard m (a.subst σ) (a.subst τ) := by
  induction a generalizing m σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app _ _ ihf ihx => exact .app (ihf H) (ihx H)
  | proj _ _ _ ih => exact .proj (ih H)
  | lam _ _ ihA ihb => exact .lam (ihA H) (ihb (lift_images H))
  | forallE _ _ ihA ihb => exact .forallE (ihA H) (ihb (lift_images H))

/-- Local substitutions may differ everywhere in the prefix. Their protected
ambient tails keep a marked variable neutral, even when images contain marks. -/
theorem ProofNeutralEtaVariant.subst_pair (V : ProofNeutralEtaVariant Guard n a b)
    (HS : σ.PreservesTail n m) (HT : τ.PreservesTail n m)
    (H : ∀ i, ProofNeutralEtaVariant Guard m (σ i) (τ i)) :
    ProofNeutralEtaVariant Guard m (a.subst σ) (b.subst τ) := by
  induction V generalizing m σ τ with
  | refl => exact .subst_images _ H
  | app _ _ ihf ihx => exact .app (ihf HS HT H) (ihx HS HT H)
  | proj _ ih => exact .proj (ih HS HT H)
  | lam _ _ ihA ihb => exact .lam (ihA HS HT H) (ihb HS.lift HT.lift (lift_images H))
  | forallE _ _ ihA ihb => exact .forallE (ihA HS HT H) (ihb HS.lift HT.lift (lift_images H))
  | @etaL A i n HG =>
    simp only [subst, HS.apply_lift, Subst.lift, HS i, HT i, ProofShape.liftN,
      liftVar, Nat.not_lt_zero, if_false]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ProofNeutralEtaVariant.etaL (n := m) HG
  | @etaR A i n HG =>
    simp only [subst, HT.apply_lift, Subst.lift, HS i, HT i, ProofShape.liftN,
      liftVar, Nat.not_lt_zero, if_false]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ProofNeutralEtaVariant.etaR (n := m) HG

/-- Beta substitution preserves the protected neutral marks on both sides. -/
theorem ProofNeutralEtaVariant.inst_pair (V : ProofNeutralEtaVariant Guard (n+1) a b)
    (H : ProofNeutralEtaVariant Guard n x y) : ProofNeutralEtaVariant Guard n (a.inst x) (b.inst y) := by
  simp only [inst_eq_subst, Subst.liftN]
  apply V.subst_pair
  · intro i; rfl
  · intro i; rfl
  · intro i; cases i with
    | zero => exact H
    | succ i => exact .refl

/-- A paired proof marker is unchanged: eta marks only affect variable and
lambda roots. This is used after typing identifies a proof argument. -/
theorem ProofNeutralEtaVariant.proof_right (V : ProofNeutralEtaVariant Guard n .proof b) : b = .proof := by
  cases V
  rfl

end Lean4Lean.VEnv.Strengthening.ProofShape
