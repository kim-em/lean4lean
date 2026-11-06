import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNormalSyntax

/-! # Protected neutral eta expansions under local beta reduction

The short endpoint of a mark is an ambient variable. Local substitution may
duplicate or discard marks but cannot replace that variable by a lambda.
These marks retain the bound argument; proof-domain eta needs a typed extension
and is not asserted by this raw relation. No general comparison readout or
arbitrary ambient-substitution closure is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open private lifted_middle from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants
variable {σ τ : Subst} {Guard : ProofShape → Nat → Prop}

/-- Structural pairs with either orientation of eta at a protected ambient
variable. The local depth protects both the annotation and the variable index. -/
inductive NeutralEtaVariant (Guard : ProofShape → Nat → Prop) :
    Nat → ProofShape → ProofShape → Prop where
  | refl : NeutralEtaVariant Guard n a a
  | app : NeutralEtaVariant Guard n f g → NeutralEtaVariant Guard n x y →
      NeutralEtaVariant Guard n (.app f x) (.app g y)
  | proj : NeutralEtaVariant Guard n a b → NeutralEtaVariant Guard n (.proj s i a) (.proj s i b)
  | lam : NeutralEtaVariant Guard n A C → NeutralEtaVariant Guard (n+1) b c →
      NeutralEtaVariant Guard n (.lam A b) (.lam C c)
  | forallE : NeutralEtaVariant Guard n A C → NeutralEtaVariant Guard (n+1) B E →
      NeutralEtaVariant Guard n (.forallE A B) (.forallE C E)
  | etaL : Guard A i → NeutralEtaVariant Guard n
      (.lam (A.liftN n) (.app (.bvar (i+n+1)) (.bvar 0))) (.bvar (i+n))
  | etaR : Guard A i → NeutralEtaVariant Guard n
      (.bvar (i+n)) (.lam (A.liftN n) (.app (.bvar (i+n+1)) (.bvar 0)))

/-- Reversing a pair preserves its ambient neutral origin. -/
theorem NeutralEtaVariant.symm (H : NeutralEtaVariant Guard n a b) : NeutralEtaVariant Guard n b a := by
  induction H with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihb => exact .forallE ihA ihb
  | etaL HG => exact .etaR HG
  | etaR HG => exact .etaL HG

/-- Inserting local binders retains the same protected eta origin. -/
theorem NeutralEtaVariant.liftN (H : NeutralEtaVariant Guard n a b) (hk : k ≤ n) :
    NeutralEtaVariant Guard (n+m) (a.liftN m k) (b.liftN m k) := by
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
      Nat.zero_lt_succ, if_true, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (NeutralEtaVariant.etaL (n := n+m) HG)
  | @etaR A i n HG =>
    simpa only [ProofShape.liftN, lifted_middle _ hk, liftVar,
      if_neg (show ¬ i+n+1 < k+1 by omega),
      if_neg (show ¬ i+(n+1) < k+1 by omega), if_neg (show ¬ i+n < k by omega),
      Nat.zero_lt_succ, if_true, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (NeutralEtaVariant.etaR (n := n+m) HG)

private theorem lift_images (H : ∀ i, NeutralEtaVariant Guard m (σ i) (τ i)) :
    ∀ i, NeutralEtaVariant Guard (m+1) (σ.lift i) (τ.lift i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (H i).liftN (Nat.zero_le m)

/-- Arbitrary raw templates retain independently related substitution images. -/
theorem NeutralEtaVariant.subst_images (a : ProofShape)
    (H : ∀ i, NeutralEtaVariant Guard m (σ i) (τ i)) :
    NeutralEtaVariant Guard m (a.subst σ) (a.subst τ) := by
  induction a generalizing m σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app _ _ ihf ihx => exact .app (ihf H) (ihx H)
  | proj _ _ _ ih => exact .proj (ih H)
  | lam _ _ ihA ihb => exact .lam (ihA H) (ihb (lift_images H))
  | forallE _ _ ihA ihb => exact .forallE (ihA H) (ihb (lift_images H))

/-- Local substitutions may differ everywhere in the prefix. Their protected
ambient tails keep a marked variable neutral, even when images contain marks. -/
theorem NeutralEtaVariant.subst_pair (V : NeutralEtaVariant Guard n a b)
    (HS : σ.PreservesTail n m) (HT : τ.PreservesTail n m)
    (H : ∀ i, NeutralEtaVariant Guard m (σ i) (τ i)) :
    NeutralEtaVariant Guard m (a.subst σ) (b.subst τ) := by
  induction V generalizing m σ τ with
  | refl => exact .subst_images _ H
  | app _ _ ihf ihx => exact .app (ihf HS HT H) (ihx HS HT H)
  | proj _ ih => exact .proj (ih HS HT H)
  | lam _ _ ihA ihb => exact .lam (ihA HS HT H) (ihb HS.lift HT.lift (lift_images H))
  | forallE _ _ ihA ihb => exact .forallE (ihA HS HT H) (ihb HS.lift HT.lift (lift_images H))
  | @etaL A i n HG =>
    simp only [subst, HS.apply_lift, Subst.lift, HS i, HT i, ProofShape.liftN,
      liftVar, Nat.not_lt_zero, if_false]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using NeutralEtaVariant.etaL (n := m) HG
  | @etaR A i n HG =>
    simp only [subst, HT.apply_lift, Subst.lift, HS i, HT i, ProofShape.liftN,
      liftVar, Nat.not_lt_zero, if_false]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using NeutralEtaVariant.etaR (n := m) HG

/-- Beta substitution preserves the protected neutral marks on both sides. -/
theorem NeutralEtaVariant.inst_pair (V : NeutralEtaVariant Guard (n+1) a b)
    (H : NeutralEtaVariant Guard n x y) : NeutralEtaVariant Guard n (a.inst x) (b.inst y) := by
  simp only [inst_eq_subst, Subst.liftN]
  apply V.subst_pair
  · intro i; rfl
  · intro i; rfl
  · intro i; cases i with
    | zero => exact H
    | succ i => exact .refl

private theorem neutral_body_fixed (R : BetaRed (.app (.bvar i) (.bvar 0)) out) :
    out = .app (.bvar i) (.bvar 0) := by
  apply R.fixed_of_normal (Step := fun _ _ => False)
  exact ⟨fun _ H => H, (by intro A b H; cases H),
    ⟨fun _ H => H, trivial⟩, ⟨fun _ H => H, trivial⟩⟩

/-- Every beta path has a paired path. Applying a marked expansion discards
its wrapper and leaves the same ambient variable applied to related arguments;
no new lambda-domain comparison is needed in this neutral case. -/
theorem NeutralEtaVariant.beta_left
    (hg : ∀ {A i A'}, Guard A i → BetaRed A A' → Guard A' i)
    (R : BetaRed a a') (V : NeutralEtaVariant Guard n a b) :
    ∃ b', BetaRed b b' ∧ NeutralEtaVariant Guard n a' b' := by
  induction R generalizing n b with
  | refl => exact ⟨_, .refl, V⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨b₁, RB, V₁⟩ := ih₁ V
    obtain ⟨b₂, RC, V₂⟩ := ih₂ V₁
    exact ⟨b₂, RB.trans RC, V₂⟩
  | app RF RX ihf ihx =>
    cases V with
    | refl => exact ⟨_, .app RF RX, .refl⟩
    | app VF VX =>
      obtain ⟨g, RG, VG⟩ := ihf VF
      obtain ⟨y, RY, VY⟩ := ihx VX
      exact ⟨_, .app RG RY, .app VG VY⟩
  | proj R ih =>
    cases V with
    | refl => exact ⟨_, .proj R, .refl⟩
    | proj V =>
      obtain ⟨b, RB, VB⟩ := ih V
      exact ⟨_, .proj RB, .proj VB⟩
  | lam RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .lam RA RB, .refl⟩
    | lam VA VB =>
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨c, Rc, Vc⟩ := ihB VB
      exact ⟨_, .lam RC Rc, .lam VC Vc⟩
    | etaL HG =>
      obtain ⟨A', RA', rfl⟩ := RA.liftN_inv
      obtain rfl := neutral_body_fixed RB
      exact ⟨_, .refl, .etaL (hg HG RA')⟩
  | forallE RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨c, Rc, Vc⟩ := ihB VB
      exact ⟨_, .forallE RC Rc, .forallE VC Vc⟩
  | beta =>
    cases V with
    | refl => exact ⟨_, .beta, .refl⟩
    | app VF VX =>
      cases VF with
      | refl => exact ⟨_, .beta, NeutralEtaVariant.refl.inst_pair VX⟩
      | lam _ VB => exact ⟨_, .beta, VB.inst_pair VX⟩
      | etaL HG =>
        refine ⟨_, .refl, ?_⟩
        simpa [ProofShape.inst, instVar, ProofShape.liftN_zero] using
          NeutralEtaVariant.app NeutralEtaVariant.refl VX

/-- Independent beta paths can be continued to related residuals. Only raw
beta confluence at one endpoint is used; the paired terms need not join. -/
theorem NeutralEtaVariant.beta_residuals
    (hg : ∀ {A i A'}, Guard A i → BetaRed A A' → Guard A' i)
    (V : NeutralEtaVariant Guard n a b) (RA : BetaRed a p) (RB : BetaRed b q) :
    ∃ p' q', BetaRed p p' ∧ BetaRed q q' ∧ NeutralEtaVariant Guard n p' q' := by
  obtain ⟨b₁, RB₁, V₁⟩ := NeutralEtaVariant.beta_left (Guard := Guard) (fun H R => hg H R) RA V
  obtain ⟨q', RQ, RB₁'⟩ := RB.raw_confluent RB₁
  obtain ⟨p', RP, V₂⟩ := NeutralEtaVariant.beta_left (Guard := Guard) (fun H R => hg H R) RB₁' V₁.symm
  exact ⟨p', q', RP, RQ, V₂.symm⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
