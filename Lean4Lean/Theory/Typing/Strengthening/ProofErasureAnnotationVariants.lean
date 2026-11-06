import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRawBetaJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-! # Paired annotation changes protected from local beta substitution

A marked lambda uses a pair of domains from the ambient context. At local
binder depth n, both domains are lifted by n. Substitution may replace local
variables by different related images, but preserves the ambient variables.
Thus beta may duplicate or discard marked lambdas without substituting different
images into their stored domain certificates. No unary reannotation reduction
or claim of typed descent is introduced.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private liftN_app_inv liftN_proj_inv liftN_lam_inv liftN_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable {σ τ : Subst} {Guard : ProofShape → ProofShape → Prop}

/-- Pure beta cannot introduce a variable into an omitted block. The exact
reduct is the lift of a beta reduct of the original raw proof shape. -/
theorem BetaRed.liftN_inv (R : BetaRed (a.liftN n k) out) :
    ∃ a', BetaRed a a' ∧ out = a'.liftN n k := by
  generalize E : a.liftN n k = source at R
  induction R generalizing a k with
  | refl => exact ⟨a, .refl, E.symm⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨a₁, R₁, E₁⟩ := ih₁ E
    obtain ⟨a₂, R₂, E₂⟩ := ih₂ E₁.symm
    exact ⟨a₂, R₁.trans R₂, E₂⟩
  | app _ _ ihf ihx =>
    obtain ⟨f, x, rfl, rfl, rfl⟩ := liftN_app_inv E
    obtain ⟨f', RF, rfl⟩ := ihf rfl
    obtain ⟨x', RX, rfl⟩ := ihx rfl
    exact ⟨_, .app RF RX, rfl⟩
  | proj _ ih =>
    obtain ⟨m, rfl, rfl⟩ := liftN_proj_inv E
    obtain ⟨m', RM, rfl⟩ := ih rfl
    exact ⟨_, .proj RM, rfl⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := liftN_lam_inv E
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨b', RB, rfl⟩ := ihb rfl
    exact ⟨_, .lam RA RB, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := liftN_forallE_inv E
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨B', RB, rfl⟩ := ihB rfl
    exact ⟨_, .forallE RA RB, rfl⟩
  | beta =>
    obtain ⟨f, x, rfl, EF, rfl⟩ := liftN_app_inv E
    obtain ⟨A, b, rfl, rfl, rfl⟩ := liftN_lam_inv EF
    exact ⟨_, .beta, by simpa only [Nat.add_zero] using (liftN_instN b x n k 0).symm⟩

/-- Simultaneous substitution changes the local prefix and leaves the ambient
variables untouched, accounting for the new prefix length. -/
def Subst.PreservesTail (σ : Subst) (n m : Nat) : Prop :=
  ∀ i, σ (i + n) = .bvar (i + m)

/-- Protected ambient terms are unaffected by replacement of local variables. -/
theorem Subst.PreservesTail.apply_lift (H : σ.PreservesTail n m) (a : ProofShape) :
    (a.liftN n).subst σ = a.liftN m := by
  rw [← subst_bvar_liftN, subst_subst, ← subst_bvar_liftN]
  congr 1
  funext i
  simpa only [Subst.comp, subst, liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using H i

/-- Entering a binder extends the protected local prefix on both sides. -/
theorem Subst.PreservesTail.lift (H : σ.PreservesTail n m) :
    σ.lift.PreservesTail (n + 1) (m + 1) := by
  intro i
  rw [show i + (n + 1) = (i + n) + 1 by omega]
  change (σ (i + n)).liftN 1 = _
  rw [H i]
  change ProofShape.bvar (1 + (i + m)) = ProofShape.bvar (i + (m + 1))
  congr 1
  omega

private theorem lifted_middle (a : ProofShape) (h : k ≤ n) :
    (a.liftN n).liftN m k = a.liftN (n + m) := by
  rw [← subst_bvar_liftN]
  apply Subst.PreservesTail.apply_lift
  intro i
  simp only [liftVar, if_neg (show ¬ i + n < k by omega)]
  congr 1
  omega

/-- Structural paired terms with marked changes of ambient lambda domains.
The depth index counts local binders, protecting each marked domain from their
later instantiation. Ordinary syntax, including annotations, remains recursive. -/
inductive AnnotationVariant (Guard : ProofShape → ProofShape → Prop) :
    Nat → ProofShape → ProofShape → Prop where
  | refl : AnnotationVariant Guard n a a
  | app : AnnotationVariant Guard n f g → AnnotationVariant Guard n x y →
      AnnotationVariant Guard n (.app f x) (.app g y)
  | proj : AnnotationVariant Guard n a b → AnnotationVariant Guard n (.proj s i a) (.proj s i b)
  | lam : AnnotationVariant Guard n A C → AnnotationVariant Guard (n + 1) b c →
      AnnotationVariant Guard n (.lam A b) (.lam C c)
  | forallE : AnnotationVariant Guard n A C → AnnotationVariant Guard (n + 1) B E →
      AnnotationVariant Guard n (.forallE A B) (.forallE C E)
  | marked : Guard A C → AnnotationVariant Guard (n + 1) b c →
      AnnotationVariant Guard n (.lam (A.liftN n) b) (.lam (C.liftN n) c)

/-- Inserting local variables preserves every ambient annotation origin. -/
theorem AnnotationVariant.liftN (H : AnnotationVariant Guard n a b) (hk : k ≤ n) :
    AnnotationVariant Guard (n + m) (a.liftN m k) (b.liftN m k) := by
  induction H generalizing k with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app (ihf hk) (ihx hk)
  | proj _ ih => exact .proj (ih hk)
  | lam _ _ ihA ihb =>
    apply AnnotationVariant.lam (ihA hk)
    simpa only [Nat.add_right_comm] using ihb (show k + 1 ≤ _ by omega)
  | forallE _ _ ihA ihB =>
    apply AnnotationVariant.forallE (ihA hk)
    simpa only [Nat.add_right_comm] using ihB (show k + 1 ≤ _ by omega)
  | marked HG _ ih =>
    simp only [ProofShape.liftN, lifted_middle _ hk]
    apply AnnotationVariant.marked HG
    simpa only [Nat.add_right_comm] using ih (show k + 1 ≤ _ by omega)

private theorem lift_images (H : ∀ i, AnnotationVariant Guard m (σ i) (τ i)) :
    ∀ i, AnnotationVariant Guard (m + 1) (σ.lift i) (τ.lift i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (H i).liftN (Nat.zero_le m)

/-- An arbitrary raw template accepts independently related images. All
occurrences, including occurrences in dependent annotations, are retained. -/
theorem AnnotationVariant.subst_images (a : ProofShape)
    (H : ∀ i, AnnotationVariant Guard m (σ i) (τ i)) :
    AnnotationVariant Guard m (a.subst σ) (a.subst τ) := by
  induction a generalizing m σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app _ _ ihf ihx => exact .app (ihf H) (ihx H)
  | proj _ _ _ ih => exact .proj (ih H)
  | lam _ _ ihA ihb => exact .lam (ihA H) (ihb (lift_images H))
  | forallE _ _ ihA ihB => exact .forallE (ihA H) (ihB (lift_images H))

/-- Paired substitution of local variables preserves the relation. The two
maps may differ throughout the local prefix; only their ambient tails agree. -/
theorem AnnotationVariant.subst_pair (V : AnnotationVariant Guard n a b)
    (HS : σ.PreservesTail n m) (HT : τ.PreservesTail n m)
    (H : ∀ i, AnnotationVariant Guard m (σ i) (τ i)) :
    AnnotationVariant Guard m (a.subst σ) (b.subst τ) := by
  induction V generalizing m σ τ with
  | refl => exact .subst_images _ H
  | app _ _ ihf ihx => exact .app (ihf HS HT H) (ihx HS HT H)
  | proj _ ih => exact .proj (ih HS HT H)
  | lam _ _ ihA ihb => exact .lam (ihA HS HT H) (ihb HS.lift HT.lift (lift_images H))
  | forallE _ _ ihA ihB => exact .forallE (ihA HS HT H) (ihB HS.lift HT.lift (lift_images H))
  | marked HG _ ih =>
    simp only [subst, HS.apply_lift, HT.apply_lift]
    exact .marked HG (ih HS.lift HT.lift (lift_images H))

/-- Beta substitution is a special case of protected paired substitution. -/
theorem AnnotationVariant.inst_pair (V : AnnotationVariant Guard (n + 1) a b)
    (H : AnnotationVariant Guard n x y) :
    AnnotationVariant Guard n (a.inst x) (b.inst y) := by
  simp only [inst_eq_subst, Subst.liftN]
  apply V.subst_pair
  · intro i; change ProofShape.bvar (i + n) = ProofShape.bvar (i + n); rfl
  · intro i; change ProofShape.bvar (i + n) = ProofShape.bvar (i + n); rfl
  · intro i; cases i with
    | zero => exact H
    | succ i => exact .refl

/-- Symmetric domain guards reverse the complete paired syntax. -/
theorem AnnotationVariant.symm (hs : ∀ {A C}, Guard A C → Guard C A)
    (V : AnnotationVariant Guard n a b) : AnnotationVariant Guard n b a := by
  induction V with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | marked HG _ ih => exact .marked (hs HG) ih

/-- Every finite beta path has a matching path from the paired term. Changed
annotations retain their ambient certificate; contracting a marked lambda
simply discards that certificate and substitutes the related arguments. -/
theorem AnnotationVariant.beta_left
    (hg : ∀ {A C A'}, Guard A C → BetaRed A A' → Guard A' C)
    (R : BetaRed a a') (V : AnnotationVariant Guard n a b) :
    ∃ b', BetaRed b b' ∧ AnnotationVariant Guard n a' b' := by
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
    | marked HG VB =>
      obtain ⟨A', RA', rfl⟩ := RA.liftN_inv
      obtain ⟨c, Rc, Vc⟩ := ihB VB
      exact ⟨_, .lam .refl Rc, .marked (hg HG RA') Vc⟩
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
      | refl => exact ⟨_, .beta, AnnotationVariant.refl.inst_pair VX⟩
      | lam _ VB => exact ⟨_, .beta, VB.inst_pair VX⟩
      | marked _ VB => exact ⟨_, .beta, VB.inst_pair VX⟩

/-- Independent finite beta paths have further reducts related by the same
annotation certificate grammar. Raw beta confluence suffices; neither endpoint
needs a normal form and the paired endpoints need not computationally join. -/
theorem AnnotationVariant.beta_residuals
    (hs : ∀ {A C}, Guard A C → Guard C A)
    (hg : ∀ {A C A'}, Guard A C → BetaRed A A' → Guard A' C)
    (V : AnnotationVariant Guard n a b) (RA : BetaRed a p) (RB : BetaRed b q) :
    ∃ p' q', BetaRed p p' ∧ BetaRed q q' ∧ AnnotationVariant Guard n p' q' := by
  obtain ⟨b₁, RB₁, V₁⟩ := AnnotationVariant.beta_left (Guard := Guard) hg RA V
  obtain ⟨q', RQ, RB₁'⟩ := RB.raw_confluent RB₁
  obtain ⟨p', RP, V₂⟩ := AnnotationVariant.beta_left (Guard := Guard) hg RB₁' (V₁.symm hs)
  exact ⟨p', q', RP, RQ, V₂.symm hs⟩

/-- A common substitution of ambient variables transforms the stored guards
and both terms together. Local variables remain bound, including beneath
marked lambdas; the substitution may create arbitrary new beta redexes. -/
theorem AnnotationVariant.subst_ambient {Guard' : ProofShape → ProofShape → Prop}
    (hg : ∀ {A C}, Guard A C → Guard' (A.subst σ) (C.subst σ))
    (V : AnnotationVariant Guard n a b) :
    AnnotationVariant Guard' n (a.subst (σ.liftN n)) (b.subst (σ.liftN n)) := by
  induction V with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | marked HG _ ih =>
    simp only [subst, liftN_subst_liftN]
    exact .marked (hg HG) ih

end Lean4Lean.VEnv.Strengthening.ProofShape
