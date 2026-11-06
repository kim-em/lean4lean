import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants

/-! # Protected ambient origins inside arbitrary beta consumers

Local substitutions can duplicate or discard origins but do not change their
ambient variables. Separate annotation marks record lambda domains exposed by
computation inside an origin. The atomic beta interactions are explicit.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private lifted_middle from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants
variable {σ τ : Subst} {Guard Atom : ProofShape → ProofShape → Prop}

/-- An ambient pair occurring beneath a protected local prefix. -/
def LiftedOrigin (Atom : ProofShape → ProofShape → Prop) (n : Nat) (a b : ProofShape) : Prop :=
  ∃ x y, Atom x y ∧ a = x.liftN n ∧ b = y.liftN n

/-- Structural paired terms with protected ambient origins and marked lambda
domains. The depth index protects both from local instantiation. Ordinary
syntax, including annotations and bodies of marked lambdas, remains recursive. -/
inductive AmbientVariant (Guard Atom : ProofShape → ProofShape → Prop) :
    Nat → ProofShape → ProofShape → Prop where
  | refl : AmbientVariant Guard Atom n a a
  | app : AmbientVariant Guard Atom n f g → AmbientVariant Guard Atom n x y →
      AmbientVariant Guard Atom n (.app f x) (.app g y)
  | proj : AmbientVariant Guard Atom n a b → AmbientVariant Guard Atom n (.proj s i a) (.proj s i b)
  | lam : AmbientVariant Guard Atom n A C → AmbientVariant Guard Atom (n + 1) b c →
      AmbientVariant Guard Atom n (.lam A b) (.lam C c)
  | forallE : AmbientVariant Guard Atom n A C → AmbientVariant Guard Atom (n + 1) B E →
      AmbientVariant Guard Atom n (.forallE A B) (.forallE C E)
  | marked : Guard A C → AmbientVariant Guard Atom (n + 1) b c →
      AmbientVariant Guard Atom n (.lam (A.liftN n) b) (.lam (C.liftN n) c)
  | origin : LiftedOrigin Atom n a b → AmbientVariant Guard Atom n a b

/-- Inserting local variables preserves every ambient annotation origin. -/
theorem AmbientVariant.liftN (H : AmbientVariant Guard Atom n a b) (hk : k ≤ n) :
    AmbientVariant Guard Atom (n + m) (a.liftN m k) (b.liftN m k) := by
  induction H generalizing k with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app (ihf hk) (ihx hk)
  | proj _ ih => exact .proj (ih hk)
  | lam _ _ ihA ihb =>
    apply AmbientVariant.lam (ihA hk)
    simpa only [Nat.add_right_comm] using ihb (show k + 1 ≤ _ by omega)
  | forallE _ _ ihA ihB =>
    apply AmbientVariant.forallE (ihA hk)
    simpa only [Nat.add_right_comm] using ihB (show k + 1 ≤ _ by omega)
  | marked HG _ ih =>
    simp only [ProofShape.liftN, lifted_middle _ hk]
    apply AmbientVariant.marked HG
    simpa only [Nat.add_right_comm] using ih (show k + 1 ≤ _ by omega)
  | origin H =>
    obtain ⟨a, b, H, rfl, rfl⟩ := H
    exact .origin ⟨a, b, H, lifted_middle _ hk, lifted_middle _ hk⟩

private theorem lift_images (H : ∀ i, AmbientVariant Guard Atom m (σ i) (τ i)) :
    ∀ i, AmbientVariant Guard Atom (m + 1) (σ.lift i) (τ.lift i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (H i).liftN (Nat.zero_le m)

/-- An arbitrary raw template accepts independently related images. All
occurrences, including occurrences in dependent annotations, are retained. -/
theorem AmbientVariant.subst_images (a : ProofShape)
    (H : ∀ i, AmbientVariant Guard Atom m (σ i) (τ i)) :
    AmbientVariant Guard Atom m (a.subst σ) (a.subst τ) := by
  induction a generalizing m σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app _ _ ihf ihx => exact .app (ihf H) (ihx H)
  | proj _ _ _ ih => exact .proj (ih H)
  | lam _ _ ihA ihb => exact .lam (ihA H) (ihb (lift_images H))
  | forallE _ _ ihA ihB => exact .forallE (ihA H) (ihB (lift_images H))

/-- Paired substitution of local variables preserves the relation. The two
maps may differ throughout the local prefix; only their ambient tails agree. -/
theorem AmbientVariant.subst_pair (V : AmbientVariant Guard Atom n a b)
    (HS : σ.PreservesTail n m) (HT : τ.PreservesTail n m)
    (H : ∀ i, AmbientVariant Guard Atom m (σ i) (τ i)) :
    AmbientVariant Guard Atom m (a.subst σ) (b.subst τ) := by
  induction V generalizing m σ τ with
  | refl => exact .subst_images _ H
  | app _ _ ihf ihx => exact .app (ihf HS HT H) (ihx HS HT H)
  | proj _ ih => exact .proj (ih HS HT H)
  | lam _ _ ihA ihb => exact .lam (ihA HS HT H) (ihb HS.lift HT.lift (lift_images H))
  | forallE _ _ ihA ihB => exact .forallE (ihA HS HT H) (ihB HS.lift HT.lift (lift_images H))
  | marked HG _ ih =>
    simp only [subst, HS.apply_lift, HT.apply_lift]
    exact .marked HG (ih HS.lift HT.lift (lift_images H))
  | origin HO =>
    obtain ⟨a, b, HO, rfl, rfl⟩ := HO
    exact .origin ⟨a, b, HO, HS.apply_lift _, HT.apply_lift _⟩

/-- Beta substitution is a special case of protected paired substitution. -/
theorem AmbientVariant.inst_pair (V : AmbientVariant Guard Atom (n + 1) a b)
    (H : AmbientVariant Guard Atom n x y) :
    AmbientVariant Guard Atom n (a.inst x) (b.inst y) := by
  simp only [inst_eq_subst, Subst.liftN]
  apply V.subst_pair
  · intro i; change ProofShape.bvar (i + n) = ProofShape.bvar (i + n); rfl
  · intro i; change ProofShape.bvar (i + n) = ProofShape.bvar (i + n); rfl
  · intro i; cases i with
    | zero => exact H
    | succ i => exact .refl

/-- Symmetric domain guards reverse the complete paired syntax. -/
theorem AmbientVariant.symm (hs : ∀ {A C}, Guard A C → Guard C A)
    (ha : ∀ {a b}, Atom a b → Atom b a)
    (V : AmbientVariant Guard Atom n a b) : AmbientVariant Guard Atom n b a := by
  induction V with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | marked HG _ ih => exact .marked (hs HG) ih
  | origin HO =>
    obtain ⟨a, b, HO, EA, EB⟩ := HO
    exact .origin ⟨b, a, ha HO, EB, EA⟩

/-- Consumer beta simulation reduces to two atomic interactions: computation
inside a protected origin, and applying an origin whose left endpoint is a
lambda. All duplication and newly created consumer redexes are handled here. -/
theorem AmbientVariant.beta_left
    (hg : ∀ {A C A'}, Guard A C → BetaRed A A' → Guard A' C)
    (ho : ∀ {n a a' b}, LiftedOrigin Atom n a b → BetaRed a a' →
      ∃ b', BetaRed b b' ∧ AmbientVariant Guard Atom n a' b')
    (hap : ∀ {n A body g x y}, LiftedOrigin Atom n (.lam A body) g →
      AmbientVariant Guard Atom n x y → ∃ out, BetaRed (.app g y) out ∧
        AmbientVariant Guard Atom n (body.inst x) out)
    (R : BetaRed a a') (V : AmbientVariant Guard Atom n a b) :
    ∃ b', BetaRed b b' ∧ AmbientVariant Guard Atom n a' b' := by
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
    | origin HO => exact ho HO (.app RF RX)
  | proj R ih =>
    cases V with
    | refl => exact ⟨_, .proj R, .refl⟩
    | proj V =>
      obtain ⟨b, RB, VB⟩ := ih V
      exact ⟨_, .proj RB, .proj VB⟩
    | origin HO => exact ho HO (.proj R)
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
    | origin HO => exact ho HO (.lam RA RB)
  | forallE RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨c, Rc, Vc⟩ := ihB VB
      exact ⟨_, .forallE RC Rc, .forallE VC Vc⟩
    | origin HO => exact ho HO (.forallE RA RB)
  | beta =>
    cases V with
    | refl => exact ⟨_, .beta, .refl⟩
    | origin HO => exact ho HO .beta
    | app VF VX =>
      cases VF with
      | refl => exact ⟨_, .beta, AmbientVariant.refl.inst_pair VX⟩
      | lam _ VB => exact ⟨_, .beta, VB.inst_pair VX⟩
      | marked _ VB => exact ⟨_, .beta, VB.inst_pair VX⟩
      | origin HO => exact hap HO VX

/-- The two proved atomic interactions suffice for independent beta residuals.
Only ordinary raw beta confluence is used to align the simulated paths. -/
theorem AmbientVariant.beta_residuals
    (hs : ∀ {A C}, Guard A C → Guard C A)
    (ha : ∀ {a b}, Atom a b → Atom b a)
    (hg : ∀ {A C A'}, Guard A C → BetaRed A A' → Guard A' C)
    (ho : ∀ {n a a' b}, LiftedOrigin Atom n a b → BetaRed a a' →
      ∃ b', BetaRed b b' ∧ AmbientVariant Guard Atom n a' b')
    (hap : ∀ {n A body g x y}, LiftedOrigin Atom n (.lam A body) g →
      AmbientVariant Guard Atom n x y → ∃ out, BetaRed (.app g y) out ∧
        AmbientVariant Guard Atom n (body.inst x) out)
    (V : AmbientVariant Guard Atom n a b) (RA : BetaRed a p) (RB : BetaRed b q) :
    ∃ p' q', BetaRed p p' ∧ BetaRed q q' ∧ AmbientVariant Guard Atom n p' q' := by
  obtain ⟨b₁, RB₁, V₁⟩ := AmbientVariant.beta_left (Guard := Guard) (Atom := Atom)
    (fun H R => hg H R) (fun H R => ho H R) (fun H V => hap H V) RA V
  obtain ⟨q', RQ, RB₁'⟩ := RB.raw_confluent RB₁
  obtain ⟨p', RP, V₂⟩ := AmbientVariant.beta_left (Guard := Guard) (Atom := Atom)
    (fun H R => hg H R) (fun H R => ho H R) (fun H V => hap H V) RB₁' (V₁.symm hs ha)
  exact ⟨p', q', RP, RQ, V₂.symm hs ha⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
