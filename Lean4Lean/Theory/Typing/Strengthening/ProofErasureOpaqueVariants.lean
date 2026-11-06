import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines

/-! # Protected opaque occurrences in arbitrary consumers

A marked ambient term may be replaced by an arbitrary payload. The relation
tracks every occurrence through local substitution and beta duplication. It is
directed: a payload may expose a new head that was blocked by its source.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private lifted_middle from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariants
variable {σ τ : Subst} {Guard : ProofShape → ProofShape → Prop}

private theorem head_lift (a : ProofShape) : (a.liftN n k).constHead = a.constHead := by
  induction a generalizing k with
  | app _ _ ih _ => exact ih
  | bvar => simp [ProofShape.liftN, constHead]
  | _ => rfl

/-- Paired syntax with protected ambient opaque terms on the left. The guard
records the source and replacement; local substitution cannot alter either
ambient origin. Opaqueness is imposed by the simulation theorem, not by this
pure structural relation. -/
inductive OpaqueVariant (Guard : ProofShape → ProofShape → Prop) :
    Nat → ProofShape → ProofShape → Prop where
  | refl : OpaqueVariant Guard n a a
  | app : OpaqueVariant Guard n f g → OpaqueVariant Guard n x y →
      OpaqueVariant Guard n (.app f x) (.app g y)
  | proj : OpaqueVariant Guard n a b → OpaqueVariant Guard n (.proj s i a) (.proj s i b)
  | lam : OpaqueVariant Guard n A C → OpaqueVariant Guard (n + 1) b c →
      OpaqueVariant Guard n (.lam A b) (.lam C c)
  | forallE : OpaqueVariant Guard n A C → OpaqueVariant Guard (n + 1) B E →
      OpaqueVariant Guard n (.forallE A B) (.forallE C E)
  | marked : Guard a b → OpaqueVariant Guard n (a.liftN n) (b.liftN n)

/-- Inserting local variables preserves every ambient marked origin. -/
theorem OpaqueVariant.liftN (H : OpaqueVariant Guard n a b) (hk : k ≤ n) :
    OpaqueVariant Guard (n + m) (a.liftN m k) (b.liftN m k) := by
  induction H generalizing k with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app (ihf hk) (ihx hk)
  | proj _ ih => exact .proj (ih hk)
  | lam _ _ ihA ihb =>
    apply OpaqueVariant.lam (ihA hk)
    simpa only [Nat.add_right_comm] using ihb (show k + 1 ≤ _ by omega)
  | forallE _ _ ihA ihB =>
    apply OpaqueVariant.forallE (ihA hk)
    simpa only [Nat.add_right_comm] using ihB (show k + 1 ≤ _ by omega)
  | marked HG => simp only [lifted_middle _ hk]; exact .marked HG

private theorem lift_images (H : ∀ i, OpaqueVariant Guard m (σ i) (τ i)) :
    ∀ i, OpaqueVariant Guard (m + 1) (σ.lift i) (τ.lift i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (H i).liftN (Nat.zero_le m)

/-- An arbitrary raw template accepts independently related images. All
occurrences, including occurrences in dependent annotations, are retained. -/
theorem OpaqueVariant.subst_images (a : ProofShape)
    (H : ∀ i, OpaqueVariant Guard m (σ i) (τ i)) :
    OpaqueVariant Guard m (a.subst σ) (a.subst τ) := by
  induction a generalizing m σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app _ _ ihf ihx => exact .app (ihf H) (ihx H)
  | proj _ _ _ ih => exact .proj (ih H)
  | lam _ _ ihA ihb => exact .lam (ihA H) (ihb (lift_images H))
  | forallE _ _ ihA ihB => exact .forallE (ihA H) (ihB (lift_images H))

/-- Paired substitution of local variables preserves the relation. The two
maps may differ throughout the local prefix; only their ambient tails agree. -/
theorem OpaqueVariant.subst_pair (V : OpaqueVariant Guard n a b)
    (HS : σ.PreservesTail n m) (HT : τ.PreservesTail n m)
    (H : ∀ i, OpaqueVariant Guard m (σ i) (τ i)) :
    OpaqueVariant Guard m (a.subst σ) (b.subst τ) := by
  induction V generalizing m σ τ with
  | refl => exact .subst_images _ H
  | app _ _ ihf ihx => exact .app (ihf HS HT H) (ihx HS HT H)
  | proj _ ih => exact .proj (ih HS HT H)
  | lam _ _ ihA ihb => exact .lam (ihA HS HT H) (ihb HS.lift HT.lift (lift_images H))
  | forallE _ _ ihA ihB => exact .forallE (ihA HS HT H) (ihB HS.lift HT.lift (lift_images H))
  | marked HG => simpa only [HS.apply_lift, HT.apply_lift] using (OpaqueVariant.marked (n := m) HG)

/-- Beta substitution is a special case of protected paired substitution. -/
theorem OpaqueVariant.inst_pair (V : OpaqueVariant Guard (n + 1) a b)
    (H : OpaqueVariant Guard n x y) :
    OpaqueVariant Guard n (a.inst x) (b.inst y) := by
  simp only [inst_eq_subst, Subst.liftN]
  apply V.subst_pair
  · intro i; change ProofShape.bvar (i + n) = ProofShape.bvar (i + n); rfl
  · intro i; change ProofShape.bvar (i + n) = ProofShape.bvar (i + n); rfl
  · intro i; cases i with
    | zero => exact H
    | succ i => exact .refl

private theorem lam_parts
    (hh : ∀ {a b}, Guard a b → a.constHead = some c)
    (V : OpaqueVariant Guard n (.lam A b) out) :
    ∃ C d, out = .lam C d ∧ OpaqueVariant Guard n A C ∧ OpaqueVariant Guard (n+1) b d := by
  generalize E : ProofShape.lam A b = source at V
  cases V with
  | refl => cases E; exact ⟨_, _, rfl, .refl, .refl⟩
  | lam VA VB => cases E; exact ⟨_, _, rfl, VA, VB⟩
  | marked HG =>
    have H := congrArg constHead E
    rw [head_lift, hh HG] at H
    cases H
  | app | proj | forallE => cases E

/-- A left beta path is simulated when marked sources have a constant head
and the guard retains their own beta reducts. Redexes newly exposed on the
payload side are deliberately left for a later confluence argument. -/
theorem OpaqueVariant.beta_left
    (hh : ∀ {a b}, Guard a b → a.constHead = some c)
    (hg : ∀ {a b a'}, Guard a b → BetaRed a a' → Guard a' b)
    (R : BetaRed a a') (V : OpaqueVariant Guard n a b) :
    ∃ b', BetaRed b b' ∧ OpaqueVariant Guard n a' b' := by
  induction R generalizing n b with
  | refl => exact ⟨_, .refl, V⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨b₁, RB, V₁⟩ := ih₁ V
    obtain ⟨b₂, RC, V₂⟩ := ih₂ V₁
    exact ⟨b₂, RB.trans RC, V₂⟩
  | @app f f' x x' RF RX ihf ihx =>
    generalize E : ProofShape.app f x = source at V
    cases V with
    | refl => cases E; exact ⟨_, .app RF RX, .refl⟩
    | app VF VX =>
      cases E
      obtain ⟨g, RG, VG⟩ := ihf VF
      obtain ⟨y, RY, VY⟩ := ihx VX
      exact ⟨_, .app RG RY, .app VG VY⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ BetaRed.app RF RX).liftN_inv
      refine ⟨_, .refl, ?_⟩
      rw [EO]
      exact .marked (hg HG RA')
    | proj | lam | forallE => cases E
  | @proj m m' s i R ih =>
    generalize E : ProofShape.proj s i m = source at V
    cases V with
    | refl => cases E; exact ⟨_, .proj R, .refl⟩
    | proj V =>
      cases E
      obtain ⟨b, RB, VB⟩ := ih V
      exact ⟨_, .proj RB, .proj VB⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ BetaRed.proj R).liftN_inv
      refine ⟨_, .refl, ?_⟩
      rw [EO]
      exact .marked (hg HG RA')
    | app | lam | forallE => cases E
  | lam RA RB ihA ihB =>
    obtain ⟨C, d, rfl, VA, VB⟩ := lam_parts hh V
    obtain ⟨C', RC, VC⟩ := ihA VA
    obtain ⟨d', RD, VD⟩ := ihB VB
    exact ⟨_, .lam RC RD, .lam VC VD⟩
  | @forallE A A' B B' RA RB ihA ihB =>
    generalize E : ProofShape.forallE A B = source at V
    cases V with
    | refl => cases E; exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      cases E
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨d, RD, VD⟩ := ihB VB
      exact ⟨_, .forallE RC RD, .forallE VC VD⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ BetaRed.forallE RA RB).liftN_inv
      refine ⟨_, .refl, ?_⟩
      rw [EO]
      exact .marked (hg HG RA')
    | app | proj | lam => cases E
  | @beta A body x =>
    generalize E : ProofShape.app (.lam A body) x = source at V
    cases V with
    | refl => cases E; exact ⟨_, .beta, .refl⟩
    | app VF VX =>
      cases E
      obtain ⟨C, d, rfl, _, VB⟩ := lam_parts hh VF
      exact ⟨_, .beta, VB.inst_pair VX⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ BetaRed.beta).liftN_inv
      refine ⟨_, .refl, ?_⟩
      rw [EO]
      exact .marked (hg HG RA')

    | proj | lam | forallE => cases E

end Lean4Lean.VEnv.Strengthening.ProofShape
