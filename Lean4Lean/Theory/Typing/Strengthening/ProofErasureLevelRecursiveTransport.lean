import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFixedTailReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreBetaSquare

/-! # Comparisons whose references may continue computing

Typed join leaves may reduce indefinitely. Fixed comparison leaves preserve
eta differences without requiring a common reduct. Pi and lambda frames combine
these two behaviors, with independent computation in every component. Coverage
of arbitrary checking certificates, especially reducible applications, remains
open; no forward-transport oracle is a constructor of this fragment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A recursive level-core comparison fragment. Fixedness is required only at
comparison leaves, not at join leaves or enclosing binders. Leaf typings are
actual witnesses used for confluence and universe-return arguments; the raw
comparison conclusion can subsequently be embedded at any checking context. -/
inductive LevelRecursiveGuard (D : Definitions) : Bool → ProofShape → ProofShape → Prop where
  | join (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (HJ : ComputeJoin (ErasedLevelCore D) (proofErase Γ a) (proofErase Γ b)) :
      LevelRecursiveGuard D mode (proofErase Γ a) (proofErase Γ b)
  | fixed (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (HA : ComputeFixed (ErasedIotaPrimitive D) (proofErase Γ a))
      (HB : ComputeFixed (ErasedIotaPrimitive D) (proofErase Γ b))
      (H : RawCheckedCompare (ErasedLevelCore D) mode (proofErase Γ a) (proofErase Γ b)) :
      LevelRecursiveGuard D mode (proofErase Γ a) (proofErase Γ b)
  | lam : LevelRecursiveGuard D false A A' → LevelRecursiveGuard D mode b b' →
      LevelRecursiveGuard D mode (.lam A b) (.lam A' b')
  | lamCommon : LevelRecursiveGuard D true b b' →
      LevelRecursiveGuard D true (.lam A b) (.lam A' b')
  | forallE : LevelRecursiveGuard D false A A' → LevelRecursiveGuard D false B B' →
      LevelRecursiveGuard D mode (.forallE A B) (.forallE A' B')
  | compute (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (HA : Compute (ErasedLevelCore D) (proofErase Γ a) a')
      (HB : Compute (ErasedLevelCore D) (proofErase Γ b) b')
      (H : LevelRecursiveGuard D mode a' b') :
      LevelRecursiveGuard D mode (proofErase Γ a) (proofErase Γ b)
  | symm : LevelRecursiveGuard D mode a b → LevelRecursiveGuard D mode b a

/-- Independent level-core paths preserve comparison for the recursive
fragment. Typed confluence handles evolving join leaves; fixed leaves return
locally. Neither entire endpoint must normalize, return, or join the other. -/
theorem LevelRecursiveGuard.forward
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode a b)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    RawCheckedCompare (ErasedLevelCore D) mode a' b' := by
  induction H generalizing a' b' with
  | join hΓ ha hb HJ =>
    have H := (ComputeJoin.of_compute RA).symm.trans_typed hc hΓ ha HJ
    obtain ⟨shared, RL, RR⟩ := H.trans_typed hc hΓ hb (.of_compute RB)
    exact .compute RL RR (.base .refl)
  | fixed hΓ ha hb HA HB H =>
    have RL := proofErase_fixed_core_join_return hs hl hcon hΓ ha HA
      (ComputeJoin.of_compute RA).symm
    have RR := proofErase_fixed_core_join_return hs hl hcon hΓ hb HB
      (ComputeJoin.of_compute RB).symm
    exact .compute RL RR H
  | lam _ _ ihA ihb =>
    obtain ⟨_, _, rfl, RA, Ra⟩ := RA.level_core_lam_inv
    obtain ⟨_, _, rfl, RB, Rb⟩ := RB.level_core_lam_inv
    exact .lam (ihA RA RB) (ihb Ra Rb)
  | lamCommon _ ih =>
    obtain ⟨_, _, rfl, _, Ra⟩ := RA.level_core_lam_inv
    obtain ⟨_, _, rfl, _, Rb⟩ := RB.level_core_lam_inv
    exact .lamCommon (ih Ra Rb)
  | forallE _ _ ihA ihB =>
    obtain ⟨_, _, rfl, RA, Ra⟩ := RA.pi_parts (fun H => erased_level_core_no_pi H)
    obtain ⟨_, _, rfl, RB, Rb⟩ := RB.pi_parts (fun H => erased_level_core_no_pi H)
    exact .forallE (ihA RA RB) (ihB Ra Rb)
  | compute hΓ ha hb HA HB _ ih =>
    obtain ⟨left, RL, HL⟩ := hc hΓ ha RA HA
    obtain ⟨right, RR, HR⟩ := hc hΓ hb RB HB
    exact .compute RL RR (ih HL HR)
  | symm _ ih => exact (ih RB RA).symm

/-- Reference joins suffice to transport a recursive comparison even when
neither join can return to its original reference. Both references evolve to
their respective joining points before the recursive forward theorem applies. -/
theorem LevelRecursiveGuard.of_joins
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode a b)
    (HA : ComputeJoin (ErasedLevelCore D) outA a)
    (HB : ComputeJoin (ErasedLevelCore D) outB b) :
    RawCheckedCompare (ErasedLevelCore D) mode outA outB := by
  obtain ⟨left, RL, RA⟩ := HA
  obtain ⟨right, RR, RB⟩ := HB
  exact .compute RL RR (H.forward hs hl hcon hc RA RB)

end Lean4Lean.VEnv.Strengthening
