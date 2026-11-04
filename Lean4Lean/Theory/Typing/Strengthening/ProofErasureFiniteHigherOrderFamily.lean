import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRankedTypeFamily

/-! # Readout for all finite sort-and-function trees

The ranked native hierarchy has no fixed higher-order depth bound. Every finite
syntax tree built from universes and function types has a certificate at some
level, uniformly in its ambient context. Actual typing remains explicit in the
carrier and context conversion consumers.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- Finite type syntax with sort leaves and arbitrary nesting on both sides
of Pi. There are no variable, constant, or application leaves in this fragment. -/
inductive SortPiTree : VExpr → Prop where
  | sort : SortPiTree (.sort u)
  | function : SortPiTree A → SortPiTree B → SortPiTree (.forallE A B)

/-- One level suffices uniformly in every context for a finite syntax tree,
both as a family target and as a native function tree. -/
theorem SortPiTree.coverage [Params] (H : SortPiTree T) :
    ∃ n, ∀ Γ, Ranked n Γ T ∧ Tree (Ranked n) Γ T := by
  induction H with
  | sort => exact ⟨0, fun _ => ⟨.sort, .sort⟩⟩
  | @function A B HA HB ihA ihB =>
    obtain ⟨n, Hn⟩ := ihA
    obtain ⟨m, Hm⟩ := ihB
    refine ⟨max n m + 1, fun Γ => ?_⟩
    have liftN : ∀ {Γ T}, Ranked n Γ T → Ranked (max n m) Γ T :=
      ranked_mono (Nat.le_max_left _ _)
    have liftM : ∀ {Γ T}, Ranked m Γ T → Ranked (max n m) Γ T :=
      ranked_mono (Nat.le_max_right _ _)
    have RA := liftN (Hn Γ).1
    have TA := (Hn Γ).2.mono liftN
    have RB := liftM (Hm (A :: Γ)).1
    have TB := (Hm (A :: Γ)).2.mono liftM
    exact ⟨Extension.native TA (ranked_step _ RB),
      .function (ranked_step _ RA) (TB.mono (fun H => ranked_step _ H))⟩

variable [Params]

/-- Any ordinarily equal source carrier reads at a finite sort/Pi target.
No particular rank or bound on the target's higher-order nesting is assumed. -/
theorem SortPiTree.carrier_convert (HT : SortPiTree T)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ f) (proofErase Γ g) := by
  obtain ⟨n, Hn⟩ := HT.coverage
  exact ranked_carrier_convert (Hn Γ).1 hs hΓ hf hg HE H

/-- Binder conversion to any finite sort/Pi tree transports the full recursive
carrier judgment, with the source's raw carrier and endpoints unchanged. -/
theorem SortPiTree.carrier_context (HT : SortPiTree B)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (B :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  obtain ⟨n, Hn⟩ := HT.coverage
  exact ranked_carrier_context hs hΓ HAB (Hn Γ).2 ha hb H

end Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
