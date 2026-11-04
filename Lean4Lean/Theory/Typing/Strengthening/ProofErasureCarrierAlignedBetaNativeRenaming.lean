import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJoinedNativeContext

/-! # Raw variable renaming for beta-only native recovery

The native grammar needs exact oracle lookups under variable renaming, but no
interpreted context substitution. This permits raw joined images to extend
under every displayed binder, including impure target annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
namespace ProofShape

/-- A variable renaming whose lifted type lookups agree exactly. -/
def RawOracleRenaming (Δ Δ' : List ProofShape) (τ : Subst) : Prop :=
  ∀ i, ∃ j, τ i = .bvar j ∧ contextOracle Δ' j = (contextOracle Δ i).subst τ

/-- Raw oracle renamings extend beneath any displayed annotation. -/
theorem RawOracleRenaming.cons (W : RawOracleRenaming Δ Δ' τ) :
    RawOracleRenaming (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  intro i
  cases i with
  | zero =>
    refine ⟨0, rfl, ?_⟩
    simp only [contextOracle, TypeOracle.cons, lift_subst_lift]
  | succ i =>
    obtain ⟨j, Ej, ET⟩ := W i
    refine ⟨j+1, ?_, ?_⟩
    · simp [Subst.lift, Ej, ProofShape.liftN, liftVar, Nat.add_comm]
    · simp only [contextOracle, TypeOracle.cons, lift_subst_lift] at ET ⊢
      exact congrArg (·.liftN 1) ET

/-- A computation with no primitive roots is precisely a beta path. -/
theorem ScopedCompute.beta_only (R : ScopedCompute (fun _ _ _ => False) Δ a b) : BetaRed a b := by
  induction R with
  | base H => exact H.elim
  | beta R => exact R
  | trans _ _ ihR ihS => exact ihR.trans ihS
  | app _ _ ihR ihS => exact .app ihR ihS
  | lam _ _ ihR ihS => exact .lam ihR ihS
  | forallE _ _ ihR ihS => exact .forallE ihR ihS
  | proj _ ih => exact .proj ih

variable [Params]
/-- Beta-only native recovery renames using just exact raw oracle lookup.
Constants and projection recipes use their existing closedness/substitution laws. -/
theorem ScopedTypeRecovery.beta_rename
    (R : ScopedTypeRecovery (fun _ _ _ => False) Δ e T) (W : RawOracleRenaming Δ Δ' τ) :
    ScopedTypeRecovery (fun _ _ _ => False) Δ' (e.subst τ) (T.subst τ) := by
  induction R generalizing Δ' τ with
  | bvar =>
    rename_i Δ i
    obtain ⟨j, Ej, ET⟩ := W i
    simp only [ProofShape.subst, Ej, ← ET]
    exact .bvar
  | sort hu => exact .sort hu
  | const hc hw hn =>
    rw [proofErase_closed_subst ((henv.ordered.closedC hc).instL)]
    exact .const hc hw hn
  | lam _ ih => exact .lam (ih W.cons)
  | app _ ih => rw [subst_inst]; exact .app (ih W)
  | forallE _ _ ihA ihB => exact .forallE (ihA W) (ihB W.cons)
  | proj hi HT hj hlen _ ih =>
    have HR' := ih W
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at HR'
    rw [ProofShape.projectionType_subst HT hj (by omega)]
    exact .proj hi HT hj (by simpa only [List.length_map] using hlen) HR'
  | convert _ RC ih => exact .convert (ih W) (.beta RC.beta_only.subst)

open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- Beta-only native recovery weakens under an arbitrary raw binder. No typing
or purity of the inserted annotation is required. -/
theorem ScopedTypeRecovery.beta_weak
    (R : ScopedTypeRecovery (fun _ _ _ => False) Δ e T) :
    ScopedTypeRecovery (fun _ _ _ => False) (A :: Δ) (e.liftN 1) (T.liftN 1) := by
  have W : RawOracleRenaming Δ (A :: Δ) (fun i => .bvar (liftVar 1 i 0)) := by
    intro i
    refine ⟨i+1, ?_, ?_⟩
    · simp [liftVar, Nat.add_comm]
    · simp only [contextOracle, TypeOracle.cons, subst_bvar_liftN]
  simpa only [subst_bvar_liftN] using R.beta_rename W

end ProofShape
end Lean4Lean.VEnv.Strengthening
