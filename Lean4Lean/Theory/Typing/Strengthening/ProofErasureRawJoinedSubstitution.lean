import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawJoinedApplication

/-! # Paired raw body substitution with computationally joined arguments

The common raw reduct can be substituted without a typing or recovery oracle.
Both instantiated bodies compute to that shared substitution, where the original
body certificate applies. This avoids a comparison-composition hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape
variable [Params]

omit [Params] in
/-- A fixed raw body computes pointwise with its substituted argument. -/
theorem Compute.inst_argument
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (R : Compute Step x y) (b : ProofShape) : Compute Step (b.inst x) (b.inst y) := by
  simp only [inst_eq_subst, Subst.liftN]
  apply Compute.subst_images hweak
  intro i
  cases i with
  | zero => exact R
  | succ i => exact .refl

/-- Paired raw bodies may substitute different arguments when those arguments
have a literal computational join. Modes are preserved, and the join need not
have any original representative for this syntactic theorem. -/
theorem RawCheckedCompare.inst_join
    (hsubst : ∀ {a b} {τ : Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (HB : RawCheckedCompare Step mode b b')
    (RX : Compute Step x shared) (RY : Compute Step y shared) :
    RawCheckedCompare Step mode (b.inst x) (b'.inst y) := by
  apply RawCheckedCompare.compute (RX.inst_argument hweak b) (RY.inst_argument hweak b')
  simpa only [inst_eq_subst, Subst.liftN] using HB.subst hsubst (σ := Subst.one shared)
end ProofShape
variable [Params]

/-- Typed body certificates instantiate with different computationally joined
arguments, retaining a raw certificate in the lower context and its original
mode. No common composition or target recovery assumption is required. -/
theorem proofErase_raw_inst_join
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hweak : ∀ {a b n k}, Step a b → Step (a.liftN n k) (b.liftN n k))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hb' : env.HasType univs (A :: Γ) b' B')
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HB : ProofShape.RawCheckedCompare Step mode (proofErase (A :: Γ) b) (proofErase (A :: Γ) b'))
    (RX : ProofShape.Compute Step (proofErase Γ x) shared)
    (RY : ProofShape.Compute Step (proofErase Γ y) shared) :
    ProofShape.RawCheckedCompare Step mode (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) := by
  rw [proofErase_instN hΓA hx .zero hb, proofErase_instN hΓA hy .zero hb']
  exact HB.inst_join hsubst hweak RX RY

/-- Prefix-only primitives weaken at every finite stage. -/
theorem erased_prefix_only_liftN : ∀ stage {a b n k}, ErasedPrefixOnlyStage D stage a b →
    ErasedPrefixOnlyStage D stage (a.liftN n k) (b.liftN n k) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_liftN H
  | succ stage ih =>
    intro a b n k H
    exact H.elim (fun H => .inl (ih H)) (fun H => .inr (H.liftN ih))

/-- Joined-argument paired instantiation holds at every prefix-only stage without
increasing the stage bound, including for inferred body certificates. -/
theorem proofErase_prefix_only_raw_inst_join
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hb' : env.HasType univs (A :: Γ) b' B')
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HB : ProofShape.RawCheckedCompare (ErasedPrefixOnlyStage D stage) mode
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) b'))
    (RX : ProofShape.Compute (ErasedPrefixOnlyStage D stage) (proofErase Γ x) shared)
    (RY : ProofShape.Compute (ErasedPrefixOnlyStage D stage) (proofErase Γ y) shared) :
    ProofShape.RawCheckedCompare (ErasedPrefixOnlyStage D stage) mode
      (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) :=
  proofErase_raw_inst_join (fun H => erased_prefix_only_subst stage H)
    (fun H => erased_prefix_only_liftN stage H) hΓA hb hb' hx hy HB RX RY

end Lean4Lean.VEnv.Strengthening
