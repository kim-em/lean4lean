import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixKStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationSimulation

/-! # Eliminating full K in favor of prefix unfolding and beta

Full K is simulated by unfolding its function prefix and contracting the new
lambda application. At every finite stage, omitting full K as a primitive leaves
all computations and contextual comparisons unchanged, without increasing stages.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace ProofShape

/-- Every full K step factors as a proof-major prefix step followed by beta.
The proof argument may be any raw shape, including a proof marker. -/
theorem RawCheckedKPrimitive.prefix_compute (H : RawCheckedKPrimitive Step e out) :
    Compute (RawCheckedPrefixKPrimitive Step) e out := by
  cases H with
  | @intro a b v w α M m p HC =>
    have HR : Compute (RawCheckedPrefixKPrimitive Step)
        (eqRecBeforeMajor v w α a M out b) (.lam (eqProofType w α a b) (out.liftN 1)) :=
      .base (.intro HC)
    apply Compute.trans (.app HR (.refl (e := p)))
    apply Compute.beta
    simpa only [inst_eq_subst, Subst.liftN, Subst.one, lift_subst_cons, subst_id] using
      (BetaRed.beta (A := eqProofType w α a b) (b := out.liftN 1) (a := p))
end ProofShape

/-- Finite stages containing only core primitives and proof-major prefix K. -/
def ErasedPrefixOnlyStage (D : PureObservation.Definitions) : Nat → ProofShape → ProofShape → Prop
  | 0 => ErasedIotaPrimitive D
  | stage + 1 => fun a b => ErasedPrefixOnlyStage D stage a b ∨
      ProofShape.RawCheckedPrefixKPrimitive (ErasedPrefixOnlyStage D stage) a b

/-- Omitting full K gives a primitive subrelation of the enriched stages. -/
theorem erased_prefix_only_into : ∀ stage {a b},
    ErasedPrefixOnlyStage D stage a b → ErasedPrefixKStage D stage a b := by
  intro stage
  induction stage with
  | zero => exact id
  | succ stage ih =>
    intro a b H
    rcases H with H | H
    · exact .inl (ih H)
    · cases H with
      | intro HC => exact .inr (.inr (.intro (HC.mono ih)))

/-- Every enriched primitive is a finite prefix-only computation at the same
stage. Endpoint guards are translated recursively at the preceding stage. -/
theorem erased_prefix_K_only_simulation : ∀ stage {a b},
    ErasedPrefixKStage D stage a b → ProofShape.Compute (ErasedPrefixOnlyStage D stage) a b := by
  intro stage
  induction stage with
  | zero => exact fun H => .base H
  | succ stage ih =>
    intro a b H
    rcases H with H | H | H
    · exact (ih H).mono (fun H => .inl H)
    · cases H with
      | intro HC =>
        exact (ProofShape.RawCheckedKPrimitive.prefix_compute (.intro (HC.simulate ih))).mono
          (fun H => .inr H)
    · cases H with
      | intro HC => exact .base (.inr (.intro (HC.simulate ih)))

/-- Removing full K preserves all finite computations, with identical endpoints
and the same stage bound. -/
theorem erased_prefix_only_compute_iff :
    ProofShape.Compute (ErasedPrefixOnlyStage D stage) a b ↔
      ProofShape.Compute (ErasedPrefixKStage D stage) a b :=
  ⟨fun H => H.mono (erased_prefix_only_into stage),
    fun H => H.simulate (erased_prefix_K_only_simulation stage)⟩

/-- The endpoint checking guards are also unchanged at each stage. -/
theorem erased_prefix_only_rawChecked_iff :
    ProofShape.RawCheckedCompare (ErasedPrefixOnlyStage D stage) mode a b ↔
      ProofShape.RawCheckedCompare (ErasedPrefixKStage D stage) mode a b :=
  ⟨fun H => H.mono (erased_prefix_only_into stage),
    fun H => H.simulate (erased_prefix_K_only_simulation stage)⟩

/-- Contextual comparison is unchanged by eliminating full K primitives. -/
theorem erased_prefix_only_context_iff :
    ProofShape.ContextCompare (ErasedPrefixOnlyStage D stage) Δ mode a b ↔
      ProofShape.ContextCompare (ErasedPrefixKStage D stage) Δ mode a b :=
  ⟨fun H => H.mono (erased_prefix_only_into stage),
    fun H => H.simulate (erased_prefix_K_only_simulation stage)⟩

/-- The smaller primitive presentation retains typed descent. -/
theorem erased_prefix_only_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedPrimitiveDescent (ErasedPrefixOnlyStage D stage) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  exact erased_prefix_K_stage_descent heq hs stage hΓ hΓ' W ht (erased_prefix_only_into stage R)

/-- The smaller presentation retains unrestricted raw substitution. -/
theorem erased_prefix_only_subst : ∀ stage {a b} {σ : ProofShape.Subst},
    ErasedPrefixOnlyStage D stage a b → ErasedPrefixOnlyStage D stage (a.subst σ) (b.subst σ) := by
  intro stage
  induction stage with
  | zero => exact fun H => erased_iota_primitive_subst H
  | succ stage ih =>
    intro a b σ H
    exact H.elim (fun H => .inl (ih H)) (fun H => .inr (H.subst ih))

end Lean4Lean.VEnv.Strengthening
