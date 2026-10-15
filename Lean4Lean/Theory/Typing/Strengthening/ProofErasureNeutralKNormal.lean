import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedTransport

/-! # Fixed syntax through every compared-K stage

Core normality alone is insufficient for stage normality. This file supplies the
additional syntactic invariant: every full Eq recursor has distinct bare variables
as its endpoints. The invariant covers all subterms, including annotations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params

namespace ProofShape
/-- Every full Eq recursor in this syntax, including under annotations, has
unequal bare-variable endpoints. Such endpoints never compare in the old language. -/
def NeutralKGuards (e : ProofShape) : Prop :=
  (∀ v w α a M m b p, e = eqRec v w α a M m b p →
    ∃ i j, a = .bvar i ∧ b = .bvar j ∧ i ≠ j) ∧ match e with
  | .app f a => NeutralKGuards f ∧ NeutralKGuards a
  | .proj _ _ m => NeutralKGuards m
  | .lam A b | .forallE A b => NeutralKGuards A ∧ NeutralKGuards b
  | _ => True
end ProofShape

variable [Params]

/-- The full compared-K stages, like the prefix stages, only contract constant
or projection heads. This is independent of any completeness assumption. -/
theorem erased_compared_K_stage_head : ∀ stage {a b}, ErasedComparedKStage D stage a b →
    ProofShape.PrimitiveHead a := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_head
  | succ stage ih =>
    intro a b H
    rcases H with H | H
    · exact ih H
    · cases H; trivial

namespace ProofShape
/-- Unequal variables cannot pass an old compared-K guard at any finite stage. -/
theorem Compare.comparedK_bvar_injective
    (H : Compare (ErasedComparedKStage D stage) mode (.bvar i) (.bvar j)) : i = j := by
  have H' : ScopedCompare (fun _ => ErasedComparedKStage D stage) [] mode (.bvar i) (.bvar j) :=
    H.scoped (fun H => .base H)
  exact H'.bvar_injective (erased_compared_K_stage_head stage)

private theorem NeutralKGuards.no_K (h : NeutralKGuards e)
    (H : ComparedKPrimitive (ErasedComparedKStage D stage) e out) : False := by
  cases H with
  | intro HC =>
    obtain ⟨i, j, rfl, rfl, hne⟩ := h.1 _ _ _ _ _ _ _ _ rfl
    exact hne HC.comparedK_bvar_injective

private theorem normal_add_K (hn : NormalSyntax (ErasedComparedKStage D stage) e)
    (hg : NeutralKGuards e) : NormalSyntax (ErasedComparedKStage D (stage+1)) e := by
  have root {e} (hn : NormalSyntax (ErasedComparedKStage D stage) e)
      (hg : NeutralKGuards e) : ∀ out, ¬ ErasedComparedKStage D (stage+1) e out := by
    intro out H
    exact H.elim hn.no_step hg.no_K
  induction e with
  | app f a ihf iha =>
    exact ⟨root hn hg, hn.2.1, ihf hn.2.2.1 hg.2.1, iha hn.2.2.2 hg.2.2⟩
  | proj s i m ihm => exact ⟨root hn hg, ihm hn.2 hg.2⟩
  | lam A b ihA ihb | forallE A b ihA ihb =>
    exact ⟨root hn hg, ihA hn.2.1 hg.2.1, ihb hn.2.2 hg.2.2⟩
  | bvar | sort | const | proof => exact ⟨root hn hg, trivial⟩

/-- A core-normal term whose every Eq recursor has distinct neutral endpoints
remains normal through every old compared-K stage. In particular, adding more
stages cannot uncover a hidden alternate computation through an annotation. -/
theorem NeutralKGuards.normal_comparedK (hg : NeutralKGuards e)
    (hn : NormalSyntax (ErasedIotaPrimitive D) e) (stage : Nat) :
    NormalSyntax (ErasedComparedKStage D stage) e := by
  induction stage with
  | zero => exact hn
  | succ stage ih => exact normal_add_K ih hg

/-- Under the whole-term hypotheses, every finite old-stage computation has
exactly its starting syntax as endpoint; this excludes all exposure paths. -/
theorem NeutralKGuards.fixed_comparedK (hg : NeutralKGuards e)
    (hn : NormalSyntax (ErasedIotaPrimitive D) e)
    (R : Compute (ErasedComparedKStage D stage) e out) : out = e :=
  (hg.normal_comparedK hn stage).fixed R

end ProofShape
end Lean4Lean.VEnv.Strengthening
