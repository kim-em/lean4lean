import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
import Lean4Lean.Theory.Typing.Strengthening.GuardedKComputation

/-! # Canonical Eq computation on erased proof majors

The equality proof need not retain a constructor shape. Common erased endpoint
computations justify replacing it by reflexivity using source typing. Finite
stages allow earlier erased computations to certify later Eq.rec steps.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

namespace ProofShape
/-- The six-argument canonical Eq recursor in erased syntax. -/
def eqRec (v w : VLevel) (α a M m b p : ProofShape) : ProofShape :=
  .app (.app (.app (.app (.app (.app (.const ``Eq.rec [v, w]) α) a) M) m) b) p

/-- Endpoint computations certify the non-syntactic K match. The proof capture
may be a marker; its actual inhabitant comes from the typed source. -/
inductive KPrimitive (Step : ProofShape → ProofShape → Prop) : ProofShape → ProofShape → Prop where
  | intro : Compute Step a common → Compute Step b common →
      KPrimitive Step (eqRec v w α a M m b p) m
end ProofShape

variable [Params]

/-- Erasing a visible Eq.rec spine retains all six original arguments even
when the proof argument loses its original constructor or variable shape. -/
theorem proofErase_eqRec_inv (H : proofErase Γ e = ProofShape.eqRec v w α a M m b p) :
    ∃ α₀ a₀ M₀ m₀ b₀ p₀, e = eqRecApp v w α₀ a₀ M₀ m₀ b₀ p₀ ∧
      proofErase Γ α₀ = α ∧ proofErase Γ a₀ = a ∧ proofErase Γ M₀ = M ∧
      proofErase Γ m₀ = m ∧ proofErase Γ b₀ = b ∧ proofErase Γ p₀ = p := by
  obtain ⟨f, p₀, rfl, _, Hf, Hp⟩ := erase_app_inv H
  obtain ⟨f, b₀, rfl, _, Hf, Hb⟩ := erase_app_inv Hf
  obtain ⟨f, m₀, rfl, _, Hf, Hm⟩ := erase_app_inv Hf
  obtain ⟨f, M₀, rfl, _, Hf, HM⟩ := erase_app_inv Hf
  obtain ⟨f, a₀, rfl, _, Hf, Ha⟩ := erase_app_inv Hf
  obtain ⟨f, α₀, rfl, _, Hf, Hα⟩ := erase_app_inv Hf
  obtain rfl := erase_const_inv Hf
  exact ⟨α₀, a₀, M₀, m₀, b₀, p₀, rfl, Hα, Ha, HM, Hm, Hb, Hp⟩

/-- Typed descent of the endpoint computations gives typed descent of K. This
is a proof-major primitive beyond syntactic PatternCompute replay. -/
theorem erased_K_descent (heq : env.HasCanonicalEq) (hstep : ErasedPrimitiveDescent Step) :
    ErasedPrimitiveDescent (ProofShape.KPrimitive Step) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  cases R with
  | intro Ra Rb =>
    rw [← proofErase_liftN hΓ hΓ' W ht] at hsrc
    obtain ⟨α', a', M', m', b', p', hs, _, Ha, _, Hm, Hb, _⟩ := proofErase_eqRec_inv hsrc
    rw [← lift'_consN_skipN] at hs
    obtain ⟨α₀, a₀, M₀, m₀, b₀, p₀, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
      lift'_eq_eqRecApp hs
    obtain ⟨_, _, _, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, ht⟩
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W ha] at Ha
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W hb] at Hb
    rw [← Ha] at Ra
    rw [← Hb] at Rb
    have hab := proofErase_typed_join_descend hstep hΓ hΓ' W ha hb Ra Rb
    have HH := eqRecApp_simAt henv heq hΓ ⟨_, hab⟩ T ht
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W HH.hasType.2] at Hm
    exact ⟨m₀, HH, Hm⟩

/-- Finite primitive stages start with visible beta/delta/projection/pattern
computation and then add K guarded by the preceding stage's finite paths. -/
def ErasedKStage (D : PureObservation.Definitions) : Nat → ProofShape → ProofShape → Prop
  | 0 => ErasedIotaPrimitive D
  | stage + 1 => fun a b => ErasedKStage D stage a b ∨ ProofShape.KPrimitive (ErasedKStage D stage) a b

/-- Every finite stage descends from a typed source below binder insertion. -/
theorem erased_K_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedPrimitiveDescent (ErasedKStage D stage) := by
  intro stage
  induction stage with
  | zero => exact ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht R
    exact R.elim (ih hΓ hΓ' W ht) (erased_K_descent heq ih hΓ hΓ' W ht)

/-- Common erased results involving finitely staged proof-major Eq computation
give equality below the inserted binders. No completeness premise is used. -/
theorem proofErase_K_join_descend (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (Ra : ProofShape.Compute (ErasedKStage D stage) (proofErase Γ' (a.liftN n k)) out)
    (Rb : ProofShape.Compute (ErasedKStage D stage) (proofErase Γ' (b.liftN n k)) out) :
    env.IsDefEq univs Γ a b T := by
  rw [proofErase_liftN hΓ hΓ' W ha] at Ra
  rw [proofErase_liftN hΓ hΓ' W hb] at Rb
  exact proofErase_typed_join_descend (erased_K_stage_descent heq hs stage) hΓ hΓ' W ha hb Ra Rb

end Lean4Lean.VEnv.Strengthening
