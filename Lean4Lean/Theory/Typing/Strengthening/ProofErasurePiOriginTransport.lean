import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiOriginObservation

/-! # Transporting marked Pi observations through typed computation

The computational induction exposes individual root beta contractions. All
control frames are handled uniformly; only literal Pi component computation
needs a payload-specific closure law in the original context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.PiOriginObservation
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

namespace ProofShape
/-- Computational induction with a single root-beta case. Child computation
certificates remain available for typed replay and payload-specific callbacks. -/
theorem ScopedCompute.rootBeta_induction
    {motive : (Δ : List ProofShape) → (a b : ProofShape) → ScopedCompute Step Δ a b → Prop}
    (R : ScopedCompute Step Δ source out)
    (refl : ∀ {Δ e}, motive Δ e e .refl)
    (base : ∀ {Δ e out} (H : Step Δ e out), motive Δ e out (.base H))
    (beta : ∀ {Δ A b a}, motive Δ (.app (.lam A b) a) (b.inst a) (.beta .beta))
    (trans : ∀ {Δ a b c} (R : ScopedCompute Step Δ a b) (S : ScopedCompute Step Δ b c),
      motive Δ a b R → motive Δ b c S → motive Δ a c (.trans R S))
    (app : ∀ {Δ f f' a a'} (R : ScopedCompute Step Δ f f') (S : ScopedCompute Step Δ a a'),
      motive Δ f f' R → motive Δ a a' S → motive Δ (.app f a) (.app f' a') (.app R S))
    (proj : ∀ {Δ m m' s i} (R : ScopedCompute Step Δ m m'), motive Δ m m' R →
      motive Δ (.proj s i m) (.proj s i m') (.proj R))
    (lam : ∀ {Δ A A' b b'} (R : ScopedCompute Step Δ A A') (S : ScopedCompute Step (A :: Δ) b b'),
      motive Δ A A' R → motive (A :: Δ) b b' S → motive Δ (.lam A b) (.lam A' b') (.lam R S))
    (forallE : ∀ {Δ A A' B B'} (R : ScopedCompute Step Δ A A') (S : ScopedCompute Step (A :: Δ) B B'),
      motive Δ A A' R → motive (A :: Δ) B B' S → motive Δ (.forallE A B) (.forallE A' B') (.forallE R S)) :
    motive Δ source out R := by
  induction R with
  | base H => exact base H
  | @beta e out Δ H =>
    induction H generalizing Δ with
    | refl => exact refl
    | trans R S ihR ihS => exact trans (.beta R) (.beta S) ihR ihS
    | beta => exact beta
    | app R S ihR ihS => exact app (.beta R) (.beta S) ihR ihS
    | proj R ihR => exact proj (.beta R) ihR
    | lam R S ihR ihS => exact lam (.beta R) (.beta S) ihR ihS
    | forallE R S ihR ihS => exact forallE (.beta R) (.beta S) ihR ihS
  | trans R S ihR ihS => exact trans R S ihR ihS
  | app R S ihR ihS => exact app R S ihR ihS
  | proj R ihR => exact proj R ihR
  | lam R S ihR ihS => exact lam R S ihR ihS
  | forallE R S ihR ihS => exact forallE R S ihR ihS
end ProofShape

variable [Params]
/-- Every expanded primitive preserves the marked payload directly. Opaque
heads and literal sort roots are excluded by the observation derivation. -/
theorem erased_expansion_stage_piOriginObservation : ∀ stage {Δ a b P n S o},
    ErasedExpansionStage D stage Δ a b → Obs P n S a o → Obs P n S b o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b P n S o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const => exact (H.not_primitiveHead trivial).elim
    · cases R
      exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b P n S o R H
    rcases R with R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · cases R
      exact H.identity_expansion

/-- Unbounded finite guard depth preserves the same marked Pi observation. -/
theorem erased_expansion_union_piOriginObservation
    (R : ErasedExpansionUnion D Δ a b) (H : Obs P n S a o) : Obs P n S b o := by
  obtain ⟨stage, R⟩ := R
  exact erased_expansion_stage_piOriginObservation stage R H

/-- A payload closure law handles just component computation of a literal Pi
lifted through an arbitrary well-formed prefix. It retains exact raw outputs. -/
def PiOriginComponentClosure (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ : List VExpr) (P : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ' n A B X Y}, OnCtx Γ' (env.IsType univs) → Ctx.LiftN n 0 Γ Γ' → P A B →
    ScopedCompute Step (proofEraseCtx Γ') (A.liftN n) X →
    ScopedCompute Step (A.liftN n :: proofEraseCtx Γ') (B.liftN n 1) Y →
    ∃ A' B', P A' B' ∧ X = A'.liftN n ∧ Y = B'.liftN n 1

/-- Typed computation preserves marked observations whenever literal Pi
components preserve their histories. Control applications, beta contractions,
changing lambda annotations and temporary binders need no further premise. -/
theorem proofErase_scoped_compute_piOriginObservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b n S o}, Step Δ a b → Obs P n S a o → Obs P n S b o)
    (hpi : PiOriginComponentClosure Step Γ P)
    (R : ScopedCompute Step Δ source out)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (ht : env.HasType univs Γ' e T) (EΓ : proofEraseCtx Γ' = Δ) (Ee : proofErase Γ' e = source)
    (H : Obs P n S source o) : Obs P n S out o := by
  induction R using ScopedCompute.rootBeta_induction generalizing Γ' n S o e T with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ' ht EΓ Ee R₁
    exact ih₂ hΓ' W HE.hasType.2 EΓ EE (ih₁ hΓ' W ht EΓ Ee H)
  | app RF RX ihf ihx =>
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ'
    obtain ⟨keys, HF, HX⟩ := H.app_inv
    exact .app (ihf hΓ' W hf EΓ Ef HF) (fun key hk => ihx hΓ' W hx EΓ Ex (HX key hk))
  | proj => exact H.not_proj.elim
  | lam RA RB ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ'
    obtain ⟨keys, result, rfl, HB⟩ := H.lam_inv
    have hΓA : OnCtx (A :: Γ') (env.IsType univs) := ⟨hΓ', u, hA⟩
    have W' : Ctx.LiftN (n+1) 0 Γ (A :: Γ') := W.comp (by omega) (by omega) Ctx.LiftN.one
    apply Obs.lam
    exact ihb hΓA W' hb (by simp only [proofEraseCtx, EA, EΓ]) Eb HB
  | forallE RA RB =>
    obtain ⟨rfl, A, B, HP, rfl, rfl⟩ := H.forallE_inv
    obtain ⟨A', B', HP', EX, EY⟩ := hpi hΓ' W HP (EΓ ▸ RA) (EΓ ▸ RB)
    rw [EX, EY]
    exact Obs.payload HP'

end Lean4Lean.VEnv.Strengthening
