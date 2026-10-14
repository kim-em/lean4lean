import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextPrefixFixed

/-! # Typed contextual nontransitivity before the proof major

The cast and constant motives disagree away from the supplied endpoint. Their
fixed partial recursors cannot compare, although both compare through a shared
lambda at a common type. Thus typed primitive descent and substitution stability
alone do not imply contextual composition. This concerns certificate completeness,
not strengthening of original equality.
-/
namespace Lean4Lean.VEnv.Strengthening.ContextPrefixWitness
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The two motives are not definitionally equal. A propositional equality proof
at an alternative Pi endpoint does not make that Pi definitionally equal to Sort. -/
theorem motives_not_defeq (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ env.IsDefEq univs Γ dependentMotive constantMotive motiveType := by
  intro H
  let Y : VExpr := .forallE point point
  have hY : env.HasType univs Γ Y (.sort level) := by
    exact (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  let Q := eqApp (.succ level) (.sort level) point Y
  have hQ : env.HasType univs Γ Q (.sort .zero) :=
    HasType.eqApp heq (by trivial) (.sort (by trivial)) (.sort (by trivial)) hY
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hp : env.HasType univs (Q :: Γ) (.bvar 0) Q := by
    have hp : env.HasType univs (Q :: Γ) (.bvar 0) Q.lift := .bvar .zero
    simpa [Q, Y, eqApp, point, lift, liftN] using hp
  have hY' : env.HasType univs (Q :: Γ) Y (.sort level) := by
    simpa [Y, point, lift, liftN] using (hY.weak henv (B := Q)).hasType.1
  have HM : env.IsDefEq univs (Q :: Γ) dependentMotive constantMotive motiveType := by
    simpa [dependentMotive, constantMotive, motiveType, castMotive, constantEqMotive,
      eqApp, point, lift, liftN] using H.weak henv (B := Q)
  have H1 := IsDefEq.appDF HM hY'
  have H1' : env.IsDefEq univs (Q :: Γ) (.app dependentMotive Y) (.app constantMotive Y)
      (.forallE Q (.sort level)) := by
    simpa [motiveType, inst, instVar, eqApp, point, Q, Y, liftN] using H1
  have H2 := IsDefEq.appDF H1' hp
  have HL := IsDefEq.castMotive_app henv.ordered heq (by trivial)
    (show env.HasType univs (Q :: Γ) point (.sort level) from .sort (by trivial)) hY' hp
  have HR := constantEqMotive_app henv heq (by trivial) hΓQ
    (show env.HasType univs (Q :: Γ) (.sort level) (.sort (.succ level)) from .sort (by trivial))
    (show env.HasType univs (Q :: Γ) point (.sort level) from .sort (by trivial))
    (show env.HasType univs (Q :: Γ) point (.sort level) from .sort (by trivial)) hY' hp
  have HE : env.IsDefEq univs (Q :: Γ) Y point (.sort level) := HL.symm.trans (H2.trans HR)
  exact IsDefEqU.sort_forallE_inv henv hΓQ ⟨_, HE.symm⟩

/-- Consequently no contextual comparison of the two motives is available in
the selected fragment, even in common mode at their shared type. -/
theorem motives_not_compare (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ProofShape.ContextCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ dependentMotive) (proofErase Γ constantMotive) := by
  intro H
  exact motives_not_defeq heq hΓ
    (proofErase_context_compare_reflect (step_descent heq) hΓ (motives_typed heq).1 (motives_typed heq).2 H)

private theorem peel
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.HasType univs Γ (.app f a) (.forallE A B))
    (hr : env.HasType univs Γ (.app g b) (.forallE A' B'))
    (hnl : ¬ IsProof Γ (.app f a)) (hnr : ¬ IsProof Γ (.app g b))
    (FL : ProofShape.ComputeFixed Step (proofErase Γ (.app f a)))
    (FR : ProofShape.ComputeFixed Step (proofErase Γ (.app g b)))
    (H : ProofShape.ContextCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.app f a)) (proofErase Γ (.app g b))) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g) ∧
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) ∧
    ProofShape.ComputeFixed Step (proofErase Γ f) ∧ ProofShape.ComputeFixed Step (proofErase Γ g) := by
  have EL : proofErase Γ (.app f a) = .app (proofErase Γ f) (proofErase Γ a) := if_neg hnl
  have ER : proofErase Γ (.app g b) = .app (proofErase Γ g) (proofErase Γ b) := if_neg hnr
  have hSL (m) := proofErase_function_not_structure_eta (m := m) hΓ hl
  have hSR (m) := proofErase_function_not_structure_eta (m := m) hΓ hr
  rw [EL] at FL hSL
  rw [ER] at FR hSR
  rw [EL, ER] at H
  have HI := H.fixed_app_inv FL FR hSL hSR
  exact ⟨HI.1, HI.2, FL.fn, FR.fn⟩

/-- Comparison of the two fixed prefixes would compare their retained motives.
Three applications are stripped, using their actual Pi typings to rule out
structure eta and typed fixedness to rule out computation at each spine. -/
theorem prefix_comparison_motives (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (H : ProofShape.ContextCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (partialRec dependentMotive)) (proofErase Γ (partialRec constantMotive))) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ dependentMotive) (proofErase Γ constantMotive) := by
  have hl5 := dependent_typed (Γ := Γ) heq
  have hr5 := constant_typed heq hΓ
  have hnL := not_isProof_function_to_sort hΓ hl5
  have hnR := not_isProof_function_to_sort hΓ hr5
  obtain ⟨FL, FR⟩ := prefixes_fixed heq hΓ
  obtain ⟨_, _, hl4, hla5⟩ := hl5.app_inv henv hΓ
  obtain ⟨_, _, hr4, hra5⟩ := hr5.app_inv henv hΓ
  obtain ⟨H4, _, FL4, FR4⟩ := peel hΓ hl5 hr5 hnL hnR FL FR H
  have hnL4 := not_isProof_fn hΓ hl4 hla5 hnL
  have hnR4 := not_isProof_fn hΓ hr4 hra5 hnR
  obtain ⟨_, _, hl3, hla4⟩ := hl4.app_inv henv hΓ
  obtain ⟨_, _, hr3, hra4⟩ := hr4.app_inv henv hΓ
  obtain ⟨H3, _, FL3, FR3⟩ := peel hΓ hl4 hr4 hnL4 hnR4 FL4 FR4 H4
  have hnL3 := not_isProof_fn hΓ hl3 hla4 hnL4
  have hnR3 := not_isProof_fn hΓ hr3 hra4 hnR4
  exact (peel hΓ hl3 hr3 hnL3 hnR3 FL3 FR3 H3).2.1

/-- These common-typed fixed prefixes have no contextual comparison, despite
the two checked links through their common lambda value. -/
theorem prefixes_not_compare (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ProofShape.ContextCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (partialRec dependentMotive)) (proofErase Γ (partialRec constantMotive)) :=
  fun H => motives_not_compare heq hΓ (prefix_comparison_motives heq hΓ H)

/-- Typed primitive descent and substitution closure do not suffice for common
composition of contextual certificates. The counterexample uses canonical Eq,
beta and full K, and all three originals share a type in the empty context. -/
theorem not_common_composition (heq : env.HasCanonicalEq) : ¬ ContextCommonComposition Step := by
  intro Hcomp
  obtain ⟨hl, hm, hr, H1, H2⟩ := typed_bridge heq (Γ := []) trivial
  exact prefixes_not_compare heq (Γ := []) trivial (Hcomp (Γ := []) trivial hl hm hr H1 H2)

/-- There is no uniform composition theorem from typed primitive descent and
raw substitution closure alone. The selected full-K fragment satisfies both
premises and has the common-typed counterexample above. -/
theorem no_uniform_composition (heq : env.HasCanonicalEq) :
    ¬ (∀ (R : ProofShape → ProofShape → Prop), ErasedPrimitiveDescent R →
      (∀ {a b} {σ : ProofShape.Subst}, R a b → R (a.subst σ) (b.subst σ)) →
      ContextCommonComposition R) := by
  intro H
  exact not_common_composition heq (H Step (step_descent heq) (fun H => step_subst H))

end Lean4Lean.VEnv.Strengthening.ContextPrefixWitness
