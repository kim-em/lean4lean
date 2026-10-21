import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureRecursiveRigid
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathProbeBoundary

/-! # A coverage boundary for recursive rigid conversion

Even with arbitrarily changed Pi domains, typed recursive rigid replacement
and finite beta closure cannot leave the beta-reduct class of a literal sort.
A closed reflexive canonical-Eq probe supplies a definitional equality outside
that class. This refutes fragment completeness, not strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private beta_sort_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathProbeBoundary
variable [Params]

private theorem rigid_change_sort_reduct
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A B (.sort v))
    (EA : proofErase Γ A = a) (EB : proofErase Γ B = b)
    (H : RigidTypeChange a b) (R : ProofShape.BetaRed a (.sort u)) :
    ProofShape.BetaRed b (.sort u) := by
  cases H with
  | refl => exact R
  | closed hr =>
    obtain ⟨A', RA, EA'⟩ := proofErase_beta_replay hΓ HE.hasType.1 (EA ▸ R)
    obtain rfl := erase_sort_inv EA'
    obtain rfl := erase_const_inv EB
    have HA := beta_eq hΓ HE.hasType.1 RA
    exact (henv.headInversion.sort_rigid (args := []) hΓ hr
      ((HA.symm.trans HE).toU.typeChain henv hΓ HA.hasType.2)).elim
  | forallE =>
    obtain ⟨D, C, E, _, _⟩ := beta_forallE_parts R
    cases E

/-- Every typed recursive rigid/beta path beginning at a type with a literal
sort beta reduct preserves that exact reduct. Actual equality is essential:
it excludes raw closed replacements from a sort to a rigid constant. -/
theorem TypeChangePath.rigid_sort_reduct
    (hΓ : OnCtx Γ (env.IsType univs))
    (P : TypeChangePath (fun _ => RigidTypeChange) Γ v A B)
    (R : ProofShape.BetaRed (proofErase Γ A) (.sort u)) :
    ProofShape.BetaRed (proofErase Γ B) (.sort u) := by
  induction P with
  | refl => exact R
  | related HE H => exact rigid_change_sort_reduct hΓ HE rfl rfl H R
  | beta hA hB RB =>
    obtain ⟨out, RS, RT⟩ := proofErase_beta_confluent hΓ hA R RB
    obtain rfl := beta_sort_fixed RS
    exact RT
  | beta_back hA hB RB => exact RB.trans R
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ R)

/-- No recursive rigid/beta path can connect a literal sort to an Eq type probe.
The probe may have a reflexive equality major: its missing reduction is
primitive Eq computation, not an unsolved equality of proposition indices. -/
theorem no_rigid_path_to_sort_probe
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    ¬ TypeChangePath (fun _ => RigidTypeChange) Γ (.succ .zero) (.sort .zero)
      (eqTypeProbe (.succ .zero) (.sort .zero) P Q q) := by
  intro H
  have hS : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have ES : proofErase Γ (.sort .zero) = .sort .zero := if_neg (not_isProof_of_sort hΓ hS)
  have R := H.rigid_sort_reduct hΓ (show ProofShape.BetaRed (proofErase Γ (.sort .zero)) (.sort .zero) from by rw [ES]; exact .refl)
  rw [eqTypeProbe_erase heq hΓ hS hP hQ hq] at R
  obtain ⟨args, E, _⟩ := R.const_spine
  have HE := congrArg ProofShape.constHead E
  simp only [ProofShape.constHead, constHead_mkApps] at HE
  cases HE

/-- A closed, well-typed canonical-Eq counterexample to completeness of the
mixed recursive rigid/beta path fragment. It is not a strengthening counterexample:
the two types are already definitionally equal in the empty context. -/
theorem rigid_beta_paths_not_complete (heq : env.HasCanonicalEq) :
    ∃ A B, env.IsDefEq univs [] A B (.sort (.succ .zero)) ∧
      ¬ TypeChangePath (fun _ => RigidTypeChange) [] (.succ .zero) A B := by
  let P : VExpr := .forallE (.sort .zero) (.bvar 0)
  have hP : env.HasType univs [] P (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial)
      (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
        (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
  have hS : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hq := HasType.eqReflApp heq (by trivial) hS hP
  have HE := eqTypeProbe_defeq heq (by trivial) hS hP hP hq ⟨_, hP⟩
  exact ⟨_, _, HE.symm, no_rigid_path_to_sort_probe heq (by trivial) hP hP hq⟩

end Lean4Lean.VEnv.Strengthening
