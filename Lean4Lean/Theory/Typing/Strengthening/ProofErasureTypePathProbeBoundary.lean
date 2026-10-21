import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeChangePaths
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBoxTypeChange
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredLambdaDomains

/-! # A primitive Eq reduction outside structural/beta type paths

Finite beta closure does not make the recursive Pi/Box fragment complete.
A literal sort is a beta-normal invariant of every path starting there. Even
a reflexive, closed Eq type probe is therefore outside this path relation,
although canonical Eq makes it definitionally equal to its sort-valued minor.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private BetaRed.forallE_shape
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredLambdaDomains
variable [Params]

omit [Params] in
private theorem beta_sort_fixed (R : ProofShape.BetaRed (.sort u) out) : out = .sort u := by
  have aux {a b} (H : ProofShape.BetaRed a b) : ∀ u, a = .sort u → b = .sort u := by
    induction H with
    | refl => exact fun _ E => E
    | trans R S ihR ihS => exact fun u E => ihS u (ihR u E)
    | app | lam | forallE | proj | beta => intro u E; cases E
  exact aux R u rfl

omit [Params] in
private theorem box_change_sort_reduct
    (H : BoxTypeChange family k a b) (R : ProofShape.BetaRed a (.sort u)) :
    ProofShape.BetaRed b (.sort u) := by
  cases H with
  | refl => exact R
  | neutral =>
    obtain ⟨args, E, _⟩ := R.bvar_spine
    cases args using List.snoc_induction with
    | nil => cases E
    | snoc args a => rw [ProofShape.mkApps_snoc] at E; cases E
  | forallE =>
    obtain ⟨A, B, E, _⟩ := BetaRed.forallE_shape R
    cases E
  | box =>
    obtain ⟨args, E, _⟩ := (show ProofShape.BetaRed
      (ProofShape.mkApps (.const family []) [_]) (.sort u) from R).const_spine
    have HE := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead, constHead_mkApps] at HE
    cases HE

/-- Every recursive Pi/Box and beta path starting at a type whose erasure
beta-reduces to a literal sort retains that same beta reduct. This is a
syntactic limitation of the fragment, independent of canonical Eq. -/
theorem TypeChangePath.box_sort_reduct
    (hΓ : OnCtx Γ (env.IsType univs))
    (P : TypeChangePath (BoxTypeChange family) Γ v A B)
    (R : ProofShape.BetaRed (proofErase Γ A) (.sort u)) :
    ProofShape.BetaRed (proofErase Γ B) (.sort u) := by
  induction P with
  | refl => exact R
  | related _ H => exact box_change_sort_reduct H R
  | beta hA hB RB =>
    obtain ⟨out, RS, RT⟩ := proofErase_beta_confluent hΓ hA R RB
    obtain rfl := beta_sort_fixed RS
    exact RT
  | beta_back hA hB RB => exact RB.trans R
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ R)

omit [Params] in
private theorem beta_const_fixed (R : ProofShape.BetaRed (.const c ls) out) :
    out = .const c ls := by
  obtain ⟨args, E, H⟩ := (show ProofShape.BetaRed (ProofShape.mkApps (.const c ls) []) out from R).const_spine
  cases H
  exact E

omit [Params] in
private theorem box_change_const_reduct
    (H : BoxTypeChange family k a b) (R : ProofShape.BetaRed a (.const c ls)) :
    ProofShape.BetaRed b (.const c ls) := by
  cases H with
  | refl => exact R
  | neutral =>
    obtain ⟨args, E, _⟩ := R.bvar_spine
    cases args using List.snoc_induction with
    | nil => cases E
    | snoc args a => rw [ProofShape.mkApps_snoc] at E; cases E
  | forallE =>
    obtain ⟨A, B, E, _⟩ := BetaRed.forallE_shape R
    cases E
  | box =>
    obtain ⟨args, E, H⟩ := (show ProofShape.BetaRed
      (ProofShape.mkApps (.const family []) [_]) (.const c ls) from R).const_spine
    cases H with
    | cons _ H => cases H; cases E

/-- Bare constants, like literal sorts, remain beta reducts throughout any
Pi/Box/beta path. A parameter-changing Box edge cannot erase its argument. -/
theorem TypeChangePath.box_const_reduct
    (hΓ : OnCtx Γ (env.IsType univs))
    (P : TypeChangePath (BoxTypeChange family) Γ v A B)
    (R : ProofShape.BetaRed (proofErase Γ A) (.const c ls)) :
    ProofShape.BetaRed (proofErase Γ B) (.const c ls) := by
  induction P with
  | refl => exact R
  | related _ H => exact box_change_const_reduct H R
  | beta hA hB RB =>
    obtain ⟨out, RS, RT⟩ := proofErase_beta_confluent hΓ hA R RB
    obtain rfl := beta_const_fixed RS
    exact RT
  | beta_back hA hB RB => exact RB.trans R
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ R)

/-- A non-Eq.rec bare constant type cannot be connected to its type-valued
Eq probe by the current paths, even when the probe's indices are reflexive. -/
theorem no_box_path_to_const_probe
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const c ls) (.sort u)) (hne : c ≠ ``Eq.rec)
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    ¬ TypeChangePath (BoxTypeChange family) Γ u (.const c ls)
      (eqTypeProbe u (.const c ls) P Q q) := by
  intro H
  have ES : proofErase Γ (.const c ls) = .const c ls := if_neg (not_isProof_of_sort hΓ hS)
  have R := H.box_const_reduct hΓ
    (show ProofShape.BetaRed (proofErase Γ (.const c ls)) (.const c ls) from by rw [ES]; exact .refl)
  rw [eqTypeProbe_erase heq hΓ hS hP hQ hq] at R
  obtain ⟨args, E, _⟩ := R.const_spine
  have HE := congrArg ProofShape.constHead E
  simp only [ProofShape.constHead, constHead_mkApps] at HE
  exact hne (Option.some.inj HE)

/-- No Pi/Box/beta path can connect a literal sort to an Eq type probe.
The probe may have a reflexive equality major: its missing reduction is
primitive Eq computation, not an unsolved equality of proposition indices. -/
theorem no_box_path_to_sort_probe
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    ¬ TypeChangePath (BoxTypeChange family) Γ (.succ .zero) (.sort .zero)
      (eqTypeProbe (.succ .zero) (.sort .zero) P Q q) := by
  intro H
  have hS : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have ES : proofErase Γ (.sort .zero) = .sort .zero := if_neg (not_isProof_of_sort hΓ hS)
  have R := H.box_sort_reduct hΓ (show ProofShape.BetaRed (proofErase Γ (.sort .zero)) (.sort .zero) from by rw [ES]; exact .refl)
  rw [eqTypeProbe_erase heq hΓ hS hP hQ hq] at R
  obtain ⟨args, E, _⟩ := R.const_spine
  have HE := congrArg ProofShape.constHead E
  simp only [ProofShape.constHead, constHead_mkApps] at HE
  cases HE

/-- A closed, well-typed canonical-Eq counterexample to completeness of the
mixed Pi/Box/beta path fragment. It is not a strengthening counterexample:
the two types are already definitionally equal in the empty context. -/
theorem box_beta_paths_not_complete (heq : env.HasCanonicalEq) :
    ∃ A B, env.IsDefEq univs [] A B (.sort (.succ .zero)) ∧
      ¬ TypeChangePath (BoxTypeChange family) [] (.succ .zero) A B := by
  let P : VExpr := .forallE (.sort .zero) (.bvar 0)
  have hP : env.HasType univs [] P (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial)
      (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
        (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
  have hS : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hq := HasType.eqReflApp heq (by trivial) hS hP
  have HE := eqTypeProbe_defeq heq (by trivial) hS hP hP hq ⟨_, hP⟩
  exact ⟨_, _, HE.symm, no_box_path_to_sort_probe heq (by trivial) hP hP hq⟩

end Lean4Lean.VEnv.Strengthening
