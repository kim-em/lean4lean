import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveFamilyCast
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCertifiedProbe

/-! # Recursive cast guards with provably nonjoining endpoint types

Eta-related equality propositions are placed in the domains of inhabited
function types. These function types have distinct normal erasures in the full
joint union, yet the recursive comparison grammar certifies them. Their cast
payload is a retained lambda, so cast removal is not merely proof erasure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private functionType function_type erasures normal_forms leftRaw rightRaw etaRaw functionRaw
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCertifiedProbe
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params] {D : Definitions}

/-- A concrete recursively certified cast between inhabited function types
whose erasures have no join even in the full joint union. The endpoint
certificate uses eta, Eq-family and sorted-Pi constructors; no supplied future
certificate or endpoint join is a premise. -/
theorem recursive_family_cast_nonjoining_endpoints
    (heq : env.HasCanonicalEq) (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' u X Y q x, OnCtx Γ' (env.IsType univs) ∧ u.WF univs ∧
      env.HasType univs Γ' X (.sort u) ∧ env.HasType univs Γ' Y (.sort u) ∧
      env.HasType univs Γ' q (eqApp (.succ u) (.sort u) X Y) ∧ env.HasType univs Γ' x X ∧
      ¬ IsProof Γ' x ∧
      RecursiveFamilyCast D true (proofEraseCtx Γ') (proofErase Γ' X) (proofErase Γ' Y) ∧
      RecursiveFamilyCast D false (proofEraseCtx Γ')
        (proofErase Γ' (typeCast u X Y q x)) (proofErase Γ' x) ∧
      ¬ ∃ shared, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' X) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' Y) shared := by
  let Γ' := functionType :: Γ
  have hC : OnCtx Γ' (env.IsType univs) := ⟨hΓ, _, function_type⟩
  have hf : env.HasType univs Γ' (.bvar 0) functionType := .bvar .zero
  have HE := IsDefEq.eta hf
  have Hη : RecursiveFamilyCast D true (proofEraseCtx Γ')
      (proofErase Γ' (.bvar 0)) (proofErase Γ' (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0)))) :=
    .symm (.eta hC hf)
  have HPQ := RecursiveFamilyCast.eqFamily (by trivial) hC function_type hf HE.hasType.1 Hη
  have hP := HasType.eqApp heq (by trivial) function_type hf hf
  have hQ := HasType.eqApp heq (by trivial) function_type hf HE.hasType.1
  have HPQeq := IsDefEq.eqApp_r heq (by trivial) function_type hf HE.symm
  let P := eqApp (.imax (.succ .zero) (.succ .zero)) functionType (.bvar 0) (.bvar 0)
  let Q := eqApp (.imax (.succ .zero) (.succ .zero)) functionType (.bvar 0) (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0)))
  change env.HasType univs Γ' P (.sort .zero) at hP
  change env.HasType univs Γ' Q (.sort .zero) at hQ
  let u := VLevel.imax .zero (.succ (.succ .zero))
  let X := VExpr.forallE P (.sort (.succ .zero))
  let Y := VExpr.forallE Q (.sort (.succ .zero))
  have hX : env.HasType univs Γ' X (.sort u) := .forallE hP (.sort (by trivial))
  have hY : env.HasType univs Γ' Y (.sort u) := .forallE hQ (.sort (by trivial))
  have hCP : OnCtx (P :: Γ') (env.IsType univs) := ⟨hC, _, hP⟩
  have hCQ : OnCtx (Q :: Γ') (env.IsType univs) := ⟨hC, _, hQ⟩
  have hS : env.HasType univs (P :: Γ') (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have ES : proofErase (P :: Γ') (.sort (.succ .zero)) = .sort (.succ .zero) :=
    if_neg (not_isProof_of_sort hCP hS)
  have ES' : proofErase (Q :: Γ') (.sort (.succ .zero)) = .sort (.succ .zero) :=
    if_neg (not_isProof_of_sort hCQ (HasType.sort (by trivial)))
  have EX : proofErase Γ' X = .forallE (proofErase Γ' P) (.sort (.succ .zero)) := by
    rw [show proofErase Γ' X = .forallE _ _ from if_neg (not_isProof_of_sort hC hX), ES]
  have EY : proofErase Γ' Y = .forallE (proofErase Γ' Q) (.sort (.succ .zero)) := by
    rw [show proofErase Γ' Y = .forallE _ _ from if_neg (not_isProof_of_sort hC hY), ES']
  have HB : RecursiveFamilyCast D true (proofEraseCtx (P :: Γ'))
      (.sort (.succ .zero)) (.sort (.succ .zero)) := by
    rw [← ES]
    exact .join hCP hS hS (.prior (.core .refl)) (.prior (.core .refl))
  have HS : DomainSort (proofEraseCtx (P :: Γ')) (.sort (.succ .zero)) (.succ (.succ .zero)) :=
    ES ▸ DomainSort.of_typed hCP hS
  have HX : RecursiveFamilyCast D true (proofEraseCtx Γ') (proofErase Γ' X) (proofErase Γ' Y) := by
    rw [EX, EY]
    exact .forallSorted (DomainSort.of_typed hC hP) (DomainSort.of_typed hC hQ) HS HS HPQ HB
  have HXY : env.IsDefEq univs Γ' X Y (.sort u) := .forallEDF HPQeq (HasType.sort (by trivial))
  have hu : u.WF univs := by trivial
  have hq := (IsDefEq.eqApp_r heq (by exact hu) (HasType.sort hu) hX HXY).defeq
    (HasType.eqReflApp heq (by exact hu) (HasType.sort hu) hX)
  have hx : env.HasType univs Γ' (.lam P (.sort .zero)) X := .lam hP (.sort (by trivial))
  refine ⟨Γ', u, X, Y, _, _, hC, hu, hX, hY, hq, hx,
    not_isProof_function_to_sort hC hx, HX, .cast hu hC hX hY hq hx HX, ?_⟩
  rintro ⟨shared, RX, RY⟩
  obtain ⟨Eα, Ef, Eη⟩ := erasures hΓ
  have EP : proofErase Γ' P = leftRaw := by
    have H := proofErase_eqProofType heq (by trivial) hC function_type hf hf
    rw [Eα, Ef] at H
    exact H
  have EQ : proofErase Γ' Q = rightRaw := by
    have H := proofErase_eqProofType heq (by trivial) hC function_type hf HE.hasType.1
    change proofErase (functionType :: Γ)
      (.lam (.sort .zero) (.app (VExpr.bvar 0).lift (.bvar 0))) = etaRaw at Eη
    rw [Eα, Ef, Eη] at H
    exact H
  rw [EX, EP] at RX
  rw [EY, EQ] at RY
  have NL (Δ) : NormalSyntax (ErasedJointUnion D Δ) (.forallE leftRaw (.sort (.succ .zero))) :=
    ⟨fun _ H => erased_joint_union_head H, (normal_forms heq hEq Δ).1,
      fun _ H => erased_joint_union_head H, trivial⟩
  have NR (Δ) : NormalSyntax (ErasedJointUnion D Δ) (.forallE rightRaw (.sort (.succ .zero))) :=
    ⟨fun _ H => erased_joint_union_head H, (normal_forms heq hEq Δ).2,
      fun _ H => erased_joint_union_head H, trivial⟩
  have EL := scoped_normal_fixed RX NL
  have ER := scoped_normal_fixed RY NR
  cases EL.symm.trans ER

end Lean4Lean.VEnv.Strengthening
