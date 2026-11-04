import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredCongruence
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCommonBetaBoundary

/-! # Nonjoining unit images through arbitrary typed bodies

The enlarged comparison accepts distinct variables of a positive empty
structure. They cannot compute to a shared shape, and the old computed checker
cannot compare them. Nevertheless their two instances of every typed body
compare by recovered-carrier congruence. This is a conditional fragment, not a
canonical-Eq counterexample or completeness of the enlarged relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

/-- Distinct bare variables cannot compare in either joint mode. Computation
at constant/projection heads and carrier-aware applications cannot change this. -/
theorem ProofShape.ComputedJointCompare.bvar_injective
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ComputedJointCompare Step Δ mode (.bvar i) (.bvar j)) : i = j := by
  generalize EA : ProofShape.bvar i = a at H
  generalize EB : ProofShape.bvar j = b at H
  change ComputedJointCheck Step Δ (.compare mode) a b at H
  generalize hk : JointCheckKind.compare mode = kind at H
  induction H generalizing mode i j with
  | leaf H =>
    cases H with
    | refl => exact ProofShape.bvar.inj (EA.trans EB.symm)
    | sort | const => cases EA
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.trans E
  | compute RA RB H ih =>
    exact ih ((EA ▸ RA).bvar_fixed hhead).symm ((EB ▸ RB).bvar_fixed hhead).symm hk
  | symm H ih => exact (ih EB EA hk).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EA
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | etaBodyR => cases EB
  | app | appCarrier | appComputed | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EA
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- A closed positive empty structure gives nonjoining image pairs that can
be substituted through every typed body using the recovered-carrier extension.
The pair itself has no comparison in the original computed union. -/
theorem carrier_recovered_nonjoining_unit_images
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ A x y, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ x A ∧ env.HasType univs Γ y A ∧
      (¬ ∃ out, ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) out ∧
        ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ) (proofErase Γ y) out) ∧
      (¬ ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) true
        (proofErase Γ x) (proofErase Γ y)) ∧
      (∀ {b B}, env.HasType univs (A :: Γ) b B →
        CarrierRecoveredCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) false
          (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y))) := by
  let S := VExpr.const family ls
  let Γ := [S, S]
  have hΓ₁ : OnCtx [S] (env.IsType univs) := ⟨trivial, _, hS⟩
  have hS₁ : env.HasType univs [S] S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₁, _, hS₁⟩
  have hSΓ : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (S :: Γ) (env.IsType univs) := ⟨hΓ, _, hSΓ⟩
  have h₀ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have E₀ : proofErase Γ (.bvar 0) = .bvar 0 := if_neg (not_proof_at_positive_type hΓ hSΓ h₀)
  have E₁ : proofErase Γ (.bvar 1) = .bvar 1 := if_neg (not_proof_at_positive_type hΓ hSΓ h₁)
  have Ectx : proofEraseCtx Γ = [.const family ls, .const family ls] := by
    change [proofErase [S] S, proofErase [] S] = _
    rw [show proofErase [S] S = .const family ls from if_neg (not_isProof_of_sort hΓ₁ hS₁),
      show proofErase [] S = .const family ls from if_neg (not_isProof_of_sort (Γ := []) trivial hS)]
  have R₀ : ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar 0)) (.const family ls) := by
    rw [Ectx, E₀]
    exact .bvar
  have R₁ : ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar 1)) (.const family ls) := by
    rw [Ectx, E₁]
    exact .bvar
  have HC : ComputedJointCarrierGuard (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (.const family ls) (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) :=
    .carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm)
  refine ⟨Γ, S, .bvar 0, .bvar 1, hΓ, h₀, h₁, ?_, ?_, ?_⟩
  · rintro ⟨out, R, R'⟩
    rw [E₀] at R
    rw [E₁] at R'
    have E := (R.bvar_fixed erased_computed_joint_union_head).symm.trans
      (R'.bvar_fixed erased_computed_joint_union_head)
    cases E
  · rw [E₀, E₁]
    intro H
    have E := H.bvar_injective erased_computed_joint_union_head
    cases E
  · intro b B hb
    exact proofErase_computed_union_inst_shared_recovered_carrier heq hs hΓS hb h₀ h₁ R₀ R₁ HC


private theorem unit_lambda
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hx : env.HasType univs Γ (.bvar i) (.const family ls)) :
    env.HasType univs Γ (.lam (.sort (.succ .zero)) (.bvar (i + 1)))
      (.forallE (.sort (.succ .zero)) (.const family ls)) ∧
    proofErase Γ (.lam (.sort (.succ .zero)) (.bvar (i + 1))) =
      .lam (.sort (.succ .zero)) (.bvar (i + 1)) := by
  have hD : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) := .sort (by trivial)
  have hΓD : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
  have hbody : env.HasType univs (.sort (.succ .zero) :: Γ) (.bvar (i + 1)) (.const family ls) := by
    simpa [VExpr.lift, VExpr.liftN, liftVar, Nat.add_comm] using (hx.weak henv (B := .sort (.succ .zero))).hasType.1
  have hfn := HasType.lam hD hbody
  have hp : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have happ : env.HasType univs Γ (.app (.lam (.sort (.succ .zero)) (.bvar (i + 1))) (.sort .zero))
      (.const family ls) := .app hfn hp
  have hn := not_isProof_fn hΓ hfn hp (not_proof_at_positive_type hΓ hS happ)
  refine ⟨hfn, ?_⟩
  rw [show proofErase Γ (.lam (.sort (.succ .zero)) (.bvar (i + 1))) = .lam _ _ from if_neg hn,
    show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) from if_neg (not_isProof_of_sort hΓ hD),
    show proofErase (.sort (.succ .zero) :: Γ) (.bvar (i + 1)) = .bvar (i + 1) from
      if_neg (not_proof_at_positive_type hΓD (hS.weak henv) hbody)]

/-- The nonjoining images may themselves be lambdas. Two constant functions
returning distinct unit variables have normal, unequal erased bodies; their
shared native function type and carrier guard still permit substitution into
every typed body in the enlarged comparison. -/
theorem carrier_recovered_nonjoining_lambda_images
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ A x y, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ x A ∧ env.HasType univs Γ y A ∧
      (∃ X b Y c, x = .lam X b ∧ y = .lam Y c) ∧
      (¬ ∃ out, ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) out ∧
        ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ) (proofErase Γ y) out) ∧
      (∀ {b B}, env.HasType univs (A :: Γ) b B →
        CarrierRecoveredCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) false
          (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y))) := by
  let S := VExpr.const family ls
  let Γ := [S, S]
  let F := VExpr.forallE (.sort (.succ .zero)) S
  have hΓ₁ : OnCtx [S] (env.IsType univs) := ⟨trivial, _, hS⟩
  have hS₁ : env.HasType univs [S] S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₁, _, hS₁⟩
  have hSΓ : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have h₀ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  obtain ⟨hL, EL⟩ := unit_lambda hΓ hSΓ h₀
  obtain ⟨hR, ER⟩ := unit_lambda hΓ hSΓ h₁
  have Ectx : proofEraseCtx Γ = [.const family ls, .const family ls] := by
    change [proofErase [S] S, proofErase [] S] = _
    rw [show proofErase [S] S = .const family ls from if_neg (not_isProof_of_sort hΓ₁ hS₁),
      show proofErase [] S = .const family ls from if_neg (not_isProof_of_sort (Γ := []) trivial hS)]
  have HN : ∀ i Δ, NormalSyntax (ErasedComputedJointUnion D Δ)
      (.lam (.sort (.succ .zero)) (.bvar i)) := by
    intro i Δ
    exact ⟨(fun _ H => erased_computed_joint_union_head H),
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩,
      ⟨fun _ H => erased_computed_joint_union_head H, trivial⟩⟩
  have Himages : CarrierRecoveredCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam (.sort (.succ .zero)) (.bvar 1)))
      (proofErase Γ (.lam (.sort (.succ .zero)) (.bvar 2))) := by
    rw [EL, ER, Ectx]
    apply CarrierRecoveredCompare.lam (.base (.leaf .refl))
    exact .recovered (A := .const family ls) .bvar .bvar
      (.carrierSubsingleton (.unit hi hx hf (ps := []) hp.symm))
  obtain ⟨v, hF⟩ := hL.isType henv hΓ
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, v, hF⟩
  refine ⟨Γ, F, _, _, hΓ, hL, hR, ⟨_, _, _, _, rfl, rfl⟩, ?_, ?_⟩
  · rintro ⟨out, RL, RR⟩
    rw [EL] at RL
    rw [ER] at RR
    have E := (scoped_normal_fixed RL (HN 1)).symm.trans (scoped_normal_fixed RR (HN 2))
    cases E
  · intro b B hb
    exact proofErase_carrier_recovered_inst_images (erased_computed_joint_union_rename heq hs)
      hΓF hb hL hR Himages

end Lean4Lean.VEnv.Strengthening
