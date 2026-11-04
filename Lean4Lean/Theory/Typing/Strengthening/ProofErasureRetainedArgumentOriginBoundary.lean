import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerEtaAnnotation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFreshTypeBoundary

/-! # Retained argument origins fail after caller eta

A caller declares a function argument at a unit-converted domain. Eta on the
caller and then its bound argument changes the supplied lambda's annotation.
The new annotation mentions a fresh retained index, so no descending computation
of that supplied argument can reach it. The endpoint is already beta-normal.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Neutral type-head readout cannot generally retain a forward computation
history for each data argument, even after arbitrary beta cleanup. The source
and endpoint are typed type applications with one function-valued argument.
The counterexample uses caller eta and unit equality, not a failure of joining
or strengthening: both arguments compute to a shared lambda by unit eta. It applies to canonical-Eq environments with a positive empty
unindexed structure. -/
theorem static_structure_retained_argument_origin_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ x y,
      OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ (.app (.bvar 0) x) (.sort (.succ .zero)) ∧
      env.HasType univs Γ (.app (.bvar 0) y) (.sort (.succ .zero)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app (.bvar 0) x)) (proofErase Γ (.app (.bvar 0) y)) ∧
      (∃ shared,
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ x) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ y) shared) ∧
      ¬ ∃ arg, BetaRed (proofErase Γ (.app (.bvar 0) y)) (.app (.bvar 0) arg) ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ x) arg := by
  let S := VExpr.const family []
  let K := VExpr.forallE S (.sort (.succ .zero))
  let Γ₀ := [K, S]
  have hK : env.HasType univs [] K (.sort (.imax (.succ u) (.succ (.succ .zero)))) :=
    .forallE hS (.sort (by trivial))
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hK.weak0 henv.ordered⟩
  have hK₀ : env.HasType univs Γ₀ (.bvar 0) K := .bvar .zero
  have hx₀ : env.HasType univs Γ₀ (.bvar 1) S := .bvar (.succ .zero)
  let B₀ := VExpr.app (.bvar 0) (.bvar 1)
  have hB₀ : env.HasType univs Γ₀ B₀ (.sort (.succ .zero)) := .app hK₀ hx₀
  let q₀ := VExpr.lam B₀ (.sort .zero)
  have hq₀ : env.HasType univs Γ₀ q₀ (.forallE B₀ (.sort (.succ .zero))) :=
    .lam hB₀ (.sort (by trivial))
  let Γ₁ := S :: Γ₀
  have hΓ₁ : OnCtx Γ₁ (env.IsType univs) := ⟨hΓ₀, _, hS.weak0 henv.ordered⟩
  have hK₁ : env.HasType univs Γ₁ (.bvar 1) K := .bvar (.succ .zero)
  have hy₁ : env.HasType univs Γ₁ (.bvar 0) S := .bvar .zero
  have hx₁ : env.HasType univs Γ₁ (.bvar 2) S := .bvar (.succ (.succ .zero))
  let A₁ := VExpr.app (.bvar 1) (.bvar 0)
  have hA₁ : env.HasType univs Γ₁ A₁ (.sort (.succ .zero)) := .app hK₁ hy₁
  have HE₁ : env.IsDefEq univs Γ₁ A₁ B₀.lift (.sort (.succ .zero)) :=
    IsDefEq.appDF hK₁ (IsDefEq.unitLike hi (params := []) hp.symm hx hz hy₁ hx₁)
  let Q₁ := VExpr.forallE A₁ (.sort (.succ .zero))
  let H₁ := VExpr.forallE Q₁ (.sort (.succ .zero))
  have hQ₁ : env.HasType univs Γ₁ Q₁
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) := .forallE hA₁ (.sort (by trivial))
  have hH₁ : env.HasType univs Γ₁ H₁
      (.sort (.imax (.imax (.succ .zero) (.succ (.succ .zero))) (.succ (.succ .zero)))) :=
    .forallE hQ₁ (.sort (by trivial))
  let Γ := H₁ :: Γ₁
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₁, _, hH₁⟩
  have W : Ctx.LiftN 2 0 Γ₀ Γ := .zero [H₁, S]
  let A := A₁.lift
  let B := B₀.liftN 2
  let Q := Q₁.lift
  let x := q₀.liftN 2
  let y := VExpr.lam A (.sort .zero)
  have hA : env.HasType univs Γ A (.sort (.succ .zero)) := hA₁.weakN henv Ctx.LiftN.one
  have hB : env.HasType univs Γ B (.sort (.succ .zero)) := hB₀.weakN henv W
  have hQ : env.HasType univs Γ Q
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) := hQ₁.weakN henv Ctx.LiftN.one
  have HE : env.IsDefEq univs Γ A B (.sort (.succ .zero)) := HE₁.weakN henv Ctx.LiftN.one
  have hxQ : env.HasType univs Γ x Q :=
    (IsDefEq.forallEDF HE (HasType.sort (l := .succ .zero) (by trivial))).symm.defeq (hq₀.weakN henv W)
  have hyQ : env.HasType univs Γ y Q := .lam hA (.sort (by trivial))
  have hf : env.HasType univs Γ (.bvar 0) (.forallE Q (.sort (.succ .zero))) := .bvar .zero
  have hfx := HasType.app hf hxQ
  have hfy := HasType.app hf hyQ
  have hK₂ : env.HasType univs Γ (.bvar 2) K := .bvar (.succ (.succ .zero))
  have hy₂ : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have hx₂ : env.HasType univs Γ (.bvar 3) S := .bvar (.succ (.succ (.succ .zero)))
  have EF : proofErase Γ (.bvar 0) = .bvar 0 := if_neg (not_isProof_function_to_sort hΓ hf)
  have EK : proofErase Γ (.bvar 2) = .bvar 2 := if_neg (not_isProof_function_to_sort hΓ hK₂)
  have EX : proofErase Γ (.bvar 3) = .bvar 3 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hx₂)
  have EY : proofErase Γ (.bvar 1) = .bvar 1 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hy₂)
  have EA : proofErase Γ A = .app (.bvar 2) (.bvar 1) := by
    rw [show proofErase Γ A = .app _ _ from if_neg (not_isProof_of_sort hΓ hA)]
    change ProofShape.app (proofErase Γ (.bvar 2)) (proofErase Γ (.bvar 1)) = _
    rw [EK, EY]
  have EB : proofErase Γ B = .app (.bvar 2) (.bvar 3) := by
    rw [show proofErase Γ B = .app _ _ from if_neg (not_isProof_of_sort hΓ hB)]
    change ProofShape.app (proofErase Γ (.bvar 2)) (proofErase Γ (.bvar 3)) = _
    rw [EK, EX]
  have ES (Γ' : List VExpr) (hΓ' : OnCtx Γ' (env.IsType univs)) (v : VLevel) (hv : v.WF univs) :
      proofErase Γ' (.sort v) = .sort v := if_neg (not_isProof_of_sort hΓ' (HasType.sort hv))
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, _, hB⟩
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have EQ : proofErase Γ Q = .forallE (.app (.bvar 2) (.bvar 1)) (.sort (.succ .zero)) := by
    rw [show proofErase Γ Q = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hQ)]
    change ProofShape.forallE (proofErase Γ A) (proofErase (A :: Γ) (.sort (.succ .zero))) = _
    rw [EA, ES _ hΓA _ (by trivial)]
  have Ex : proofErase Γ x = .lam (.app (.bvar 2) (.bvar 3)) (.sort .zero) := by
    rw [show proofErase Γ x = .lam _ _ from if_neg (not_isProof_function_to_sort hΓ hxQ)]
    change ProofShape.lam (proofErase Γ B) (proofErase (B :: Γ) (.sort .zero)) = _
    rw [EB, ES _ hΓB _ (by trivial)]
  have Ey : proofErase Γ y = .lam (.app (.bvar 2) (.bvar 1)) (.sort .zero) := by
    rw [show proofErase Γ y = .lam _ _ from if_neg (not_isProof_function_to_sort hΓ hyQ), EA,
      ES _ hΓA _ (by trivial)]
  have EFtype : proofErase Γ (.forallE Q (.sort (.succ .zero))) =
      .forallE (.forallE (.app (.bvar 2) (.bvar 1)) (.sort (.succ .zero))) (.sort (.succ .zero)) := by
    rw [show proofErase Γ (.forallE Q (.sort (.succ .zero))) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (HasType.forallE hQ (HasType.sort (by trivial)))), EQ,
      ES _ hΓQ _ (by trivial)]
  have RN := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionUnion D)
    hΓ Lookup.zero (not_isProof_function_to_sort hΓ hf) ScopedCompute.refl
  change ScopedTypeRecovery _ _ (proofErase Γ (.bvar 0))
    (proofErase Γ (.forallE Q (.sort (.succ .zero)))) at RN
  rw [EF, EFtype] at RN
  have SQ := DomainSort.of_typed hΓ hQ
  rw [EQ] at SQ
  have SA := DomainSort.of_typed hΓQ (hA.weakN henv Ctx.LiftN.one)
  rw [proofErase_liftN hΓ hΓQ Ctx.LiftN.one hA, EA, proofEraseCtx, EQ] at SA
  have R := static_structure_caller_reannotates_constant
    (L := ProofShape.app (.bvar 2) (.bvar 3)) (w := .zero) RN SQ
    (by intro E; have H := congrFun E []; simp [VLevel.eval, Lean.Nat.imax] at H)
    SA (by intro E; have H := congrFun E []; simp [VLevel.eval] at H)
  have Efx : proofErase Γ (.app (.bvar 0) x) = .app (.bvar 0) (proofErase Γ x) := by
    rw [show proofErase Γ (.app (.bvar 0) x) = .app _ _ from if_neg (not_isProof_of_sort hΓ hfx), EF]
  have Efy : proofErase Γ (.app (.bvar 0) y) = .app (.bvar 0) (proofErase Γ y) := by
    rw [show proofErase Γ (.app (.bvar 0) y) = .app _ _ from if_neg (not_isProof_of_sort hΓ hfy), EF]
  have ESc : proofErase Γ S = .const family [] :=
    if_neg (not_isProof_of_sort hΓ (hS.weak0 henv.ordered))
  have RI := proofErase_scoped_lookup_recovery
    (Step := ErasedStaticStructureEtaExpansionUnion D) hΓ
    (show Lookup Γ 3 S from .succ (.succ (.succ .zero)))
    (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hx₂) ScopedCompute.refl
  have RJ := proofErase_scoped_lookup_recovery
    (Step := ErasedStaticStructureEtaExpansionUnion D) hΓ
    (show Lookup Γ 1 S from .succ .zero)
    (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hy₂) ScopedCompute.refl
  rw [EX, ESc] at RI
  rw [EY, ESc] at RJ
  have UI : NativeUnitExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar 3) (.const info.ctorName []) := .intro hi hx hz (ps := []) hp.symm RI
  have UJ : NativeUnitExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar 1) (.const info.ctorName []) := .intro hi hx hz (ps := []) hp.symm RJ
  have CI := ScopedCompute.base (erased_static_structure_eta_expansion_union_structure UI.maskedStructure)
  have CJ := ScopedCompute.base (erased_static_structure_eta_expansion_union_structure UJ.maskedStructure)
  refine ⟨Γ, x, y, hΓ, hfx, hfy, ?_, ?_, ?_⟩
  · simpa only [Efx, Efy, Ex, Ey] using R
  · refine ⟨.lam (.app (.bvar 2) (.const info.ctorName [])) (.sort .zero), ?_, ?_⟩
    · rw [Ex]
      exact .lam (.app .refl CI) .refl
    · rw [Ey]
      exact .lam (.app .refl CJ) .refl
  · rintro ⟨arg, RB, RX⟩
    rw [Efy, Ey] at RB
    have HN : NormalSyntax (fun _ _ => False)
        (.app (.bvar 0) (.lam (.app (.bvar 2) (.bvar 1)) (.sort .zero))) := by
      simp [NormalSyntax]
    have Earg := ProofShape.app.inj (RB.fixed_of_normal HN)
    rw [Earg.2] at RX
    have EN := proofErase_liftN hΓ₀ hΓ W hq₀
    change proofErase Γ x = _ at EN
    rw [EN] at RX
    exact compute_no_inserted_lambda_domain_argument
      (erased_static_structure_eta_expansion_union_descent heq hs)
      hΓ₀ hΓ W hq₀ (j := 1) (by decide) (by decide) RX

end Lean4Lean.VEnv.Strengthening
