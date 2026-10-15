import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureSingletonStages
import Lean4Lean.Theory.Typing.Strengthening.EqRecResultBoundary

/-! # A nested empty-structure field in a neutral Eq-prefix guard

The outer structure has one data field of an empty-structure type. Comparing
its neutral majors recursively uses that field's explicit carrier; no comparison
of their raw projections or of the original variables is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- A one-field outer structure whose closed field type is an empty structure
admits a recursive carrier guard for arbitrary raw majors. The field is data,
so this exercises recursive type-directed checking rather than proof skipping. -/
theorem one_unit_field_guard
    (hi : env.projections inner innerInfo) (hip : innerInfo.nparams = 0)
    (hix : innerInfo.nindices = 0) (hif : innerInfo.numFields = 0)
    (hS : env.HasType univs [] (.const inner ils) (.sort (.succ u)))
    (ho : env.projections outer outerInfo) (hop : outerInfo.nparams = 0)
    (hox : outerInfo.nindices = 0) (hof : outerInfo.numFields = 1)
    (hoshape : outerInfo.ctorType.instL ols = .forallE (.const inner ils) (.const outer ols))
    (hadm : (outerInfo.resultLevel.inst ols).IsNeverZero ∨
      StructureReplay.ProofFields env univs outerInfo ols) :
    ProofShape.StructureCarrierGuard Step Δ (.const outer ols) a b := by
  have HT : ProjTele env univs outer outerInfo ols [.const inner ils] (.const outer ols) := by
    refine ⟨hoshape, ⟨outer, ols, [], rfl⟩, ?_, ?_, ?_⟩
    · intro k hk
      have : k = 0 := by simp only [List.length_singleton] at hk; omega
      subst k
      exact ⟨_, hS⟩
    · intro k hk
      have : k = 0 ∨ k = 1 := by simp only [List.length_singleton] at hk; omega
      rcases this with rfl | rfl
      · trivial
      · exact ⟨trivial, _, hS⟩
    · simp [hof, hop]
  apply ProofShape.StructureCarrierGuard.nested ho hox (ps := []) hop.symm hadm HT
  intro i hj _
  have : i = 0 := by omega
  subst i
  have ES : proofErase [] (.const inner ils) = .const inner ils :=
    if_neg (not_isProof_of_sort (by trivial) hS)
  have ER : ProofShape.projectionType outer outerInfo [.const inner ils] 0
      (by simp [hop]) [] a = .const inner ils := by
    simp [ProofShape.projectionType, ProofShape.projectionArgs, hop, ES,
      ProofShape.instOuter, ProofShape.subst]
  rw [ER]
  exact ProofShape.StructureCarrierGuard.intro hi hix (ps := []) hip.symm
    (.inr (StructureReplay.ProofFields.of_no_fields hif)) (by intro j hj; omega)

/-- A concrete context of two outer-structure variables supplies a typed
recursor computing to Prop with the nested field guard at stage one. Direct
ScopedCompare of those variables remains impossible at every augmented stage.
The hypotheses specify registered structures; no environment extension is
constructed or assumed to follow merely from their syntactic shapes. -/
theorem nested_unit_neutral_sort_exposure (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hi : env.projections inner innerInfo) (hip : innerInfo.nparams = 0)
    (hix : innerInfo.nindices = 0) (hif : innerInfo.numFields = 0)
    (hS : env.HasType univs [] (.const inner ils) (.sort (.succ u)))
    (ho : env.projections outer outerInfo) (hop : outerInfo.nparams = 0)
    (hox : outerInfo.nindices = 0) (hof : outerInfo.numFields = 1)
    (hoshape : outerInfo.ctorType.instL ols = .forallE (.const inner ils) (.const outer ols))
    (hadm : (outerInfo.resultLevel.inst ols).IsNeverZero ∨
      StructureReplay.ProofFields env univs outerInfo ols)
    (hO : env.HasType univs [] (.const outer ols) (.sort (.succ v))) :
    ∃ Γ e, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ e (.sort (.succ .zero)) ∧
      env.IsDefEq univs Γ e (.sort .zero) (.sort (.succ .zero)) ∧
      ProofShape.ScopedCompute (ErasedStructureSingletonStage D 1) (proofEraseCtx Γ)
        (proofErase Γ e) (.sort .zero) ∧
      ∀ stage mode, ¬ ProofShape.ScopedCompare (ErasedStructureSingletonStage D stage)
        (proofEraseCtx Γ) mode (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) := by
  let O := VExpr.const outer ols
  let Γ := [O, O]
  have hΓ : OnCtx Γ (env.IsType univs) :=
    ⟨⟨trivial, _, hO⟩, _, hO.weak0 henv.ordered⟩
  have hO' : env.HasType univs Γ O (.sort (.succ v)) := hO.weak0 henv.ordered
  have h₀ : env.HasType univs Γ (.bvar 0) O := .bvar .zero
  have h₁ : env.HasType univs Γ (.bvar 1) O := .bvar (.succ .zero)
  have EO : proofErase Γ O = .const outer ols := if_neg (not_isProof_of_sort hΓ hO')
  have HC : ProofShape.StructureCarrierGuard (ErasedStructureSingletonStage D 0) (proofEraseCtx Γ)
      (proofErase Γ O) (proofErase Γ (.bvar 0)) (proofErase Γ (.bvar 1)) := by
    rw [EO]
    exact one_unit_field_guard hi hip hix hif hS ho hop hox hof hoshape hadm
  have H₀₁ := proofErase_structure_carrier_reflect
    (erased_structure_singleton_stage_descent heq hs 0) hΓ h₀ h₁ HC
  have hw := hO'.sort_r henv hΓ
  let q := eqReflApp (.succ v) O (.bvar 0)
  have hq : env.HasType univs Γ q (eqApp (.succ v) O (.bvar 0) (.bvar 1)) :=
    (IsDefEq.eqApp_r heq hw hO' h₀ H₀₁).defeq (HasType.eqReflApp heq hw hO' h₀)
  let M := constantEqMotive (.succ v) O (.bvar 0) (.sort (.succ .zero))
  let e := eqRecApp (.succ (.succ .zero)) (.succ v) O (.bvar 0) M (.sort .zero) (.bvar 1) q
  have he : env.HasType univs Γ e (.sort (.succ .zero)) :=
    constant_eqRec_typed henv heq (by trivial) hw hΓ hO' h₀
      (HasType.sort (by trivial)) (HasType.sort (by trivial)) h₁ hq
  have HE : env.IsDefEq univs Γ e (.sort .zero) (.sort (.succ .zero)) :=
    eqRecApp_simAt henv heq hΓ ⟨_, H₀₁⟩ _ he
  have R := proofErase_structure_singleton_full_forward heq hs hΓ he HC
  have Eprop : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  rw [Eprop] at R
  refine ⟨Γ, e, hΓ, he, HE, R, ?_⟩
  intro stage mode H
  have hn₀ := not_proof_at_positive_type hΓ hO' h₀
  have hn₁ := not_proof_at_positive_type hΓ hO' h₁
  rw [show proofErase Γ (.bvar 0) = .bvar 0 from if_neg hn₀,
    show proofErase Γ (.bvar 1) = .bvar 1 from if_neg hn₁] at H
  have HN := H.bvar_injective (erased_structure_singleton_stage_head stage)
  cases HN

/-- In a record with fields P : Prop and h : P, only the proposition-valued
data field is compared. The second field's closed typing supplies its static
proof certificate, even though the first field is retained by erasure. -/
theorem mixed_proposition_field_guard
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 2)
    (hshape : info.ctorType = .forallE (.sort .zero) (.forallE (.bvar 0) (.const family [])))
    (hadm : (info.resultLevel.inst []).IsNeverZero ∨ StructureReplay.ProofFields env univs info [])
    (H : ProofShape.ScopedCompare Step Δ true (.proj family 0 a) (.proj family 0 b)) :
    ProofShape.StructureCarrierGuard Step Δ (.const family []) a b := by
  have HP : StructureReplay.ProofField env univs info [] 1 := by
    refine ⟨[.sort .zero, .bvar 0], .const family [], by simp [hp], hshape,
      by simp [hp, hf], ?_⟩
    simpa only [hp, Nat.zero_add, List.take_succ_cons, List.take_zero, List.map_cons,
      List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.getElem_cons_succ, List.getElem_cons_zero, instL, VLevel.inst, lift, liftN] using
      (HasType.bvar (env := env) (U := univs) (Γ := [.sort .zero]) (Lookup.zero (Γ := [])))
  apply ProofShape.StructureCarrierGuard.intro hi hx (ps := []) hp.symm hadm
  intro i hj
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact .inr H
  · exact .inl HP

end Lean4Lean.VEnv.Strengthening
