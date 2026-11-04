import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedFieldTransfer
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFirstBeta

/-! # A mixed data/proof field guard across a computed universe variant

A nullary structure with fields P : Prop and h : P needs a comparison only of
its first projection. The selected carrier is an identity-redex expansion at a
different but equivalent universe list. Its field guard is reconstructed from
the source instance and actual typings, with no empty-field hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

/-- A P : Prop, h : P telescope marks the second field as a proof at every
universe instance. The first projection remains an explicit comparison premise. -/
theorem StructureReplay.ProofField.proposition_pair_second
    (hshape : info.ctorType = .forallE (.sort .zero) (.forallE (.bvar 0) result))
    (hp : info.nparams = 0) (hf : info.numFields = 2) :
    StructureReplay.ProofField env univs info ls 1 := by
  refine ⟨[.sort .zero, .bvar 0], result, by simp [hp], hshape, by simp [hp, hf], ?_⟩
  simpa only [hp, Nat.zero_add, List.take_succ_cons, List.take_zero, List.map_cons,
    List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.getElem_cons_succ, List.getElem_cons_zero, instL, VLevel.inst, VExpr.lift, VExpr.liftN] using
    (HasType.bvar (env := env) (U := univs) (Γ := [.sort .zero]) (Lookup.zero (Γ := [])))

omit [Params] in
private theorem identity_const_not_alias
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out) :
    ¬ ScopedCompute Step Δ (.app (.lam (.sort v) (.bvar 0)) (.const family [.zero]))
      (.const family [.max .zero .zero]) := by
  intro R
  rcases R.lambda_app_or_beta hhead with ⟨_, _, _, E, _, _⟩ | ⟨A, b, x, RF, RX, RT⟩
  · cases E
  have EF := scoped_normal_fixed RF (fun _ => ⟨fun _ H => hhead H,
    ⟨fun _ H => hhead H, trivial⟩, ⟨fun _ H => hhead H, trivial⟩⟩)
  obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj EF
  have EX := scoped_normal_fixed RX (fun _ => ⟨fun _ H => hn H, trivial⟩)
  subst x
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
    ProofShape.Subst.one, ProofShape.Subst.cons] at RT
  have ET := scoped_normal_fixed RT (fun _ => ⟨fun _ H => hn H, trivial⟩)
  cases ET

/-- A nonempty mixed-field guard transfers from the alias universe [max 0 0]
to an actual beta-expanded carrier at [0]. Projection 1 is omitted using its
closed proof certificate; projection 0 retains the supplied recursive check.
The two carrier types have no computational join. -/
theorem carrier_aligned_mixed_fields_computed_universes
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 2)
    (hshape : info.ctorType = .forallE (.sort .zero) (.forallE (.bvar 0) result))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family [.max .zero .zero]) (.sort u))
    (hS' : env.HasType univs Γ (.const family [.zero]) (.sort v))
    (hadm : (info.resultLevel.inst [.max .zero .zero]).IsNeverZero ∨
      StructureReplay.ProofFields env univs info [.max .zero .zero])
    (Hfield : ComputedJointCompare Step (proofEraseCtx Γ) true (.proj family 0 x) (.proj family 0 y)) :
    ∃ T, env.HasType univs Γ T (.sort v) ∧
      StructureReplay.ProofField env univs info [.max .zero .zero] 1 ∧
      StructureReplay.ProofField env univs info [.zero] 1 ∧
      (¬ ∃ out, ScopedCompute Step (proofEraseCtx Γ)
          (proofErase Γ (.const family [.max .zero .zero])) out ∧
        ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) out) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false
        (proofErase Γ (.const family [.max .zero .zero])) (proofErase Γ T) ∧
      ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ T) x y := by
  let T := VExpr.app (.lam (.sort v) (.bvar 0)) (.const family [.zero])
  have Hβ : env.IsDefEq univs Γ T (.const family [.zero]) (.sort v) := by
    simpa [T, VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN] using
      (IsDefEq.beta (HasType.bvar (Γ := .sort v :: Γ) Lookup.zero) hS')
  have R := proofErase_beta_forward hΓ Hβ.hasType.1 (show BetaRed T (.const family [.zero]) from .beta)
  have ES : proofErase Γ (.const family [.max .zero .zero]) = .const family [.max .zero .zero] :=
    if_neg (not_isProof_of_sort hΓ hS)
  have ES' : proofErase Γ (.const family [.zero]) = .const family [.zero] :=
    if_neg (not_isProof_of_sort hΓ hS')
  have hdom : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort (hS'.sort_r henv hΓ)
  have hΓv : OnCtx (.sort v :: Γ) (env.IsType univs) := ⟨hΓ, _, hdom⟩
  have hv : env.HasType univs (.sort v :: Γ) (.bvar 0) (.sort v) := .bvar .zero
  have hfn := HasType.lam hdom hv
  have ET : proofErase Γ T = .app (.lam (.sort v) (.bvar 0)) (.const family [.zero]) := by
    rw [show proofErase Γ T = .app _ _ from if_neg (not_isProof_of_sort hΓ Hβ.hasType.1),
      show proofErase Γ (.lam (.sort v) (.bvar 0)) = .lam _ _ from
        if_neg (not_isProof_fn hΓ hfn hS' (not_isProof_of_sort hΓ Hβ.hasType.1)),
      show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ hdom),
      show proofErase (.sort v :: Γ) (.bvar 0) = .bvar 0 from if_neg (not_isProof_of_sort hΓv hv), ES']
  have Hno : ¬ ∃ out, ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (.const family [.max .zero .zero])) out ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) out := by
    rw [ES, ET]
    rintro ⟨out, RA, RB⟩
    have E := scoped_normal_fixed RA (fun _ => ⟨fun _ H => hn H, trivial⟩)
    rw [E] at RB
    exact identity_const_not_alias hhead hn RB
  have HC : CarrierAlignedCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (.const family [.max .zero .zero])) (proofErase Γ T) := by
    apply CarrierAlignedCompare.compute .refl (.beta R)
    rw [ES, ES']
    exact .base (.base (.leaf (.const (.cons (by simp [VLevel.equiv_def, VLevel.eval]) .nil))))
  have HP : StructureReplay.ProofField env univs info [.max .zero .zero] 1 :=
    StructureReplay.ProofField.proposition_pair_second hshape hp hf
  have hlevels := StructureReplay.family_instance_levels hi hΓ hS
  have hlevels' := StructureReplay.family_instance_levels hi hΓ hS'
  have HE : List.Forall₂ (· ≈ ·) [VLevel.max .zero .zero] [VLevel.zero] :=
    .cons (by simp [VLevel.equiv_def, VLevel.eval]) .nil
  refine ⟨T, Hβ.hasType.1, HP, HP.congr_levels hi hlevels.1 hlevels'.1 hlevels.2 HE, Hno, HC, ?_⟩
  apply proofErase_carrier_aligned_nullary_fields_target hstep hn hi hx hp hΓ hS Hβ.hasType.1 HC ES hadm
  intro i hj hnproof
  have hiCases : i = 0 ∨ i = 1 := by omega
  rcases hiCases with rfl | rfl
  · exact Hfield
  · exact (hnproof HP).elim

end Lean4Lean.VEnv.Strengthening
