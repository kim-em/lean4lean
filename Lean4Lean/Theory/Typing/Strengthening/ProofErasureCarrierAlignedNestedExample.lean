import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNestedTransfer

/-! # A function-valued nested field across nonjoining universe instances

The outer structure has one retained field of type Prop → Inner, where Inner
is an empty structure. Its field guard uses recursive structural subsingleton
checking, with no comparison premise for the projected functions. Equivalent
but syntactically distinct outer universe instances have no computation join.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

/-- A one-field structure with field Prop → Inner transfers its nested carrier
guard from [max 0 0] to [0]. The empty Inner structure may have its own universe
parameter; the function field is retained and its full recipe changes universe
syntax. No endpoint or projection comparison is supplied. Actual environment
registration and family typings remain explicit hypotheses. -/
theorem carrier_aligned_nested_function_universe_variants
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls out}, ¬ Step Δ (.const family ls) out)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 1)
    (hinner : env.projections inner innerInfo) (hpi : innerInfo.nparams = 0)
    (hxi : innerInfo.nindices = 0) (hfi : innerInfo.numFields = 0)
    (hshape : info.ctorType = .forallE
      (.forallE (.sort .zero) (.const inner [.param 0])) (.const family [.param 0]))
    (hInner : env.HasType univs [] (.const inner [.max .zero .zero]) (.sort (.succ .zero)))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family [.max .zero .zero]) (.sort u))
    (hS' : env.HasType univs Γ (.const family [.zero]) (.sort v))
    (hadm : (info.resultLevel.inst [.max .zero .zero]).IsNeverZero ∨
      StructureReplay.ProofFields env univs info [.max .zero .zero]) :
    (¬ StructureReplay.ProofField env univs info [.max .zero .zero] 0) ∧
    (¬ StructureReplay.ProofField env univs info [.zero] 0) ∧
    (¬ ∃ out, ScopedCompute Step (proofEraseCtx Γ) (.const family [.max .zero .zero]) out ∧
      ScopedCompute Step (proofEraseCtx Γ) (.const family [.zero]) out) ∧
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) (.const family [.zero]) x y := by
  have hw : ∀ l ∈ [VLevel.max .zero .zero], l.WF univs := by simp; trivial
  have Hctor := henv.ordered.constWF (henv.ordered.projectionConstructor hi)
  have HT := ProjTele.of (U := univs) (S := family) henv (info := info)
    (doms := [.forallE (.sort .zero) (.const inner [.param 0])])
    (c := family) (lsR := [.param 0]) (args := []) hshape Hctor hw
  have HF : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info [.max .zero .zero] i →
      ComputedJointCompare Step (proofEraseCtx Γ) true (.proj family i x) (.proj family i y) ∨
      SubsingletonCarrier (projectionType family info
        ([.forallE (.sort .zero) (.const inner [.param 0])].map (instL [VLevel.max .zero .zero]))
        i (by simp only [List.length_map, List.length_cons, List.length_nil]; omega) [] x) := by
    intro i hj _
    have E : i = 0 := by omega
    subst i
    apply Or.inr
    obtain ⟨w, hF⟩ := HT.doms 0 (by simp)
    have hF' : env.HasType univs []
        (.forallE (.sort .zero) (.const inner [.max .zero .zero])) (.sort w) := by
      simpa [instL, VLevel.inst] using hF
    obtain ⟨⟨s, hA⟩, t, hB⟩ := hF'.forallE_inv henv
    have hΓA : OnCtx [.sort .zero] (env.IsType univs) := ⟨trivial, s, hA⟩
    have EF : proofErase [] (.forallE (.sort .zero) (.const inner [.max .zero .zero])) =
        .forallE (.sort .zero) (.const inner [.max .zero .zero]) := by
      rw [show proofErase [] (.forallE (.sort .zero) (.const inner [.max .zero .zero])) =
        .forallE _ _ from if_neg (not_isProof_of_sort (Γ := []) trivial hF'),
        show proofErase [] (.sort .zero) = .sort .zero from
          if_neg (not_isProof_of_sort (Γ := []) trivial hA),
        show proofErase [.sort .zero] (.const inner [.max .zero .zero]) = .const inner [.max .zero .zero] from
          if_neg (not_isProof_of_sort hΓA hB)]
    simp only [projectionType, hp, Nat.zero_add, List.take_zero, List.reverse_nil,
      List.getElem_cons_zero, instL, VLevel.inst, List.map_cons,
      List.map_nil, List.getD_cons_zero, EF,
      projectionArgs, List.take_nil, List.range_zero, List.nil_append, ProofShape.instOuter,
      ProofShape.subst]
    exact .forallE (.unit hinner hxi hfi (ps := []) hpi.symm)
  have ES : proofErase Γ (.const family [.max .zero .zero]) = .const family [.max .zero .zero] :=
    if_neg (not_isProof_of_sort hΓ hS)
  have ES' : proofErase Γ (.const family [.zero]) = .const family [.zero] :=
    if_neg (not_isProof_of_sort hΓ hS')
  have HE : List.Forall₂ (· ≈ ·) [VLevel.max .zero .zero] [VLevel.zero] :=
    .cons (by simp [VLevel.equiv_def, VLevel.eval]) .nil
  have Hnot : ¬ StructureReplay.ProofField env univs info [.max .zero .zero] 0 := by
    rintro ⟨ds, r, hj, Hshape, Hlen, Hprop⟩
    have Hlen' : ds.length = 1 := by omega
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil (show ds ≠ [] from by intro E; simp [E] at Hlen')
    have Eds : ds = [] := List.eq_nil_of_length_eq_zero (by simpa using Hlen')
    subst ds
    have Ed := (VExpr.forallE.inj (hshape.symm.trans Hshape)).1
    subst d
    have Hprop' : env.HasType univs []
        (.forallE (.sort .zero) (.const inner [.max .zero .zero])) (.sort .zero) := by
      simpa [hp, instL, VLevel.inst] using Hprop
    have Hpos := HasType.forallE (HasType.sort (env := env) (U := univs) (Γ := []) (l := .zero) (by trivial))
      (hInner.weak0 (Γ := [.sort .zero]) henv.ordered)
    have Hzero := (Hpos.uniqU henv (by trivial) Hprop').sort_inv henv (by trivial)
    simp [VLevel.equiv_def, VLevel.eval, Lean.Nat.imax] at Hzero
  have hs := StructureReplay.family_instance_levels hi hΓ hS
  have hs' := StructureReplay.family_instance_levels hi hΓ hS'
  refine ⟨Hnot, ?_, ?_, ?_⟩
  · exact fun H => Hnot (H.congr_levels hi hs'.1 hs.1 hs'.2 (HE.flip.imp (fun _ _ E => E.symm)))
  · rintro ⟨out, RA, RB⟩
    have EA := scoped_normal_fixed RA (fun _ => ⟨fun _ H => hn H, trivial⟩)
    have EB := scoped_normal_fixed RB (fun _ => ⟨fun _ H => hn H, trivial⟩)
    cases EA.symm.trans EB
  · have H : CarrierAlignedCompare Step (proofEraseCtx Γ) false
        (proofErase Γ (.const family [.max .zero .zero])) (proofErase Γ (.const family [.zero])) := by
      rw [ES, ES']
      exact .computed (.leaf (.const HE))
    simpa only [ES'] using proofErase_carrier_aligned_nullary_nested_target
      hstep hn hi hx hp HT hΓ hS hS' H ES hadm HF

end Lean4Lean.VEnv.Strengthening
