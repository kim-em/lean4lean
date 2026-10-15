import Lean4Lean.Theory.Typing.Strengthening.StructureProofField

/-! # Comparison guarded by an explicit structure carrier

The supplied common type determines the family and parameters below insertion.
Each field has a closed proof certificate, an ordinary scoped comparison, or
a recursive carrier comparison using its closed field-type recipe. Carrier types
may compute before inspection. No endpoint type recovery is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

namespace ProofShape
/-- A structure carrier supplies the typing information missing from an
unindexed neutral comparison. Individual proof fields need no raw comparison. -/
inductive StructureCarrierGuard (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) : ProofShape → ProofShape → ProofShape → Prop where
  | intro (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i, i < info.numFields → StructureReplay.ProofField env univs info ls i ∨
        ScopedCompare Step Δ true (.proj family i a) (.proj family i b)) :
      StructureCarrierGuard Step Δ (mkApps (.const family ls) ps) a b
  | checked : ScopedCompare Step Δ true a b → StructureCarrierGuard Step Δ A a b
  | symm : StructureCarrierGuard Step Δ A a b → StructureCarrierGuard Step Δ A b a
  | compute : ScopedCompute Step Δ A A' → StructureCarrierGuard Step Δ A' a b →
      StructureCarrierGuard Step Δ A a b
  /-- Recursive fields retain their carrier from the closed projection recipe.
  This permits nested structures, including empty structures in data fields. -/
  | nested (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (HT : ProjTele env univs family info ls doms result)
      (H : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
        StructureCarrierGuard Step Δ
          (projectionType family info doms i (by have := HT.numFields; omega) ps a)
          (.proj family i a) (.proj family i b)) :
      StructureCarrierGuard Step Δ (mkApps (.const family ls) ps) a b

/-- The static proof-field option is unchanged by substitution; retained
projection comparisons use the existing contextual substitution theorem. -/
theorem StructureCarrierGuard.subst
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : StructureCarrierGuard Step Δ A a b) (W : ContextSubstitution Δ Δ' τ) :
    StructureCarrierGuard Step Δ' (A.subst τ) (a.subst τ) (b.subst τ) := by
  induction H generalizing Δ' τ with
  | intro hi hx hp hadm H =>
    simp only [subst_mkApps, ProofShape.subst]
    apply StructureCarrierGuard.intro hi hx (by simpa only [List.length_map] using hp) hadm
    intro i hj
    rcases H i hj with HP | HC
    · exact .inl HP
    · exact .inr (HC.subst hstep W)
  | checked H => exact .checked (H.subst hstep W)
  | symm H ih => exact .symm (ih W)
  | compute R H ih => exact .compute (R.subst hstep W) (ih W)
  | nested hi hx hp hadm HT H ih =>
    rename_i family info ls doms result ps a b
    simp only [subst_mkApps, ProofShape.subst]
    apply StructureCarrierGuard.nested hi hx (by simpa only [List.length_map] using hp) hadm HT
    intro i hj hn
    have HH := ih i hj hn W
    simpa only [projectionType_subst (args := ps) HT _ (by omega), ProofShape.subst] using HH

/-- Enlarging primitive computation enlarges the carrier guard. -/
theorem StructureCarrierGuard.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : StructureCarrierGuard Step Δ A a b) : StructureCarrierGuard Step' Δ A a b := by
  induction H with
  | intro hi hx hp hadm H =>
    apply StructureCarrierGuard.intro hi hx hp hadm
    intro i hj
    exact (H i hj).imp id (ScopedCompare.mono hstep)
  | checked H => exact .checked (H.mono hstep)
  | symm H ih => exact .symm ih
  | compute R H ih => exact .compute (R.mono hstep) ih
  | nested hi hx hp hadm HT H ih => exact .nested hi hx hp hadm HT ih

/-- Constant/projection-headed primitives cannot compute a literal universe. -/
theorem ScopedCompute.sort_fixed
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.sort u) out) : out = .sort u :=
  scoped_normal_fixed R (fun _ => ⟨fun _ H => hhead H, trivial⟩)

/-- At a universe carrier, recursive structure guards reduce to ordinary scoped
checking. The new terminal language does not itself solve proposition coverage;
its additional power there can only come through the augmented computations. -/
theorem StructureCarrierGuard.sort_checked
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : StructureCarrierGuard Step Δ (.sort u) a b) : ScopedCompare Step Δ true a b := by
  generalize E : ProofShape.sort u = A at H
  induction H generalizing u with
  | checked H => exact H
  | symm H ih => exact (ih E).symm
  | compute R H ih => exact ih ((E ▸ R).sort_fixed hhead).symm
  | intro | nested =>
    have HE := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HE
    cases HE

end ProofShape

/-- Carrier and endpoint erasures descend together. Dependent field alignment
precedes recursive comparison; proof-field certificates supply irrelevance
without a comparison of raw projection heads. -/
theorem proofErase_structure_carrier_descend (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ')
      ((proofErase Γ A).liftN n k) ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    env.IsDefEqU univs Γ a b := by
  generalize Eα : (proofErase Γ A).liftN n k = α at H
  generalize Ea : (proofErase Γ a).liftN n k = sa at H
  generalize Eb : (proofErase Γ b).liftN n k = sb at H
  induction H generalizing A a b with
  | checked HC =>
    rw [← Ea, ← Eb] at HC
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    exact (proofErase_scoped_compare_descend hstep hΓ hΓ' W rfl ha hb HC).1 (.refl ⟨_, hA⟩)
  | symm H ih => exact (ih hb ha Eα Eb Ea).symm
  | compute R H ih =>
    rw [← Eα] at R
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HE, EA'⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W hA rfl R
    exact ih (HE.defeq ha) (HE.defeq hb) EA' Ea Eb
  | intro hi hx hp hadm Hfields =>
    rename_i family info ls ps sa sb
    rw [← Ea, ← Eb] at Hfields
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv Eα
    obtain ⟨args, rfl, Eoriginal⟩ := proofErase_const_spine_inv Es
    have hlen : args.length = info.nparams := by
      have Hlen := congrArg List.length Eargs
      rw [Eoriginal] at Hlen
      simpa only [List.length_map, hp] using Hlen.symm
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply structure_neutral_fields hΓ hi hlen hx hadm ha hb
    intro i hj T hia hib
    have proof_case (HP : IsProof Γ (.proj family i a)) : env.IsDefEqU univs Γ (.proj family i a) (.proj family i b) := by
      obtain ⟨P, hiaP, hP⟩ := HP
      have hibP := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaP)
      exact ⟨_, IsDefEq.proofIrrel hP hiaP hibP⟩
    rcases Hfields i hj with HP | HC
    · exact proof_case (HP.projection hΓ hi hlen hexpa)
    by_cases hpa : IsProof Γ (.proj family i a)
    · exact proof_case hpa
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    have Ea : proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) := if_neg hpa
    have Eb : proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) := if_neg hpb
    have HC' : ProofShape.ScopedCompare Step (proofEraseCtx Γ') true
        ((proofErase Γ (.proj family i a)).liftN n k) ((proofErase Γ (.proj family i b)).liftN n k) := by
      simpa only [Ea, Eb, ProofShape.liftN] using HC
    obtain ⟨_, hT⟩ := hia.isType henv hΓ
    exact (proofErase_scoped_compare_descend hstep hΓ hΓ' W rfl hia hib HC').1 (.refl ⟨_, hT⟩)
  | nested hi hx hp hadm HT Hfields ihfields =>
    rename_i family info ls doms result ps sa sb
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv Eα
    obtain ⟨args, rfl, Eoriginal⟩ := proofErase_const_spine_inv Es
    rw [Eoriginal] at Eargs
    have hlen : args.length = info.nparams := by
      have Hlen := congrArg List.length Eargs
      simpa only [List.length_map, hp] using Hlen.symm
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    apply structure_neutral_fields hΓ hi hlen hx hadm ha hb
    intro i hj T hia hib
    by_cases HP : StructureReplay.ProofField env univs info ls i
    · obtain ⟨P, hiaP, hP⟩ := HP.projection hΓ hi hlen hexpa
      exact ⟨_, IsDefEq.proofIrrel hP hiaP
        (hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaP))⟩
    have hpa : ¬ IsProof Γ (.proj family i a) := fun H =>
      HP (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    obtain ⟨hj', F, hiaF, EF⟩ := proofErase_projection_at_recovered_family hΓ hi HT hia hpa ha
    have hibF := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaF)
    have EF' : proofErase Γ F = ProofShape.projectionType family info doms i hj'
        (args.map (proofErase Γ)) (proofErase Γ a) := by
      simpa only [ProofShape.projectionType, List.map_take] using EF
    have EFlift : (proofErase Γ F).liftN n k =
        ProofShape.projectionType family info doms i hj' ps sa := by
      rw [EF', ProofShape.projectionType_liftN HT hj' (by simp [hlen]), ← Eargs, Ea]
    have Epa : (proofErase Γ (.proj family i a)).liftN n k = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa]
      simp only [ProofShape.liftN, Ea]
    have Epb : (proofErase Γ (.proj family i b)).liftN n k = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb]
      simp only [ProofShape.liftN, Eb]
    exact ihfields i hj HP hiaF hibF EFlift Epa Epb

/-- At the original context the carrier guard reflects to equality at the
supplied common type, without any type-recovery premise. -/
theorem proofErase_structure_carrier_reflect (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) : env.IsDefEq univs Γ a b A := by
  apply IsDefEqU.of_l henv hΓ _ ha
  exact proofErase_structure_carrier_descend hstep hΓ hΓ (Ctx.LiftN.zero []) ha hb
    (by simpa only [List.length_nil, ProofShape.liftN_zero] using H)

/-- Comparisons of the retained projections suffice to construct the raw guard.
Proofness at either typed expansion has the same closed field certificate, so
no syntactically visible projection of a proof field is demanded. -/
theorem proofErase_structure_carrier_forward
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (ha : env.HasType univs Γ a (mkApps (.const family ls) ps))
    (hb : env.HasType univs Γ b (mkApps (.const family ls) ps))
    (H : ∀ i, i < info.numFields → ¬ IsProof Γ (.proj family i a) →
      ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
        (proofErase Γ (.proj family i a)) (proofErase Γ (.proj family i b))) :
    ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (mkApps (.const family ls) ps)) (proofErase Γ a) (proofErase Γ b) := by
  obtain ⟨_, hA⟩ := ha.isType henv hΓ
  rw [proofErase_const_spine hΓ hA (not_isProof_of_sort hΓ hA)]
  have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx ha).2 hadm
  have hexpb := (StructureReplay.expansion_typed_iff henv hΓ hi hp hx hb).2 hadm
  apply ProofShape.StructureCarrierGuard.intro hi hx (by simpa only [List.length_map] using hp) hadm
  intro i hj
  by_cases hpa : IsProof Γ (.proj family i a)
  · exact .inl (StructureReplay.ProofField.of_projection hΓ hi hp hj hexpa hpa)
  have hpb : ¬ IsProof Γ (.proj family i b) := fun HP =>
    hpa ((StructureReplay.ProofField.of_projection hΓ hi hp hj hexpb HP).projection hΓ hi hp hexpa)
  have HC := H i hj hpa
  have Ea : proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) := if_neg hpa
  have Eb : proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) := if_neg hpb
  exact .inr (by simpa only [Ea, Eb] using HC)

end Lean4Lean.VEnv.Strengthening
