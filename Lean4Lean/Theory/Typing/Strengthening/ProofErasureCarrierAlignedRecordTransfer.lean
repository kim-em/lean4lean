import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecordVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNestedTransfer
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFieldRealization

/-! # Recursive record-carrier transport through universe variants

Record guards recurse through dependent field recipes at arbitrary depth. Leaves
may use the entire computed comparison language or structural subsingletons;
endpoint computations, carrier beta computation and symmetry are retained.
Primitive carrier computation and general function-carrier checking remain
separate obligations. All its
certificates embed in the existing computed carrier grammar.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

namespace ProofShape
/-- Recursive record checking with computed endpoint leaves and finite carrier
beta paths. Primitive carrier computation and function guards require separate
transport arguments; neither
is implicitly assumed by this certificate. -/
inductive RecordCarrierGuard (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → ProofShape → ProofShape → ProofShape → Prop where
  | checked : ComputedJointCompare Step Δ true a b → RecordCarrierGuard Step Δ A a b
  | subsingleton : SubsingletonCarrier A → RecordCarrierGuard Step Δ A a b
  | fields (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
        ComputedJointCompare Step Δ true (.proj family i a) (.proj family i b)) :
      RecordCarrierGuard Step Δ (mkApps (.const family ls) ps) a b
  | nested (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (HT : ProjTele env univs family info ls doms result)
      (H : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
        RecordCarrierGuard Step Δ
          (projectionType family info doms i (by have := HT.numFields; omega) ps a)
          (.proj family i a) (.proj family i b)) :
      RecordCarrierGuard Step Δ (mkApps (.const family ls) ps) a b
  | symm : RecordCarrierGuard Step Δ A a b → RecordCarrierGuard Step Δ A b a
  | reduce : ScopedCompute Step Δ a a' → ScopedCompute Step Δ b b' →
      RecordCarrierGuard Step Δ A a' b' → RecordCarrierGuard Step Δ A a b
  | beta : ProofShape.BetaRed A A' → RecordCarrierGuard Step Δ A' a b →
      RecordCarrierGuard Step Δ A a b

/-- Recursive record certificates are ordinary computed carrier certificates,
not new primitive equality or recovery rules. -/
theorem RecordCarrierGuard.computed (H : RecordCarrierGuard Step Δ A a b) :
    ComputedJointCarrierGuard Step Δ A a b := by
  induction H with
  | checked H => exact .carrierChecked H
  | subsingleton H => exact .carrierSubsingleton H
  | fields hi hx hp hadm H => exact .carrierIntro hi hx hp hadm H
  | nested hi hx hp hadm HT H ih => exact .carrierNested hi hx hp hadm HT ih
  | symm _ ih => exact .carrierSymm ih
  | reduce RA RB _ ih => exact .carrierReduce RA RB ih
  | beta R _ ih => exact .carrierCompute (.beta R) ih
end ProofShape

private theorem variant_family_levels
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (V : StructuralVariant (ProofShape.mkApps (.const family ls) ps) (proofErase Γ B)) :
    ∃ ls' ps', proofErase Γ B = ProofShape.mkApps (.const family ls') ps' ∧
      List.Forall₂ StructuralVariant ps ps' ∧
      (∀ l ∈ ls, l.WF univs) ∧ (∀ l ∈ ls', l.WF univs) ∧
      ls.length = info.uvars ∧ List.Forall₂ (· ≈ ·) ls ls' := by
  obtain ⟨ls', ps', EB, HL, HP⟩ := V.constant_spine
  obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EA
  obtain ⟨args', rfl, _⟩ := proofErase_const_spine_inv EB
  obtain ⟨_, hhead⟩ := (show VExpr.WF env univs Γ (VExpr.mkApps (.const family ls) args) from ⟨_, hA⟩).of_mkApps henv hΓ
  obtain ⟨_, hhead'⟩ := (show VExpr.WF env univs Γ (VExpr.mkApps (.const family ls') args') from ⟨_, hB⟩).of_mkApps henv hΓ
  have hs := StructureReplay.family_instance_levels hi hΓ hhead
  have hs' := StructureReplay.family_instance_levels hi hΓ hhead'
  exact ⟨ls', ps', EB, HP, hs.1, hs'.1, hs.2, HL⟩

private theorem variant_type_eq
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (V : StructuralVariant (proofErase Γ A) (proofErase Γ B)) :
    env.IsDefEqU univs Γ A B :=
  (proofErase_computed_joint_compare_reflect hstep hΓ hA hB (V.computed (mode := false))).2
    rfl (not_isProof_of_sort hΓ hA) (not_isProof_of_sort hΓ hB)

private theorem record_variant_transport
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : RecordCarrierGuard Step Δ α sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (hB : env.HasType univs Γ B (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (EA : proofErase Γ A = α)
    (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (V : StructuralVariant α (proofErase Γ B)) :
    RecordCarrierGuard Step Δ (proofErase Γ B) sa sb := by
  induction H generalizing Γ a b A B v with
  | checked H => exact .checked H
  | subsingleton H => exact .subsingleton (H.variant V)
  | symm H ih => exact .symm (ih hΓ hb ha hB EΓ EA Eb Ea V)
  | reduce RA RB H ih =>
    obtain ⟨a', HA, Ea'⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, Eb'⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    exact .reduce RA RB (ih hΓ HA.hasType.2 HB.hasType.2 hB EΓ EA Ea' Eb' V)
  | beta R H ih =>
    obtain ⟨rawB', RB, VB⟩ := R.variant V
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA (.beta R)
    obtain ⟨B', HB, EB'⟩ := proofErase_scoped_compute_realize hstep hΓ hB EΓ rfl (.beta RB)
    have HG := ih hΓ (ha.defeqU_r henv hΓ ⟨_, HA⟩) (hb.defeqU_r henv hΓ ⟨_, HA⟩)
      HB.hasType.2 EΓ EA' Ea Eb (by simpa only [EB'] using VB)
    exact .beta RB (by simpa only [EB'] using HG)
  | fields hi hx hp hadm Hfields =>
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    obtain ⟨ls', ps', EB, HP, hw, hw', hl, HL⟩ := variant_family_levels hi hΓ hA hB EA V
    rw [EB]
    apply RecordCarrierGuard.fields hi hx (HP.length_eq.symm.trans hp)
    · rcases hadm with hz | hp
      · exact .inl (hz.of_equiv (VLevel.inst_congr rfl HL))
      · exact .inr (hp.level_congr henv hi hw hw' hl HL)
    · intro i hj hn
      exact Hfields i hj (fun HF => hn (HF.congr_levels hi hw hw' hl HL))
  | @nested family info ls doms result Δ ps sa sb hi hx hp hadm HT Hfields ihfields =>
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    have Hsource : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
        (proofErase Γ a) (proofErase Γ b) := by
      simpa only [EΓ, EA, Ea, Eb] using (RecordCarrierGuard.nested hi hx hp hadm HT Hfields).computed
    have HE := proofErase_computed_joint_carrier_reflect hstep hΓ ha hb Hsource
    have HAB := variant_type_eq hstep hΓ hA hB (by simpa only [EA] using V)
    have hat := ha.defeqU_r henv hΓ HAB
    obtain ⟨ls', ps', EB, HP, hw, hw', hl, HL⟩ := variant_family_levels hi hΓ hA hB EA V
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv EA
    obtain ⟨args', rfl, Eargs'⟩ := proofErase_const_spine_inv EB
    have hlen : args.length = info.nparams := by
      have := congrArg List.length Eargs
      simp only [List.length_map] at this
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    obtain ⟨doms', result', HT'⟩ := projection_telescope_exists hi hw'
    have hadm' : (info.resultLevel.inst ls').IsNeverZero ∨ StructureReplay.ProofFields env univs info ls' := by
      rcases hadm with hz | hp
      · exact .inl (hz.of_equiv (VLevel.inst_congr rfl HL))
      · exact .inr (hp.level_congr henv hi hw hw' hl HL)
    rw [EB]
    apply RecordCarrierGuard.nested hi hx (HP.length_eq.symm.trans hp) hadm' HT'
    intro i hj hn'
    have hn : ¬ StructureReplay.ProofField env univs info ls i :=
      fun HF => hn' (HF.congr_levels hi hw hw' hl HL)
    obtain ⟨F, hia, hib⟩ := structure_equal_projection_typings hΓ HE hexpa hj
    have hpa : ¬ IsProof Γ (.proj family i a) :=
      fun H => hn (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    obtain ⟨hjs, Fs, hiaFs, EFs⟩ := proofErase_projection_at_recovered_family hΓ hi HT hia hpa ha
    have hibFs := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaFs)
    have EFs' : proofErase Γ Fs = projectionType family info doms i hjs ps sa := by
      simpa only [projectionType, List.map_take, ← Eargs, Ea] using EFs
    obtain ⟨hjt, Ft, hiaFt, EFt⟩ := proofErase_projection_at_recovered_family hΓ hi HT' hia hpa hat
    have EFt' : proofErase Γ Ft = projectionType family info doms' i hjt ps' sa := by
      simpa only [projectionType, List.map_take, ← Eargs', Ea] using EFt
    obtain ⟨vt, hFt⟩ := hiaFt.isType henv hΓ
    have VF := proofErase_carrier_aligned_projection_type_parameter_variant (m := sa) HT HT' hw hw' HL hjs hjt HP
    have Epa : proofErase Γ (.proj family i a) = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa, Ea]
    have Epb : proofErase Γ (.proj family i b) = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb, Eb]
    have HF := ihfields i hj hn hΓ hiaFs hibFs hFt EΓ EFs' Epa Epb (by simpa only [EFt'] using VF)
    rwa [EFt'] at HF

/-- Arbitrarily deep dependent record guards survive structural variants of
their assigned carrier, including arbitrary finite beta paths at nested carrier
types. Endpoint computations remain in the same context, so no universe-
compatibility premise on primitive computation is needed. -/
theorem proofErase_carrier_aligned_record_variant
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (hB : env.HasType univs Γ B (.sort v))
    (V : StructuralVariant (proofErase Γ A) (proofErase Γ B))
    (H : RecordCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    RecordCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ B) (proofErase Γ a) (proofErase Γ b) :=
  record_variant_transport hstep H hΓ ha hb hB rfl rfl rfl rfl V

end Lean4Lean.VEnv.Strengthening
