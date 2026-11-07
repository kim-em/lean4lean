import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCountedConstructorCut

/-! # Remove whole-record eta from exposed type-projection readout

The type field introduced by structure eta is exactly the original projection.
Induction on the outer primitive budget either reads that field back with a
strict saving, contradicting minimality, or reaches a function-eta cut on a
reachable constructor. Ambient guard stages and the complete suffix remain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private rigid_spine_eq_closed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureClosedCarrierReadout
variable [Params] {D : Definitions}

/-- A single primitive selection after native structure eta returns the
original type projection. Unlike a computation triangle, this records exactly
one primitive, so its cost can be charged in a continuation induction. -/
theorem proofErase_closed_structure_type_projection_primitive
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hj : i < info.numFields)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (ht : env.HasType univs Γ (.proj family i m) (.sort u))
    (R : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target) :
    Primitive D (.proj family i target) (.proj family i (proofErase Γ m)) := by
  cases R with
  | intro hi' hx ha hp RN =>
    obtain ⟨A, hmA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hm RN
    obtain ⟨v, hA⟩ := hmA.isType henv hΓ
    have EC := rigid_spine_eq_closed hΓ (henv.projectionRigid hi) (henv.projectionRigid hi')
      hA (hmA.uniqU henv hΓ hm) EA
    obtain ⟨rfl, rfl, rfl⟩ := ProofShape.const_spine_inj (ps' := []) EC
    cases henv.ordered.projections_unique hi hi'
    have hc := (StructureReplay.expansion_typed_iff henv hΓ hi (params := []) hp hx hm).2 ha
    have hn : ¬ StructureReplay.ProofField env univs info [] i := by
      intro H
      exact not_isProof_of_sort hΓ ht ((structure_proofField_iff hΓ hi hp hj hc).1 H)
    rename_i family
    have RR : Primitive D (.proj family i (nativeStructureOutput family info [] [] (proofErase Γ m)))
        (nativeStructureField family info [] (proofErase Γ m) i) := by
      apply Primitive.projIota hi
      · simp only [List.length_append, List.length_map, List.length_range, hp]
      · rw [List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
        simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some]
    simpa only [nativeStructureField, if_neg hn] using RR

/-- A remaining function-eta computation case. Its source is an actually typed
pair reachable from the original major. The exact prefix, nonproof next
argument, earlier ambient guard and full major continuation are stored in the
cut; a final selection and field tail reach the requested output. Reading this
function-eta case is still open. -/
def PairFunctionEtaProjection (D : Definitions) (n : Nat) (Γ : List VExpr)
    (family : Name) (info : VProjectionInfo) (source out : ProofShape) : Prop :=
  ∃ m field value major result,
    env.HasType univs Γ m (.const family []) ∧
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) source (proofErase Γ m) ∧
    proofErase Γ m = ProofShape.mkApps (.const info.ctorName []) [field, value] ∧
    RigidSpineEtaCut D n (proofEraseCtx Γ) info.ctorName [] [field, value] major
      (fun k levels pre pending target =>
        NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) (proofEraseCtx Γ)
          (ProofShape.mkApps (.const info.ctorName levels) pre) target ∧
        pre.length < 2 ∧ pending ≠ [] ∧ ∀ rest, pending ≠ .proof :: rest) ∧
    Primitive D (.proj family 0 major) result ∧
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) result out

/-- Prefixing the source history preserves the entire concrete eta witness. -/
theorem PairFunctionEtaProjection.prefix
    (H : PairFunctionEtaProjection D n Γ family info middle out)
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) source middle) :
    PairFunctionEtaProjection D n Γ family info source out := by
  obtain ⟨m, field, value, major, result, hm, RM, EM, HC, RI, RT⟩ := H
  exact ⟨m, field, value, major, result, hm, R.trans RM, EM, HC, RI, RT⟩

/-- A selected type projection either reads its original field with strictly
fewer primitive occurrences, or has a function-eta witness at a reachable pair.
Whole-record structure eta is eliminated by strong induction on the supplied
count and minimality of the original projection computation. The arbitrary
continuation stays at the original stage throughout. -/
theorem proofErase_pi_inert_pair_projection_count_readout_or_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (RI : Primitive D (.proj family 0 (proofErase Γ m)) field)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (R : ScopedComputeCount (PiInertStage D n) bound (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out) :
    (∃ j, j < bound ∧ ScopedComputeCount (PiInertStage D n) j (proofEraseCtx Γ) field out) ∨
    PairFunctionEtaProjection D n Γ family info (proofErase Γ m) out := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
  have hprim : ∀ {Δ a b}, Primitive D a b → PiInertStage D n Δ a b :=
    fun H => pi_inert_stage_core (.inl (.inl (.inl H)))
  induction bound using Nat.strongRecOn generalizing m field with
  | ind bound ih =>
    obtain ⟨cost, RC, Hmin⟩ := R.forget.minimal_count
    have hcost := Hmin _ R
    have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
    have HT : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) (.sort (.succ .zero)) :=
      ⟨Γ, .proj family 0 m, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩
    obtain ⟨major, result, cp, ct, hsplit, RM, RS, RF⟩ :=
      pi_inert_sorted_projection_selection_count heq hs HT hout hproj RC
    have hmajor : ∀ A b rest, major ≠ ProofShape.mkApps (.lam A b) rest := by
      cases RS with
      | projIota =>
        intro A b rest E
        have HH := congrArg ProofShape.constHead E
        simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
        cases HH
    obtain ⟨value, EM⟩ := proofErase_closed_pair_selection_shape hi hp hf hz hadm hΓ hm RI
    have HTM : TypedSource (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName []) [field, value]) := ⟨Γ, m, _, hΓ, rfl, hm, EM⟩
    rcases pi_inert_counted_rigid_spine_readout_or_eta_cut heq hs (henv.projectionCtorRigid hi)
        hD HTM hmajor (EM ▸ RM) with ⟨levels, args, ca, hca, EO, HL, HA⟩ | HC
    · cases HL
      cases HA with | cons RA HA =>
        cases HA with | cons _ HA =>
          cases HA
          rename_i cA A cV v RV
          have RI' : Primitive D (.proj family 0 major) A := by
            rw [EO]
            exact .projIota hi (by simp [hp, hf]) (by simp [hp])
          have E := RI'.projection_deterministic RS
          exact .inl ⟨_, by omega, (E ▸ RA).trans RF⟩
    · have HC' := RigidSpineEtaCut.closed_record (ls := []) (args := [field, value])
        heq hs hi hΓ hm EM hmajor HC
      obtain ⟨mc, levels, pre, pending, target, before, after,
        RMC, HMmin, HB, HL, HA, RP, HP, HR, RT, k, hk, HE⟩ := HC'
      have hmc := HMmin _ (EM ▸ RM)
      rcases HE with ⟨HE, hlen, hne, hproof⟩ | ⟨HE, hlen, EP⟩
      · exact .inr ⟨m, field, value, major, result, hm, .refl, EM,
          ⟨mc, levels, pre, pending, target, before, after,
            RMC, HMmin, HB, HL, HA, RP, HP, HR, RT, k, hk, HE,
            by simpa using hlen, hne, hproof⟩,
          RS, RF.forget⟩
      · subst pending
        simp only [List.append_nil, ProofShape.mkApps] at RP RT
        have RPactual : ScopedComputeCount (PiInertStage D n) before (proofEraseCtx Γ)
            (proofErase Γ m) (ProofShape.mkApps (.const info.ctorName levels) pre) := EM ▸ RP
        obtain ⟨mid, HM, EMid⟩ := proofErase_scoped_compute_realize @hd hΓ hm rfl rfl RPactual.forget
        have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D k) :=
          erased_static_structure_eta_expansion_stage_descent heq hs k
        have htMid := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ HM.hasType.2).1
        have RIeta : Primitive D (.proj family 0 target) (.proj family 0 (proofErase Γ mid)) :=
          proofErase_closed_structure_type_projection_primitive @hguard hi (by omega)
            hΓ HM.hasType.2 htMid (EMid ▸ HE)
        have Rroot : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ mid) target :=
          .base (EMid ▸ HR)
        obtain ⟨expanded, HEta, EExpanded⟩ :=
          proofErase_scoped_compute_realize @hd hΓ HM.hasType.2 rfl rfl Rroot
        have Rnext : ScopedComputeCount (PiInertStage D n) (after + 1 + ct) (proofEraseCtx Γ)
            (.proj family 0 target) out :=
          ((ScopedComputeCount.proj RT).trans (.base (hprim RS))).trans RF
        have hnext : after + 1 + ct < bound := by omega
        rcases ih _ hnext HEta.hasType.2 (EExpanded ▸ RIeta) (EExpanded ▸ Rnext) with
          ⟨j, hj, RJ⟩ | Hnext
        · have RPproj : ScopedComputeCount (PiInertStage D n) before (proofEraseCtx Γ)
              (.proj family 0 (proofErase Γ m)) (.proj family 0 (proofErase Γ mid)) := by
            rw [EMid]
            exact .proj RPactual
          have Hcontra := Hmin _ (RPproj.trans RJ)
          omega
        · have Rreach : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
              (proofErase Γ m) (proofErase Γ expanded) := by
            rw [EExpanded]
            exact RPactual.forget.trans (.base HR)
          exact .inr (Hnext.prefix Rreach)

/-- After forgetting counts, only function eta at a reachable constructor
remains in exposed pair type-projection readout. The witness can pass through
arbitrarily many structure-eta expansions, which are no longer terminal cases. -/
theorem proofErase_pi_inert_pair_projection_readout_or_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (RI : Primitive D (.proj family 0 (proofErase Γ m)) field)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out) :
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) field out ∨
    PairFunctionEtaProjection D n Γ family info (proofErase Γ m) out := by
  obtain ⟨bound, RC⟩ := R.count
  rcases proofErase_pi_inert_pair_projection_count_readout_or_function_eta
      heq hs hi hp hf hz hadm hshape hD hΓ hm RI hout hproj RC with ⟨j, _, RJ⟩ | H
  · exact .inl RJ.forget
  · exact .inr H

/-- The full checker against a sort-typed variable has the same function-eta
residue. Actual type comparison first supplies directed variable exposure;
the counted projection theorem then removes whole-record structure eta. Both
checker modes and recursive carrier argument certificates are included. -/
theorem proofErase_pi_inert_pair_projection_variable_compare_or_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (hy : env.HasType univs Γ y (.sort u)) (EY : proofErase Γ y = .bvar j)
    (RI : Primitive D (.proj family 0 (proofErase Γ m)) field)
    (H : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) mode
      (.proj family 0 (proofErase Γ m)) (.bvar j)) :
    ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) mode field (.bvar j) ∨
    PairFunctionEtaProjection D n Γ family info (proofErase Γ m) (.bvar j) := by
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  have EP : proofErase Γ (.proj family 0 m) = .proj family 0 (proofErase Γ m) :=
    if_neg (not_isProof_of_sort hΓ ht)
  have HC : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) mode
      (proofErase Γ y) (proofErase Γ (.proj family 0 m)) := by
    rw [EY, EP]
    exact .symm H
  have R := proofErase_pi_inert_type_variable_exposure heq hs hΓ hy ht HC EY
  rw [EP] at R
  have hout : ∀ A b rest, ProofShape.bvar j ≠ ProofShape.mkApps (.lam A b) rest := by
    intro A b rest E
    cases rest using List.snoc_induction with
    | nil => cases E
    | snoc rest a => rw [ProofShape.mkApps_snoc] at E; cases E
  rcases proofErase_pi_inert_pair_projection_readout_or_function_eta
      heq hs hi hp hf hz hadm hshape hD hΓ hm RI hout (by intro major E; cases E) R with RF | HF
  · exact .inl (.compute RF .refl (.leaf .refl))
  · exact .inr HF

end Lean4Lean.VEnv.Strengthening
