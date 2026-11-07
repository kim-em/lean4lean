import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertObserverPredicate

/-! # Least counted pair-readout failures and bounded field transfer

Any hypothetical pair-readout failure has a least primitive budget among all
typed pairs and scopes with the same raw output. Bounded original-field paths
transfer failures to later pairs; an actual same-scope continuation supplies
their counted projection path. A strict budget saving then contradicts the
chosen least failure. This supplies a measure, not existence of a failure or
closure of every recursive eta case. Exposed-output hypotheses are still
needed by the eta readout theorems that use this measure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Least budget among hypothetical typed pair-readout failures for the fixed
family and output, allowing their actual scope and pair fields to vary. This
is a minimum condition, not an assertion that such a failure exists. -/
def PiInertPairFailureBudgetMinimum (D : Definitions) (family : Name)
    (info : VProjectionInfo) (out : ProofShape) (budget : Nat) : Prop :=
  ∀ Δ field value cost, PiInertPairProjectionBudgetFailure D Δ family info field value out cost →
    budget ≤ cost

/-- Any hypothetical failure supplies an actual least-budget failure. Its
budget is bounded by the given one, and all scope/field witnesses are retained. -/
theorem PiInertPairProjectionBudgetFailure.least
    (H : PiInertPairProjectionBudgetFailure D Δ family info field value out budget) :
    ∃ Θ short slot least, least ≤ budget ∧
      PiInertPairProjectionBudgetFailure D Θ family info short slot out least ∧
      PiInertPairFailureBudgetMinimum D family info out least := by
  classical
  induction budget using Nat.strongRecOn generalizing Δ field value with
  | ind budget ih =>
    by_cases hex : ∃ Θ short slot cost, cost < budget ∧
        PiInertPairProjectionBudgetFailure D Θ family info short slot out cost
    · obtain ⟨Θ, short, slot, cost, hc, HF⟩ := hex
      obtain ⟨Ξ, a, b, least, hl, HL, HM⟩ := ih cost hc HF
      exact ⟨Ξ, a, b, least, by omega, HL, HM⟩
    · refine ⟨Δ, field, value, budget, by omega, H, ?_⟩
      intro Ξ a b cost HC
      by_contra hn
      exact hex ⟨Ξ, a, b, cost, by omega, HC⟩

/-- A least failure's selected projection path is globally minimum over all
finite stages. A cheaper path would itself retain the no-field-readout clause
and therefore give a smaller failure. -/
theorem PiInertPairProjectionBudgetFailure.global_projection_minimum
    (H : PiInertPairProjectionBudgetFailure D Δ family info field value out budget)
    (HM : PiInertPairFailureBudgetMinimum D family info out budget) :
    ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) out → budget ≤ j := by
  intro later j RJ
  by_cases h : budget ≤ j
  · exact h
  · obtain ⟨HT, _, HN⟩ := H
    apply HM Δ field value j
    exact ⟨HT, ⟨later, RJ⟩, fun n k hk RK => HN n k (by omega) RK⟩

/-- Transfer a failure along an actual same-scope original-field computation.
The field prefix plus the later pair's projection budget must stay within the
original failed budget. The later pair may have a completely different value. -/
theorem PiInertPairProjectionBudgetFailure.transfer
    (H : PiInertPairProjectionBudgetFailure D Δ family info original value out budget)
    (RF : ScopedComputeCount (PiInertStage D n) fieldCost Δ original field)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value']))
    (R : ScopedComputeCount (PiInertStage D stage) cost Δ
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value'])) out)
    (hcost : fieldCost+cost ≤ budget) :
    PiInertPairProjectionBudgetFailure D Δ family info field value' out cost := by
  refine ⟨HT, ⟨stage, R⟩, ?_⟩
  intro later j hj RJ
  apply H.2.2 (max n later) (fieldCost+j) (by omega)
  exact (RF.mono (pi_inert_stage_mono (Nat.le_max_left _ _))).trans
    (RJ.mono (pi_inert_stage_mono (Nat.le_max_right _ _)))

/-- An actual later pair continuation in the observer's own scope supplies
the projection path needed for bounded failure transfer. No unframed readout
path or fresh minimum is assumed independently. -/
theorem PiInertPairProjectionBudgetFailure.transfer_minimum
    (H : PiInertPairProjectionBudgetFailure D Δ family info original value out budget)
    (RF : ScopedComputeCount (PiInertStage D n) fieldCost Δ original field)
    (HNext : PiInertProjectionContinuationMinimum D Δ family 0 out Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value']) cost)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (hcost : fieldCost+cost ≤ budget) :
    PiInertPairProjectionBudgetFailure D Δ family info field value' out cost := by
  have HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value']) := by
    obtain ⟨_, _, _, _, _, HT, _⟩ := HNext
    exact HT
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz
    (by simp [hf]) HT
  obtain ⟨stage, R⟩ := HNext.closed_record_same_scope heq hs hi hΓ EΓ hm Em
  exact H.transfer RF HT R hcost

/-- A least failed budget excludes any strict saving obtained by bounded field
transfer into an actual same-scope pair minimum. This is the contradiction
needed by the stable consuming-frame branch, not a blanket field-readout law. -/
theorem PiInertPairProjectionBudgetFailure.no_smaller_transfer
    (H : PiInertPairProjectionBudgetFailure D Δ family info original value out budget)
    (HM : PiInertPairFailureBudgetMinimum D family info out budget)
    (RF : ScopedComputeCount (PiInertStage D n) fieldCost Δ original field)
    (HNext : PiInertProjectionContinuationMinimum D Δ family 0 out Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value']) cost)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (hcost : fieldCost+cost ≤ budget) (hsmall : cost < budget) : False := by
  have HF := H.transfer_minimum RF HNext heq hs hi hp hf hz hcost
  have HH := HM Δ field value' cost HF
  omega

/-- A function-eta cut on this exact pair, with the original full projection
budget and global major minimum retained. No uncounted source history changes
the selected field before the cut. Its eta-body readout remains open. -/
def PiInertDirectPairFunctionEtaMinimum (D : Definitions) (Δ : List ProofShape)
    (family : Name) (info : VProjectionInfo) (field value out : ProofShape) (budget : Nat) : Prop :=
  TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) ∧
  ∃ stage majorCost tailCost major result, majorCost+1+tailCost = budget ∧
    ScopedComputeCount (PiInertStage D stage) majorCost Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) major ∧
    (∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) major → majorCost ≤ j) ∧
    RigidSpineEtaCut D stage Δ info.ctorName [] [field, value] major
      (fun k levels pre pending target =>
        NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ
          (ProofShape.mkApps (.const info.ctorName levels) pre) target ∧
        pre.length < 2 ∧ pending ≠ [] ∧ ∀ rest, pending ≠ .proof :: rest) ∧
    Primitive D (.proj family 0 major) result ∧
    ScopedComputeCount (PiInertStage D stage) tailCost Δ result out ∧
    ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) out → budget ≤ j

/-- A least failed readout at an exposed output reaches function eta directly
on its original pair. Stable components would read the original field, and a
whole-record structure root would give a strictly smaller failed pair budget.
Thus no uncounted reachability prefix or replacement of the original field is
needed before entering the remaining constructor-function-eta case. -/
theorem PiInertPairProjectionBudgetFailure.direct_function_eta
    (H : PiInertPairProjectionBudgetFailure D Δ family info field value out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major) :
    PiInertDirectPairFunctionEtaMinimum D Δ family info field value out budget := by
  obtain ⟨Γ, m, hΓ, EΓ, hm, EM⟩ := TypedSource.closed_constructor_realize hi hp hz
    (by simp [hf]) H.1
  subst Δ
  have Hmin := H.global_projection_minimum HLeast
  obtain ⟨stage, RC⟩ := H.2.1
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  have HT : ControlTyping (proofEraseCtx Γ)
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) (.sort (.succ .zero)) := by
    have HT' : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) (.sort (.succ .zero)) :=
      ⟨Γ, .proj family 0 m, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩
    simpa only [EM] using HT'
  obtain ⟨major, result, cp, ct, hsplit, RM, RS, RF⟩ :=
    pi_inert_sorted_projection_selection_count heq hs HT hout hproj RC
  have hprim : ∀ {Ξ a b}, Primitive D a b → PiInertStage D stage Ξ a b :=
    fun RI => pi_inert_stage_core (.inl (.inl (.inl RI)))
  have hbudget : cp+1+ct = budget := by
    have HH := Hmin stage (cp+1+ct) ((RM.proj.trans (.base (hprim RS))).trans RF)
    omega
  have HmajorMin : ∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) major → cp ≤ j := by
    intro later j RJ
    have Ralt := ((RJ.mono (pi_inert_stage_mono (Nat.le_max_left later stage))).proj.trans
      (.base (pi_inert_stage_mono (Nat.le_max_right later stage) (hprim RS)))).trans
      (RF.mono (pi_inert_stage_mono (Nat.le_max_right later stage)))
    have HH := Hmin _ _ Ralt
    omega
  have hmajor : ∀ A b args, major ≠ ProofShape.mkApps (.lam A b) args := by
    cases RS with
    | projIota =>
      intro A b args E
      have HH := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
      cases HH
  rcases pi_inert_counted_rigid_spine_readout_or_eta_cut heq hs (henv.projectionCtorRigid hi)
      hD H.1 hmajor RM with ⟨levels, args, ca, hca, EO, HL, HA⟩ | HC
  · cases HL
    cases HA with | cons RA HA =>
      cases HA with | cons _ HA =>
        cases HA
        rename_i cA A cV v RV
        have RI' : Primitive D (.proj family 0 major) A := by
          rw [EO]
          exact .projIota hi (by simp [hp, hf]) (by simp [hp])
        have E := RI'.projection_deterministic RS
        exact (H.2.2 stage _ (by omega) ((E ▸ RA).trans RF)).elim
  · have HC' := RigidSpineEtaCut.closed_record (ls := []) (args := [field, value])
      heq hs hi hΓ hm EM hmajor HC
    obtain ⟨mc, levels, pre, pending, target, before, after,
      RMC, HMmin, HB, HL, HA, RP, HP, HR, RT, k, hk, HE⟩ := HC'
    have hmc := HMmin _ RM
    have hcp := HmajorMin stage mc RMC
    rcases HE with ⟨HE, hlen, hne, hproof⟩ | ⟨HE, hlen, EP⟩
    · exact ⟨H.1, stage, cp, ct, major, result, hbudget, RM, HmajorMin,
        ⟨mc, levels, pre, pending, target, before, after,
          RMC, HMmin, HB, HL, HA, RP, HP, HR, RT, k, hk, HE,
          by simpa using hlen, hne, hproof⟩, RS, RF, Hmin⟩
    · subst pending
      simp only [List.append_nil, ProofShape.mkApps] at RP RT
      have hd : ErasedScopedPrimitiveDescent (PiInertStage D stage) :=
        ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs stage)
      have RPactual : ScopedComputeCount (PiInertStage D stage) before (proofEraseCtx Γ)
          (proofErase Γ m) (ProofShape.mkApps (.const info.ctorName levels) pre) := by
        simpa only [EM, ProofShape.mkApps] using RP
      obtain ⟨mid, HM, EMid⟩ := proofErase_scoped_compute_realize hd hΓ hm rfl rfl RPactual.forget
      have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D k) :=
        erased_static_structure_eta_expansion_stage_descent heq hs k
      obtain ⟨_, HTtarget, slot, ET⟩ := proofErase_native_pair_structure_field D hguard hi hp hf hz
        hadm hshape hΓ HM.hasType.2 (EMid ▸ HE)
      have Rnext : ScopedComputeCount (PiInertStage D stage) (after+1+ct) (proofEraseCtx Γ)
          (.proj family 0 target) out := (RT.proj.trans (.base (hprim RS))).trans RF
      have HF : PiInertPairProjectionBudgetFailure D (proofEraseCtx Γ) family info
          (.proj family 0 (proofErase Γ mid)) slot out (after+1+ct) := by
        refine ⟨ET ▸ HTtarget, ⟨stage, ET ▸ Rnext⟩, ?_⟩
        intro later j hj RJ
        have RPproj : ScopedComputeCount (PiInertStage D stage) before (proofEraseCtx Γ)
            (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value]))
            (.proj family 0 (proofErase Γ mid)) := by
          rw [EMid]
          exact RP.proj
        have HH := Hmin _ _ ((RPproj.mono (pi_inert_stage_mono (Nat.le_max_left stage later))).trans
          (RJ.mono (pi_inert_stage_mono (Nat.le_max_right stage later))))
        omega
      have HH := HLeast _ _ _ _ HF
      omega

/-- Enter the exact pair's eta body while preserving the prefix charge.
The counted original-field argument vector costs at most `before`, and
`before + smaller < budget`. Thus later field transfer may spend that prefix
without losing the strict failure measure. The final sorted observer is
retained through arbitrary subsequent eta frames. -/
theorem PiInertDirectPairFunctionEtaMinimum.sorted_body_minimum
    (H : PiInertDirectPairFunctionEtaMinimum D Δ family info field value out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family []))) :
    ∃ stage pre pending A B u guardStage before ca smaller,
      pre.length < 2 ∧ pending ≠ [] ∧ (∀ rest, pending ≠ .proof :: rest) ∧ ca ≤ before ∧
      ScopedArgumentsCount (PiInertStage D stage) Δ ca [field, value] (pre ++ pending) ∧
      ScopedComputeCount (PiInertStage D stage) before Δ
        (ProofShape.mkApps (.const info.ctorName []) [field, value])
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ pending)) ∧
      guardStage < stage ∧ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D guardStage) Δ
        (ProofShape.mkApps (.const info.ctorName []) pre) (.forallE A B) ∧ DomainSort Δ A u ∧
      before+smaller < budget ∧
      PiInertSortedProjectionContinuationMinimum D Δ family 0 out (.succ .zero) (A :: Δ)
        (.app ((ProofShape.mkApps (.const info.ctorName []) pre).liftN 1) (etaArgument u)) smaller := by
  obtain ⟨HTsource, stage, majorCost, tailCost, major, result, hbudget, RM, HM, HC, RI, RF, Hfull⟩ := H
  obtain ⟨Γ, m, hΓ, EΓ, hm, EM⟩ := TypedSource.closed_constructor_realize hi hp hz
    (by simp [hf]) HTsource
  subst Δ
  obtain ⟨cost, levels, pre, pending, target, before, after,
    RC, Hmin, HB, HL, ⟨_, ca, hca, HA⟩, RP, _, HR, RT, k, hk, HE, hpre, hne, hproof⟩ := HC
  cases HL
  have hcost := Hmin _ RM
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  have HTproj : ControlTyping (proofEraseCtx Γ)
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) (.sort (.succ .zero)) := by
    have HH : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) (.sort (.succ .zero)) :=
      ⟨Γ, .proj family 0 m, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩
    simpa only [EM] using HH
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D stage) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs stage)
  have HTwhole : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using HTsource.pi_inert_compute heq hs RP.forget
  have HSort : ControlTyping (proofEraseCtx Γ)
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) (pre ++ pending))) (.sort (.succ .zero)) :=
    HTproj.compute hd RP.proj.forget
  have RObserve : ScopedComputeCount (PiInertStage D stage) (1+tailCost) (proofEraseCtx Γ)
      (.proj family 0 major) out :=
    (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans RF
  have HLocal : ∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) (pre ++ pending))) out →
      budget-before ≤ j := by
    intro later j RJ
    have RR := (RP.mono (pi_inert_stage_mono (Nat.le_max_left stage later))).proj.trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right stage later)))
    have HH := Hfull _ _ RR
    omega
  cases HE with
  | intro RN SD =>
    rename_i A B u
    obtain ⟨smaller, hsmall, HMinimum⟩ := pi_inert_eta_sorted_projected_minimum heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole HSort RN SD
      (show ScopedComputeCount (PiInertStage D stage) 0 (proofEraseCtx Γ)
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ pending))
        (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) from
          by simpa only [ProofShape.mkApps_append] using ScopedComputeCount.beta BetaRed.refl)
      HR RT RObserve (cost := budget-before) (by omega) HLocal
    exact ⟨stage, pre, pending, A, B, u, k, before, ca, smaller,
      hpre, hne, hproof, hca, HA, RP, hk, RN, SD, by omega, HMinimum⟩

end Lean4Lean.VEnv.Strengthening
