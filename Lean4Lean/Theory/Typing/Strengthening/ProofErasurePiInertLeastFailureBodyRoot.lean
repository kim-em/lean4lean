import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertPairFailureMinimum

/-! # Counted field ancestry below a least failed budget

Leastness supplies bounded readout for every smaller typed pair projection.
At a structure root inside a pair's eta body, its type-field history is charged
to the two actual component prefixes, rather than to the entire eta tail.
This retains the sum needed when combining that history with the remaining
observed root execution; recursive eta readout is still open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Below a least failed budget, every actual typed pair projection admits
field readout within that projection budget. This applies in any scope, with
the same fixed raw output, and follows from leastness rather than a separate
readout hypothesis. -/
theorem PiInertPairFailureBudgetMinimum.readout_below
    (H : PiInertPairFailureBudgetMinimum D family info out budget)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]))
    (R : ScopedComputeCount (PiInertStage D stage) cost Δ
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) out)
    (hsmall : cost < budget) :
    ∃ later j, j ≤ cost ∧ ScopedComputeCount (PiInertStage D later) j Δ field out := by
  classical
  by_contra hn
  have HF : PiInertPairProjectionBudgetFailure D Δ family info field value out cost := by
    refine ⟨HT, ⟨stage, R⟩, ?_⟩
    intro later j hj RJ
    exact hn ⟨later, j, hj, RJ⟩
  have HH := H Δ field value cost HF
  omega

/-- The same bounded readout is available from a smaller actual pair minimum
in the observer's own scope, including any remaining identity frames. -/
theorem PiInertPairFailureBudgetMinimum.readout_minimum_below
    (H : PiInertPairFailureBudgetMinimum D family info out budget)
    (HM : PiInertProjectionContinuationMinimum D Δ family 0 out Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) cost)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hsmall : cost < budget) :
    ∃ later j, j ≤ cost ∧ ScopedComputeCount (PiInertStage D later) j Δ field out := by
  have HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) := by
    obtain ⟨_, _, _, _, _, HT, _⟩ := HM
    exact HT
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz
    (by simp [hf]) HT
  obtain ⟨stage, R⟩ := HM.closed_record_same_scope heq hs hi hΓ EΓ hm Em
  exact H.readout_below HT R hsmall

/-- A structure root in a pair eta body has the lifted original-field history
within the SUM of its actual outer and body component budgets. Saturation
forces one pre-eta field and no pending body argument; the fresh slot remains
exact. This sharper bound does not charge any post-root body computation. -/
theorem pi_inert_pair_structure_field_prefix_budget
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (harity : info.nparams + info.numFields = 2)
    (hpre : pre.length < 2) (SD : DomainSort Δ A u)
    (HTpre : TypedSource Δ (ProofShape.mkApps (.const info.ctorName ls) pre))
    (ROuter : ScopedArgumentsCount (PiInertStage D outerStage) Δ outerCost
      [original, value] (pre ++ pending))
    (RBody : ScopedArgumentsCount (PiInertStage D bodyStage) (A :: Δ) bodyCost
      (pre.map (·.liftN 1) ++ [etaArgument u]) (bodyPre ++ bodyPending))
    (HTroot : TypedSource (A :: Δ) (ProofShape.mkApps (.const info.ctorName levels) bodyPre))
    (HE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D guardStage)
      (A :: Δ) (ProofShape.mkApps (.const info.ctorName levels) bodyPre) target) :
    bodyPending = [] ∧ ∃ short j, j ≤ outerCost+bodyCost ∧ TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D (max outerStage bodyStage)) j Δ original short ∧
      bodyPre = [short.liftN 1, etaArgument u] := by
  have hlen := TypedSource.structure_constructor_saturated
    (erased_static_structure_eta_expansion_stage_descent heq hs guardStage) hi HTroot HE
  have hargs := RBody.forget.length_eq
  simp only [List.length_append, List.length_map, List.length_singleton] at hargs
  have hprelen : pre.length = 1 := by omega
  have hnil : bodyPending = [] := List.eq_nil_of_length_eq_zero (by omega)
  cases pre with
  | nil => simp at hprelen
  | cons field rest =>
    have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hprelen)
    subst rest
    have HTfield : TypedSource Δ field :=
      (ScopedHole.appArg (.const info.ctorName ls) .hole).typed HTpre
    obtain ⟨short, j, hj, HTshort, RF, Eargs⟩ := pi_inert_single_field_eta_body_count_ancestry
      heq hs SD HTfield (by simpa only [List.map_cons, List.map_nil, List.cons_append,
        List.nil_append] using RBody)
    rw [hnil, List.append_nil] at Eargs
    simp only [List.singleton_append] at ROuter
    cases ROuter with
    | cons RFirst RRest =>
      exact ⟨hnil, short, _, by omega, HTshort,
        (RFirst.mono (pi_inert_stage_mono (Nat.le_max_left outerStage bodyStage))).trans
          (RF.mono (pi_inert_stage_mono (Nat.le_max_right outerStage bodyStage))), Eargs⟩


/-- A first body root with the remaining observation charged to the SAME
original budget as the field history. Function eta keeps the original bound;
structure eta reserves `charge` for the original field before its remaining
observed minimum. Recursive readout through these frames is still missing. -/
def PiInertPairWeightedBodyRoot (D : Definitions) (Ω : List ProofShape)
    (family : Name) (info : VProjectionInfo) (field : ProofShape) (u : VLevel)
    (out : ProofShape) (budget stage : Nat) (Ξ : List ProofShape)
    (source target : ProofShape) : Prop :=
  (∃ k, k < stage ∧
    NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Ξ source target ∧
    PiInertObservedBodyRoot D Ω family 0 out budget stage Ξ source target) ∨
  (∃ k short levels later charge, k < stage ∧ TypedSource Ω short ∧
    ScopedComputeCount (PiInertStage D later) charge Ω field short ∧
    source = ProofShape.mkApps (.const info.ctorName levels) [short.liftN 1, etaArgument u] ∧
    NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Ξ source target ∧
    PiInertObservedBodyRoot D Ω family 0 out (budget-charge) stage Ξ source target)

/-- Attach the actual observer to the first body root, reserving its bounded
original-field prefix cost in the structure case. Minimality ranges over every
raw competing endpoint and stage. Both the field history and remaining root
execution refer to this selected cut; no unrelated minimum is substituted. -/
theorem CountedEtaBodySpineCut.projected_pair_field_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hi : env.projections family info) (harity : info.nparams + info.numFields = 2)
    (hpre : pre.length < 2)
    (HTpre : TypedSource Δ (ProofShape.mkApps (.const info.ctorName ls) pre))
    (ROuter : ScopedArgumentsCount (PiInertStage D n) Δ outerCost
      [field, value] (pre ++ args)) (houter : outerCost ≤ cp)
    (HT : TypedSource Δ (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName ls) pre) args))
    (HTproj : TypedSource Δ (.proj family 0 original))
    (RN : ScopedTypeRecovery Guard Δ (ProofShape.mkApps (.const info.ctorName ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RPrefix : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName ls) pre) args))
    (REta : PiInertStage D n Δ (ProofShape.mkApps (.const info.ctorName ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const info.ctorName ls) pre).liftN 1) (etaArgument u))))
    (H : CountedEtaBodySpineCut D n Δ info.ctorName ls pre A u args major ct (ConstructorEtaBodyRoot D))
    (RObserve : ScopedComputeCount (PiInertStage D observerStage) observerCost Δ
      (.proj family 0 major) out)
    (hcost : cp+1+ct+observerCost ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family 0 original) out → cost ≤ j) :
    CountedEtaBodySpineCut D n Δ info.ctorName ls pre A u args major ct
      (PiInertPairWeightedBodyRoot D Δ family info field u out cost) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hb, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, HG⟩ := H
  have RRoot : ScopedComputeCount (PiInertStage D m) (1+tb) (A :: Δ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName ls') bodyPre) bodyPending) body' := by
    simpa only [Nat.add_zero] using
      ((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := bodyPending))).trans RT
  have RB := RP.trans (by simpa only [ProofShape.mkApps_append] using RRoot)
  obtain ⟨HTbody, _⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  have HTwhole : TypedSource (A :: Δ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName ls') bodyPre) bodyPending) := by
    simpa only [ProofShape.mkApps_append] using HTbody.pi_inert_compute heq hs RP.forget
  have HTend := HTwhole.pi_inert_compute heq hs RRoot.forget
  have HTlong := HT.pi_inert_compute heq hs
    (((ScopedComputeCount.base REta).mkApps (ScopedArgumentsCount.refl (args := args))).forget)
  have Rbeta : ScopedComputeCount (PiInertStage D n) 0 Δ
      (ProofShape.mkApps (.lam A' body') (x' :: xs'))
      (ProofShape.mkApps (body'.inst x') xs') := by
    simpa only [ProofShape.mkApps] using
      (ScopedComputeCount.beta (BetaRed.beta (A := A') (b := body') (a := x'))).mkApps
        (ScopedArgumentsCount.refl (args := xs'))
  have HTnext := HTlong.pi_inert_compute heq hs (((RF.mkApps RX).trans Rbeta).forget)
  have HTmajor := HTnext.pi_inert_compute heq hs RS.forget
  have RWhole := pi_inert_counted_lambda_body_replace RPrefix REta RD RB RX RS
  have HTobserver := HTproj.pi_inert_compute heq hs RWhole.proj.forget
  have HK : PiInertProjectionContinuationRun D Δ family 0 out (A :: Δ)
      (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs'
        (PiInertProjectionContinuation D Δ family 0 out)) body' (cs+observerCost) := by
    have RS' : ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') major := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have HTnext' : TypedSource Δ
        (ProofShape.mkApps (body'.subst (ProofShape.Subst.one x')) xs') := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    exact .application HTend (.inst WI) HTnext' RS'
      (.projection HTmajor HTobserver RObserve)
  have HRootMin : ∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j (A :: Δ)
        (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName ls') bodyPre) bodyPending) endpoint →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x') xs'
        (PiInertProjectionContinuation D Δ family 0 out) endpoint k →
      1+tb+(cs+observerCost) ≤ j+k := by
    rintro later j endpoint k RJ ⟨suffixStage, suffixCost, endpoint', tailCost, hsum, RK, tailStage, RL⟩
    have RBody : ScopedComputeCount (PiInertStage D (max m later)) (pb+j) (A :: Δ)
        (.app ((ProofShape.mkApps (.const info.ctorName ls) pre).liftN 1) (etaArgument u)) endpoint :=
      (RP.mono (pi_inert_stage_mono (Nat.le_max_left m later))).trans
        (by simpa only [ProofShape.mkApps_append] using RJ.mono (pi_inert_stage_mono (Nat.le_max_right m later)))
    have raise : ∀ {Ξ a b}, PiInertStage D n Ξ a b → PiInertStage D (max n suffixStage) Ξ a b :=
      pi_inert_stage_mono (Nat.le_max_left n suffixStage)
    have RK' : ScopedComputeCount (PiInertStage D (max n suffixStage)) suffixCost Δ
        (ProofShape.mkApps (endpoint.inst x') xs') endpoint' := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        RK.mono (pi_inert_stage_mono (Nat.le_max_right n suffixStage))
    have RAlt := pi_inert_counted_lambda_body_replace (RPrefix.mono raise) (raise REta)
      (RD.mono raise) RBody (RX.mono raise) RK'
    have RFinal := (RAlt.mono (pi_inert_stage_mono (Nat.le_max_left _ tailStage))).proj.trans
      (RL.mono (pi_inert_stage_mono (Nat.le_max_right _ tailStage)))
    have HH := hmin _ _ RFinal
    omega
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hc, hf, hb, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HTR, WI, HC, ?_⟩
  obtain ⟨k, hk, HE | HE⟩ := HG
  · exact .inl ⟨k, hk, HE, bodyPending, tb, body', cs+observerCost, _,
      by omega, HTwhole, HR, RT, HK, HRootMin⟩
  · obtain ⟨pa, hpa, RA⟩ := HA.2
    obtain ⟨_, short, charge, hcharge, HTshort, RField, EField⟩ :=
      pi_inert_pair_structure_field_prefix_budget heq hs hi harity hpre SD HTpre
        ROuter RA HTR HE
    exact .inr ⟨k, short, ls', max n m, charge, hk, HTshort, RField,
      congrArg (ProofShape.mkApps (.const info.ctorName ls')) EField, HE,
      bodyPending, tb, body', cs+observerCost, _, by omega, HTwhole, HR, RT, HK, HRootMin⟩


/-- The exact original pair's globally minimum function-eta path reaches a
first body root with the joint field/observer budget. The original binder's
domain sort is retained for later field descent. No reachable replacement
pair or uncounted field ancestry is introduced before selecting this cut. -/
theorem PiInertDirectPairFunctionEtaMinimum.weighted_body_cut
    (H : PiInertDirectPairFunctionEtaMinimum D Δ family info field value out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs) :
    ∃ stage pre pending A u major after, DomainSort Δ A u ∧
      CountedEtaBodySpineCut D stage Δ info.ctorName [] pre A u pending major after
        (PiInertPairWeightedBodyRoot D Δ family info field u out budget) := by
  obtain ⟨HTsource, stage, majorCost, tailCost, major, result, hbudget, RM, HM, HC, RI, RF, Hfull⟩ := H
  obtain ⟨Γ, m, hΓ, EΓ, hm, EM⟩ := TypedSource.closed_constructor_realize hi hp hz
    (by simp [hf]) HTsource
  subst Δ
  obtain ⟨cost, levels, pre, pending, target, before, after,
    RC, Hmin, HB, HL, ⟨_, ca, hca, HA⟩, RP, HP, HR, RT, k, hk, HE, hpre, hne, hproof⟩ := HC
  cases HL
  have hcost := Hmin _ RM
  have HmajorMin : ∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) major → cost ≤ j := by
    intro later j RJ
    have HH := HM later j RJ
    omega
  have hmajor : ∀ A b rest, major ≠ ProofShape.mkApps (.lam A b) rest := by
    cases RI with
    | projIota =>
      intro A b rest E
      have HH := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
      cases HH
  have HTwhole : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using HTsource.pi_inert_compute heq hs RP.forget
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  have HTproj : TypedSource (proofEraseCtx Γ)
      (.proj family 0 (ProofShape.mkApps (.const info.ctorName []) [field, value])) := by
    have HH : TypedSource (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) :=
      ⟨Γ, .proj family 0 m, _, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩
    simpa only [EM] using HH
  have RObserve : ScopedComputeCount (PiInertStage D stage) (1+tailCost) (proofEraseCtx Γ)
      (.proj family 0 major) out :=
    (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans RF
  cases HE with
  | intro RN SD =>
    rename_i A B u
    have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D k) :=
      erased_static_structure_eta_expansion_stage_descent heq hs k
    have HBody := globally_minimal_pi_inert_eta_body_spine_cut_nonlambda heq hs
      hguard HTwhole RN SD (by simpa only [ProofShape.mkApps_append] using RP)
      HR RT HB HmajorMin hmajor
    have HRoot := HBody.constructor_roots heq (henv.projectionCtorRigid hi) hD
    have HWeighted := HRoot.projected_pair_field_root heq hs hguard hi (by omega)
      hpre HP HA hca HTwhole HTproj RN SD
      (by simpa only [ProofShape.mkApps_append] using RP) HR RObserve
      (cost := budget) (by omega) Hfull
    exact ⟨stage, pre, pending, A, u, major, after, SD, HWeighted⟩

/-- Consequently every least failed pair budget at an exposed output has
this actual weighted first-body cut. This is a necessary configuration of a
hypothetical failure, not an assertion that such a failure exists or that the
remaining recursive readout obligation is sufficient for strengthening. -/
theorem PiInertPairProjectionBudgetFailure.weighted_body_cut
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
    ∃ stage pre pending A u major after, DomainSort Δ A u ∧
      CountedEtaBodySpineCut D stage Δ info.ctorName [] pre A u pending major after
        (PiInertPairWeightedBodyRoot D Δ family info field u out budget) :=
  (H.direct_function_eta HLeast heq hs hi hp hf hz hadm hshape hD hout hproj).weighted_body_cut
    heq hs hi hp hf hz hadm hshape hD


/-- Consume the weighted root invariant without separating its two budgets.
Function eta enters a smaller observed body; structure eta keeps the full
pair source with field charge PLUS its remaining minimum strictly below the
original budget. Closing readout under these continuations is still required. -/
theorem PiInertPairWeightedBodyRoot.observed_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertPairWeightedBodyRoot D Ω family info field u out budget stage Ξ source target) :
    (∃ A innerU smaller, smaller < budget ∧
      PiInertProjectionContinuationMinimum D Ω family 0 out (A :: Ξ)
        (.app (source.liftN 1) (etaArgument innerU)) smaller) ∨
    (∃ short levels later charge smaller, charge+smaller < budget ∧ TypedSource Ω short ∧
      ScopedComputeCount (PiInertStage D later) charge Ω field short ∧
      source = ProofShape.mkApps (.const info.ctorName levels) [short.liftN 1, etaArgument u] ∧
      PiInertProjectionContinuationMinimum D Ω family 0 out Ξ source smaller) := by
  rcases H with ⟨k, hk, HE, HO⟩ | ⟨k, short, levels, later, charge, hk, HT, RF, ES, HE, HO⟩
  · cases HE with
    | intro RN SD =>
      obtain ⟨smaller, hsmall, HM⟩ := HO.eta_descent heq hs
        (erased_static_structure_eta_expansion_stage_descent heq hs k) RN SD
      exact .inl ⟨_, _, smaller, hsmall, HM⟩
  · obtain ⟨smaller, hsmall, HM⟩ := HO.structure_minimum
      (erased_static_structure_eta_expansion_stage_descent heq hs k) HE
    exact .inr ⟨short, levels, later, charge, smaller, by omega, HT, RF, ES, HM⟩

end Lean4Lean.VEnv.Strengthening
