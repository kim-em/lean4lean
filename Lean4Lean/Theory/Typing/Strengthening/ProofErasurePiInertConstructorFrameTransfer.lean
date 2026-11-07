import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertObservedBodyRoot
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStructureProjectionSubstitution

/-! # Transfer a constructor field through a consuming application frame

A saturated parameterless constructor has a closed record assignment. Its
interpreted image cannot accept pending arguments. If the preceding body
computation retains its constructor components, the lifted type field descends
with its count and the actual suffix inherits projection minimality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A typed raw saturated constructor of a parameterless, unindexed family
has an actual closed record assignment in its realizing context. -/
theorem TypedSource.closed_constructor_realize
    (hi : env.projections family info) (hp : info.nparams = 0) (hz : info.nindices = 0)
    (hlen : fields.length = info.numFields)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) fields)) :
    ∃ Γ e, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
      env.HasType univs Γ e (.const family []) ∧
      proofErase Γ e = ProofShape.mkApps (.const info.ctorName []) fields := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨actual, rfl, Efields⟩ := proofErase_const_spine_inv Ee
  have hlen' : actual.length = info.nparams + info.numFields := by
    simp only [Efields, List.length_map] at hlen
    omega
  have hfam := structure_constructor_family hΓ hi hz hlen' ht
  exact ⟨Γ, _, hΓ, EΓ, by simpa only [hp, List.take_zero, VExpr.mkApps, List.foldl_nil] using hfam, Ee⟩

/-- An interpreted image of a typed saturated closed constructor has no
pending applications. This uses the actual application-source typing; the
context interpretation need not transport any guarded primitive. -/
theorem TypedSource.closed_constructor_image_pending_nil
    (hi : env.projections family info) (hp : info.nparams = 0) (hz : info.nindices = 0)
    (hlen : fields.length = info.numFields)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) fields))
    (W : ContextSubstitution Δ Θ τ)
    (HNext : TypedSource Θ
      (ProofShape.mkApps ((ProofShape.mkApps (.const info.ctorName []) fields).subst τ) pending)) :
    pending = [] := by
  obtain ⟨Γ, e, hΓ, EΓ, he, Ee⟩ := TypedSource.closed_constructor_realize hi hp hz hlen HT
  obtain ⟨Γ', σ, hΓ', EΓ', HS, ES⟩ := W hΓ EΓ
  have he' : env.HasType univs Γ' (e.subst σ) (.const family []) :=
    he.subst henv.orderedStrong HS hΓ'
  have Ee' : proofErase Γ' (e.subst σ) =
      (ProofShape.mkApps (.const info.ctorName []) fields).subst τ :=
    (proofErase_subst_with hΓ' HS he ES).trans (congrArg (fun e => e.subst τ) Ee)
  exact TypedSource.closed_record_pending_nil hi hΓ' EΓ' he' (Ee' ▸ HNext)

/-- Projection continuations can retain the current scope or remove a binder;
none of their frame constructors increases its length. -/
theorem PiInertProjectionContinuationRun.scope_length_le
    (H : PiInertProjectionContinuationRun D Ω family index out Δ K e ck) :
    Ω.length ≤ Δ.length := by
  induction H with
  | projection => exact Nat.le_refl _
  | application _ W _ _ _ ih =>
    cases W with
    | identity => exact ih
    | inst => simp only [List.length_cons]; omega
  | retained _ _ _ _ _ ih => simp only [List.length_cons]; omega

/-- Once a closed record reaches the observer's own scope, all remaining
frames flatten to an ordinary projection path with exactly their original
count. Scope length excludes consumption/retained frames; record typing
excludes pending arguments in identity application frames. -/
theorem PiInertProjectionContinuationRun.closed_record_same_scope
    (H : PiInertProjectionContinuationRun D Ω family index out Δ K e ck)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hscope : Δ = Ω)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ)
    (hm : env.HasType univs Γ m (.const family [])) (Ee : proofErase Γ m = e) :
    ∃ n, ScopedComputeCount (PiInertStage D n) ck Δ (.proj family index e) out := by
  induction H generalizing Γ m with
  | projection _ _ R => exact ⟨_, R⟩
  | application _ W HNext RNext HK ih =>
    cases W with
    | identity =>
      have hnil := TypedSource.closed_record_pending_nil hi hΓ EΓ hm
        (by simpa only [ProofShape.subst_id, ← Ee] using HNext)
      simp only [hnil, ProofShape.mkApps, ProofShape.subst_id] at RNext
      obtain ⟨m', HE, Em'⟩ := proofErase_scoped_compute_realize
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs _))
        hΓ hm EΓ Ee RNext.forget
      obtain ⟨later, RObserve⟩ := ih hscope hΓ EΓ HE.hasType.2 Em'
      exact ⟨_, (RNext.mono (pi_inert_stage_mono (Nat.le_max_left _ later))).proj.trans
        (RObserve.mono (pi_inert_stage_mono (Nat.le_max_right _ later)))⟩
    | inst =>
      have HL := HK.scope_length_le
      have HE := congrArg List.length hscope
      simp only [List.length_cons] at HE
      omega
  | retained _ _ _ _ HK ih =>
    have HL := HK.scope_length_le
    have HE := congrArg List.length hscope
    simp only [List.length_cons] at HE
    omega

/-- A projection-continuation minimum at a closed record in the observer's
scope supplies an ordinary counted projection computation. The selected body
path and all remaining frame costs are preserved exactly. -/
theorem PiInertProjectionContinuationMinimum.closed_record_same_scope
    (H : PiInertProjectionContinuationMinimum D Δ family index out Δ source cost)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ)
    (hm : env.HasType univs Γ m (.const family [])) (Ee : proofErase Γ m = source) :
    ∃ n, ScopedComputeCount (PiInertStage D n) cost Δ (.proj family index source) out := by
  obtain ⟨K, n, cb, ck, endpoint, _, RB, HK, hc, _⟩ := H
  obtain ⟨m', HE, Em'⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    hΓ hm EΓ Ee RB.forget
  obtain ⟨later, RObserve⟩ := HK.closed_record_same_scope heq hs hi rfl hΓ EΓ HE.hasType.2 Em'
  exact ⟨_, hc ▸ (RB.mono (pi_inert_stage_mono (Nat.le_max_left n later))).proj.trans
    (RObserve.mono (pi_inert_stage_mono (Nat.le_max_right n later)))⟩

/-- At a full pair in the observer's scope, the framed minimum reduces to
the existing counted pair readout: either its original type field reaches the
output with a strict saving, or an actual constructor function-eta case remains.
No caller supplies an unframed projection computation. -/
theorem PiInertProjectionContinuationMinimum.pair_readout_or_eta
    (H : PiInertProjectionContinuationMinimum D Δ family 0 out Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) cost)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major) :
    (∃ later j, j < cost ∧ ScopedComputeCount (PiInertStage D later) j Δ field out) ∨
    ∃ Γ, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
      GlobalPairFunctionEtaProjection D Γ family info
        (ProofShape.mkApps (.const info.ctorName []) [field, value]) out := by
  have HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) [field, value]) := by
    obtain ⟨_, _, _, _, _, HT, _⟩ := H
    exact HT
  obtain ⟨Γ, m, hΓ, EΓ, hm, Em⟩ := TypedSource.closed_constructor_realize hi hp hz
    (by simp [hf]) HT
  obtain ⟨n, R⟩ := H.closed_record_same_scope heq hs hi hΓ EΓ hm Em
  have RI : Primitive D (.proj family 0 (proofErase Γ m)) field := by
    rw [Em]
    exact .projIota hi (by simp [hp, hf]) (by simp [hp])
  have R' : ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out := by simpa only [EΓ, Em] using R
  rcases proofErase_pi_inert_pair_projection_global_count_readout_or_function_eta
    heq hs hi hp hf hz hadm hshape hD hΓ hm RI hout hproj R' with ⟨later, j, hj, RJ⟩ | HE
  · exact .inl ⟨later, j, hj, EΓ ▸ RJ⟩
  · exact .inr ⟨Γ, hΓ, EΓ, Em ▸ HE⟩

/-- Compose the transferred original-field path with same-scope framed
readout. A successful readout saves at least one primitive from their combined
budget; otherwise the remaining function eta starts at the transferred pair. -/
theorem pi_inert_transferred_pair_readout_or_eta
    (RField : ScopedComputeCount (PiInertStage D n) fieldCost Δ original field)
    (H : PiInertProjectionContinuationMinimum D Δ family 0 out Δ
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) cost)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major) :
    (∃ later j, j < fieldCost+cost ∧ ScopedComputeCount (PiInertStage D later) j Δ original out) ∨
    ∃ Γ, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
      GlobalPairFunctionEtaProjection D Γ family info
        (ProofShape.mkApps (.const info.ctorName []) [field, value]) out := by
  rcases H.pair_readout_or_eta heq hs hi hp hf hz hadm hshape hD hout hproj with
    ⟨later, j, hj, RJ⟩ | HE
  · exact .inl ⟨max n later, fieldCost+j, by omega,
      (RField.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
        (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))⟩
  · exact .inr HE

/-- With the incoming endpoint fixed, the actual application suffix and its
remaining projection continuation inherit minimality. The earlier body path
is reused verbatim; no guarded computation crosses the endpoint substitution. -/
theorem pi_inert_projection_application_tail_minimum
    (RBody : ScopedComputeCount (PiInertStage D n) cb Δ source endpoint)
    (HNext : TypedSource Θ (ProofShape.mkApps (endpoint.subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Θ
      (ProofShape.mkApps (endpoint.subst τ) pending) next)
    (HK : PiInertProjectionContinuationRun D Ω family index out Θ K next ck)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint' →
      PiInertApplicationContinuation D Θ τ pending K endpoint' k → cb+cs+ck ≤ j+k) :
    PiInertProjectionContinuationMinimum D Ω family index out Θ
      (ProofShape.mkApps (endpoint.subst τ) pending) (cs+ck) := by
  refine ⟨K, nextStage, cs, ck, next, HNext, RNext, HK, rfl, ?_⟩
  intro later j endpoint' k RJ RK
  have HH := HM n cb endpoint (j+k) RBody ⟨later, j, endpoint', k, rfl, RJ, RK⟩
  omega

/-- A counted component path from a pair with a lifted original field has
an exact old-scope field image after consumption. The second field may compute
arbitrarily; only its resulting raw image is retained. -/
theorem pi_inert_pair_components_consumed_field
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u) (HTfield : TypedSource Δ field)
    (HA : ScopedArgumentsCount (PiInertStage D n) (A :: Δ) ca
      [field.liftN 1, value] fields) :
    ∃ short value' j, j ≤ ca ∧ TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D n) j Δ field short ∧
      (ProofShape.mkApps (.const c []) fields).subst (ProofShape.Subst.one x) =
        ProofShape.mkApps (.const c []) [short, value'] := by
  cases HA with
  | cons RF rest =>
    cases rest with
    | cons RV last =>
      cases last
      rename_i fieldCost field' valueCost value'
      obtain ⟨short, HTshort, RS, _, EInst⟩ :=
        pi_inert_lifted_component_count_descend heq hs SD HTfield RF
      have E := EInst x
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] at E
      exact ⟨short, value'.subst (ProofShape.Subst.one x), _, by omega, HTshort, RS, by
        simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_cons, List.map_nil, E]⟩

/-- In the constructor-component branch of a consumed body, the same field
is available in the outer scope and the actual remaining path has a projection
minimum there. Its field cost plus remaining minimum is bounded by the original
body/continuation budget. Other body roots and retained-lambda frames are not
handled by this theorem. -/
theorem pi_inert_consumed_pair_component_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (SD : DomainSort Δ A u) (HTfield : TypedSource Δ field)
    (HT : TypedSource (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, value]))
    (RBody : ScopedComputeCount (PiInertStage D n) cb (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, value])
      (ProofShape.mkApps (.const info.ctorName []) fields))
    (HA : ScopedArgumentsCount (PiInertStage D n) (A :: Δ) ca
      [field.liftN 1, value] fields) (hca : ca ≤ cb)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (HNext : TypedSource Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) fields).subst (ProofShape.Subst.one x)) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ (ProofShape.mkApps
      ((ProofShape.mkApps (.const info.ctorName []) fields).subst (ProofShape.Subst.one x)) pending) next)
    (HK : PiInertProjectionContinuationRun D Ω family index out Δ K next ck)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, value]) endpoint →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K endpoint k →
      cb+cs+ck ≤ j+k) :
    pending = [] ∧ ∃ short value' j, j+(cs+ck) ≤ cb+cs+ck ∧ TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D n) j Δ field short ∧
      PiInertProjectionContinuationMinimum D Ω family index out Δ
        (ProofShape.mkApps (.const info.ctorName []) [short, value']) (cs+ck) := by
  have HTend := HT.pi_inert_compute heq hs RBody.forget
  have hlen := HA.forget.length_eq
  have hfields : fields.length = info.numFields := by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  have E := TypedSource.closed_constructor_image_pending_nil hi hp hz hfields HTend W HNext
  obtain ⟨short, value', j, hj, HTshort, RF, EImage⟩ :=
    pi_inert_pair_components_consumed_field (c := info.ctorName) (x := x) heq hs SD HTfield HA
  have HMinimum := pi_inert_projection_application_tail_minimum RBody HNext RNext HK HM
  refine ⟨E, short, value', j, by omega, HTshort, RF, ?_⟩
  simpa only [E, ProofShape.mkApps, EImage] using HMinimum

/-- Analyze an actual consuming frame without assuming a component-only body.
Either the frame transfers the original field into an outer-scope minimum, or
the body's first non-level constructor root has a strictly smaller minimum at
its target, retaining the complete counted component prefix and actual suffix.
The root alternative still needs constructor/field readout through later frames. -/
theorem pi_inert_consumed_pair_minimum_transfer_or_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (SD : DomainSort Δ A u) (HTfield : TypedSource Δ field)
    (HT : TypedSource (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, value]))
    (RBody : ScopedComputeCount (PiInertStage D n) cb (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, value]) endpoint)
    (W : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x))
    (HNext : TypedSource Δ (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) pending))
    (RNext : ScopedComputeCount (PiInertStage D nextStage) cs Δ
      (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) pending) next)
    (HK : PiInertProjectionContinuationRun D Ω family index out Δ K next ck)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, value]) endpoint' →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K endpoint' k →
      cb+cs+ck ≤ j+k) :
    (pending = [] ∧ ∃ short value' j, j+(cs+ck) ≤ cb+cs+ck ∧ TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D n) j Δ field short ∧
      PiInertProjectionContinuationMinimum D Ω family index out Δ
        (ProofShape.mkApps (.const info.ctorName []) [short, value']) (cs+ck)) ∨
    (∃ pre bodyPending target cp ct ca, cp+1+ct ≤ cb ∧ ca ≤ cp ∧
      ScopedArgumentsCount (PiInertStage D n) (A :: Δ) ca
        [field.liftN 1, value] (pre ++ bodyPending) ∧
      ScopedComputeCount (PiInertStage D n) cp (A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, value])
        (ProofShape.mkApps (.const info.ctorName []) (pre ++ bodyPending)) ∧
      PiInertStage D n (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
      ¬ LevelPrimitive univs (ProofShape.mkApps (.const info.ctorName []) pre) target ∧
      ScopedComputeCount (PiInertStage D n) ct (A :: Δ)
        (ProofShape.mkApps target bodyPending) endpoint ∧
      ct+cs+ck < cb+cs+ck ∧
      PiInertProjectionContinuationMinimum D Ω family index out (A :: Δ)
        (ProofShape.mkApps target bodyPending) (ct+cs+ck)) := by
  rcases RBody.const_spine_components_or_cut_counted (U := univs) with
    ⟨levels, fields, ch, ca, hcounts, rfl, HL, _, HA⟩ |
    ⟨levels, pre, bodyPending, target, cp, ct, ca, hcut, hca, HL, HA, RP, HR, HN, RT⟩
  · cases HL
    exact .inl (pi_inert_consumed_pair_component_minimum heq hs hi hp hf hz SD HTfield HT
      RBody HA (by omega) W HNext RNext HK HM)
  · cases HL
    have HKfull : PiInertProjectionContinuationRun D Ω family index out (A :: Δ)
        (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K)
        endpoint (cs+ck) :=
      .application (HT.pi_inert_compute heq hs RBody.forget) (.inst W) HNext RNext HK
    have RPrefixRoot : ScopedComputeCount (PiInertStage D n) (cp+1) (A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, value])
        (ProofShape.mkApps target bodyPending) := by
      have RR := (ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := bodyPending))
      rw [← ProofShape.mkApps_append] at RR
      simpa only [Nat.add_zero] using RP.trans RR
    refine .inr ⟨pre, bodyPending, target, cp, ct, ca, hcut, hca, HA, RP, HR, HN, RT,
      by omega, _, n, ct, cs+ck, endpoint, HT.pi_inert_compute heq hs RPrefixRoot.forget,
      RT, HKfull, by omega, ?_⟩
    intro later j endpoint' k RJ RK
    have RAlt := (RPrefixRoot.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
      (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
    have HH := HM _ _ endpoint' k RAlt RK
    omega

end Lean4Lean.VEnv.Strengthening
