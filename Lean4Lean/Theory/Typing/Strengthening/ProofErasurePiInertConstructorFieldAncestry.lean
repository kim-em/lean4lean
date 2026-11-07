import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorEtaBody
import Lean4Lean.Theory.Typing.Strengthening.OrdinaryIotaCoverage

/-! # Original fields inside constructor eta bodies

Before saturation, a typed constructor cannot acquire a native structure-eta
guard. In particular, eta before a pair's type argument has only nested
function eta at its first non-level body root. The already supplied fields
remain lifted components until that root.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private eta_argument_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaSpineCut
variable [Params] {D : Definitions}

/-- A native structure guard on a typed registered constructor forces that
constructor to be saturated. The guard's family need not be supplied as the
constructor's family: actual typing identifies it. -/
theorem TypedSource.structure_constructor_saturated
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName ls) args))
    (H : NativeMaskedStructureExpansion Step Δ
      (ProofShape.mkApps (.const info.ctorName ls) args) target) :
    args.length = info.nparams + info.numFields := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HT
  obtain ⟨actual, rfl, Eargs⟩ := proofErase_const_spine_inv Ee
  cases H with
  | intro hi' hx ha hp RN =>
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht (Ee ▸ RN)
    obtain ⟨params, rfl, _⟩ := proofErase_const_spine_inv EA
    have hlen := (projection_major_family henv hΓ hi (henv.projectionRigid hi') heA).2
    simpa only [Eargs, List.length_map] using hlen

/-- An eta body that still has too few arguments for its registered
constructor cannot use structure eta at the selected body root. This refines
the very same cut, retaining its counts, endpoint, and consuming continuation.
Nested function eta remains unresolved. -/
theorem CountedEtaBodySpineCut.unsaturated_function_root
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hshort : pre.length + 1 < info.nparams + info.numFields)
    (H : CountedEtaBodySpineCut D n Δ info.ctorName ls pre A u args out ct
      (ConstructorEtaBodyRoot D)) :
    CountedEtaBodySpineCut D n Δ info.ctorName ls pre A u args out ct
      (fun m Ξ source target => ∃ k, k < m ∧
        NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Ξ source target) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, ⟨HA, HAc⟩, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, HG⟩ := H
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, ⟨HA, HAc⟩, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, ?_⟩
  obtain ⟨k, hk, HE | HE⟩ := HG
  · exact ⟨k, hk, HE⟩
  · have hlen := TypedSource.structure_constructor_saturated
      (erased_static_structure_eta_expansion_stage_descent heq hs k) hi HT HE
    have hargs := HA.length_eq
    simp only [List.length_append, List.length_map, List.length_singleton] at hargs
    omega

/-- A component already present before eta cannot acquire the new binder by
Pi-inert computation. Descent preserves its exact primitive count and finite
stage; its endpoint therefore instantiates to the same old-scope expression
for every raw argument, with no native substitution certificate. -/
theorem pi_inert_lifted_component_count_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u) (HT : TypedSource Δ field)
    (R : ScopedComputeCount (PiInertStage D n) cost (A :: Δ) (field.liftN 1) out) :
    ∃ short, TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D n) cost Δ field short ∧
      out = short.liftN 1 ∧ ∀ x, out.inst x = short := by
  obtain ⟨Γ, e, T, hΓ, rfl, ht, rfl⟩ := HT
  obtain ⟨a, ha, Ea⟩ := SD.realize hΓ
  have hΓa : OnCtx (a :: Γ) (env.IsType univs) := ⟨hΓ, u, ha⟩
  obtain ⟨e', HE, RE, EE⟩ := proofErase_scoped_compute_count_descend
    (pi_inert_stage_rule_descent heq hs) hΓ hΓa Ctx.LiftN.one ht
    (congrArg (fun rawA => rawA :: proofEraseCtx Γ) Ea) R
  refine ⟨_, ⟨Γ, e', T, hΓ, rfl, HE.hasType.2, rfl⟩, RE, EE.symm, ?_⟩
  intro x
  rw [← EE]
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
    ProofShape.lift_subst_cons, ProofShape.subst_id]

/-- Before the first body-spine root, eta after one original field preserves
that field's old-scope ancestry and the fresh slot exactly. This applies to
the actual component relation retained by `CountedEtaBodySpineCut`. -/
theorem pi_inert_single_field_eta_body_ancestry
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u) (HT : TypedSource Δ field)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) (A :: Δ))
      [field.liftN 1, etaArgument u] bodyArgs) :
    ∃ short, TypedSource Δ short ∧ ScopedCompute (PiInertStage D n) Δ field short ∧
      bodyArgs = [short.liftN 1, etaArgument u] := by
  cases HA with
  | cons RF rest =>
    cases rest with
    | cons RX last =>
      cases last
      rename_i field' slot'
      obtain ⟨cost, RC⟩ := RF.count
      obtain ⟨short, HTshort, RS, E, _⟩ :=
        pi_inert_lifted_component_count_descend heq hs SD HT RC
      have EX : slot' = etaArgument u := by
        unfold etaArgument at RX ⊢
        split at RX <;> simp only [*]
        · exact RX.pi_inert_proof_fixed
        · exact RX.pi_inert_bvar_fixed
      exact ⟨short, HTshort, RS.forget, by rw [E, EX]⟩

/-- Counted component ancestry charges the old-scope field computation to
the supplied argument budget. The fresh eta slot stays unchanged. -/
theorem pi_inert_single_field_eta_body_count_ancestry
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u) (HT : TypedSource Δ field)
    (HA : ScopedArgumentsCount (PiInertStage D n) (A :: Δ) cost
      [field.liftN 1, etaArgument u] bodyArgs) :
    ∃ short j, j ≤ cost ∧ TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D n) j Δ field short ∧
      bodyArgs = [short.liftN 1, etaArgument u] := by
  cases HA with
  | cons RF rest =>
    cases rest with
    | cons RX last =>
      cases last
      obtain ⟨short, HTshort, RS, E, _⟩ :=
        pi_inert_lifted_component_count_descend heq hs SD HT RF
      exact ⟨short, _, by omega, HTshort, RS, by rw [E, eta_argument_fixed RX.forget]⟩

/-- For eta after the pair's type field, a structure root can occur only at
the full body spine. Its first field is the lift of an original-scope
computation, and its second field is precisely the eta slot. The selected
minimum and its continuation are retained; transporting the structure root
through that continuation is still open. -/
theorem CountedEtaBodySpineCut.single_field_structure_ancestry
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (harity : info.nparams + info.numFields = 2)
    (SD : DomainSort Δ A u) (HTfield : TypedSource Δ field)
    (H : CountedEtaBodySpineCut D n Δ info.ctorName ls [field] A u args out ct
      (ConstructorEtaBodyRoot D)) :
    CountedEtaBodySpineCut D n Δ info.ctorName ls [field] A u args out ct
      (fun m Ξ source target =>
        ConstructorEtaBodyRoot D m Ξ source target ∧
        ∃ short, TypedSource Δ short ∧ ScopedCompute (PiInertStage D m) Δ field short ∧
          ∀ k, NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k)
            Ξ source target →
            ∃ levels, source = ProofShape.mkApps (.const info.ctorName levels)
              [short.liftN 1, etaArgument u]) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, ⟨HA, HAc⟩, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, HG⟩ := H
  obtain ⟨short, HTshort, Rshort, Eargs⟩ := pi_inert_single_field_eta_body_ancestry
    heq hs SD HTfield (by simpa only [List.map_cons, List.map_nil, List.cons_append,
      List.nil_append] using HA)
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, ⟨HA, HAc⟩, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC,
    HG, short, HTshort, Rshort, ?_⟩
  intro k HE
  have hlen := TypedSource.structure_constructor_saturated
    (erased_static_structure_eta_expansion_stage_descent heq hs k) hi HT HE
  have hargs := congrArg List.length Eargs
  simp only [List.length_append, List.length_cons, List.length_nil] at hargs
  have hnil : bodyPending = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [hnil, List.append_nil] at Eargs
  exact ⟨ls', congrArg (ProofShape.mkApps (.const info.ctorName ls')) Eargs⟩

/-- The pair body frontier with the original type field retained. A structure
root must be on the full pair made from an old-scope field and the fresh eta
slot; only function eta may occur before the type argument has been supplied.
Neither disjunct asserts replay of a guarded root under substitution. -/
def ConstructorEtaFieldRoot (D : Definitions) (Δ pre : List ProofShape) (u : VLevel)
    (budget m : Nat) (Ξ : List ProofShape) (source target : ProofShape) : Prop :=
  (∃ k, k < m ∧ NativeEtaExpansion
    (ErasedStaticStructureEtaExpansionStage D k) Ξ source target) ∨
  ∃ k field short c levels j, k < m ∧ pre = [field] ∧ TypedSource Δ short ∧
    j < budget ∧ ScopedComputeCount (PiInertStage D m) j Δ field short ∧
    source = ProofShape.mkApps (.const c levels) [short.liftN 1, etaArgument u] ∧
    NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Ξ source target

/-- Refine the actual pair body cut without replacing its selected minimum.
Typing of the supplied constructor prefix suffices to recover the original
field typing needed by descent. -/
theorem CountedEtaBodySpineCut.pair_field_ancestry
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (harity : info.nparams + info.numFields = 2)
    (hpre : pre.length < 2) (SD : DomainSort Δ A u)
    (HTpre : TypedSource Δ (ProofShape.mkApps (.const info.ctorName ls) pre))
    (H : CountedEtaBodySpineCut D n Δ info.ctorName ls pre A u args out ct
      (ConstructorEtaBodyRoot D)) :
    CountedEtaBodySpineCut D n Δ info.ctorName ls pre A u args out ct
      (ConstructorEtaFieldRoot D Δ pre u ct) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, ⟨HA, HAc⟩, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, HG⟩ := H
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, ⟨HA, HAc⟩, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, ?_⟩
  obtain ⟨k, hk, HE | HE⟩ := HG
  · exact .inl ⟨k, hk, HE⟩
  · have hlen := TypedSource.structure_constructor_saturated
      (erased_static_structure_eta_expansion_stage_descent heq hs k) hi HT HE
    have hargs := HA.length_eq
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
      obtain ⟨pa, hpa, RCA⟩ := HAc
      obtain ⟨short, j, hj, HTshort, Rshort, Eargs⟩ := pi_inert_single_field_eta_body_count_ancestry
        heq hs SD HTfield (by simpa only [List.map_cons, List.map_nil, List.cons_append,
          List.nil_append] using RCA)
      rw [hnil, List.append_nil] at Eargs
      exact .inr ⟨k, field, short, info.ctorName, ls', j, hk, rfl, HTshort, by omega, Rshort,
        congrArg (ProofShape.mkApps (.const info.ctorName ls')) Eargs, HE⟩

/-- The field restriction holds for the actual globally selected pair body
minimum. No separate field typing or component-path premise is required. -/
theorem PairFunctionEtaBodyMinimum.field_ancestry
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : PairFunctionEtaBodyMinimum D Γ family info source out) :
    PairFunctionEtaBodyMinimum D Γ family info source out
      (fun Δ _ pre u _ after => ConstructorEtaFieldRoot D Δ pre u after) := by
  obtain ⟨m, field, value, major, result, stage, cost, pre, pending, A, B, u, k, before, after,
    hm, Rreach, EM, RC, Hmin, HB, hpre, hne, hproof, HA, RP, hk, RN, SD, RT, HC, RI, Rtail⟩ := H
  have HT : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) :=
    ⟨Γ, m, _, hΓ, rfl, hm, EM⟩
  have HTwhole : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using HT.pi_inert_compute heq hs RP.forget
  exact ⟨m, field, value, major, result, stage, cost, pre, pending, A, B, u, k, before, after,
    hm, Rreach, EM, RC, Hmin, HB, hpre, hne, hproof, HA, RP, hk, RN, SD, RT,
    HC.pair_field_ancestry heq hs hi (by omega) hpre SD (typed_spine_head HTwhole), RI, Rtail⟩

/-- The structure branch retains a counted path from the original pair field,
including its computation before the outer eta. Its cost is smaller than the
sum of the outer prefix and eta continuation budgets. Nested function eta is
still an unresolved alternative. -/
def PairEtaOriginalFieldRoot (D : Definitions) (Δ : List ProofShape) (original : ProofShape)
    (_pre : List ProofShape) (u : VLevel) (before after m : Nat)
    (Ξ : List ProofShape) (source target : ProofShape) : Prop :=
  (∃ k, k < m ∧ NativeEtaExpansion
    (ErasedStaticStructureEtaExpansionStage D k) Ξ source target) ∨
  ∃ k short c levels later j, k < m ∧ j < before + after ∧ TypedSource Δ short ∧
    ScopedComputeCount (PiInertStage D later) j Δ original short ∧
    source = ProofShape.mkApps (.const c levels) [short.liftN 1, etaArgument u] ∧
    NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Ξ source target

/-- Compose the counted history before eta with the descended body-field
history. The bound includes both histories and is attached to the same cut. -/
theorem CountedEtaBodySpineCut.original_pair_field_budget
    (RArgs : ScopedArgumentsCount (PiInertStage D stage) Δ argumentCost
      [original, value] (pre ++ pending))
    (hargs : argumentCost ≤ before)
    (H : CountedEtaBodySpineCut D n Δ c ls pre A u args out ct
      (ConstructorEtaFieldRoot D Δ pre u ct)) :
    CountedEtaBodySpineCut D n Δ c ls pre A u args out ct
      (PairEtaOriginalFieldRoot D Δ original pre u before ct) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, HG⟩ := H
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, ?_⟩
  rcases HG with HG | ⟨k, field, short, c', levels, j, hk, Epre, HTshort, hj, Rshort, Esource, HE⟩
  · exact .inl HG
  · rw [Epre, List.singleton_append] at RArgs
    cases RArgs with
    | cons Rfirst Rrest =>
      have R := (Rfirst.mono (pi_inert_stage_mono (Nat.le_max_left stage m))).trans
        (Rshort.mono (pi_inert_stage_mono (Nat.le_max_right stage m)))
      exact .inr ⟨k, short, c', levels, max stage m, _, hk, by omega, HTshort, R, Esource, HE⟩

/-- The actual globally selected pair body minimum retains a strictly bounded
field computation from its original pair, across both the prefix and eta body.
No extra premise supplies a field path or a component budget. -/
theorem PairFunctionEtaBodyMinimum.original_field_budget
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : PairFunctionEtaBodyMinimum D Γ family info source out) :
    PairFunctionEtaBodyMinimum D Γ family info source out (PairEtaOriginalFieldRoot D) := by
  obtain ⟨m, field, value, major, result, stage, cost, pre, pending, A, B, u, k, before, after,
    hm, Rreach, EM, RC, Hmin, HB, hpre, hne, hproof, ⟨HA, ca, hca, RCA⟩, RP, hk, RN, SD, RT,
    HC, RI, Rtail⟩ := H.field_ancestry heq hs hi hp hf hΓ
  exact ⟨m, field, value, major, result, stage, cost, pre, pending, A, B, u, k, before, after,
    hm, Rreach, EM, RC, Hmin, HB, hpre, hne, hproof, ⟨HA, ca, hca, RCA⟩, RP, hk, RN, SD, RT,
    HC.original_pair_field_budget RCA hca, RI, Rtail⟩

/-- Pair projection readout now leaves only a body minimum with the original
type-field ancestry recorded. This is still a local frontier: closing its
nested eta and structure continuation cases is not assumed or proved here. -/
theorem proofErase_pi_inert_pair_projection_readout_or_field_ancestry
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
    (∃ later, ScopedCompute (PiInertStage D later) (proofEraseCtx Γ) field out) ∨
    PairFunctionEtaBodyMinimum D Γ family info (proofErase Γ m) out
      (PairEtaOriginalFieldRoot D) := by
  rcases proofErase_pi_inert_pair_projection_readout_or_eta_body heq hs hi hp hf hz hadm
    hshape hD hΓ hm RI hout hproj R with H | H
  · exact .inl H
  · exact .inr (H.original_field_budget heq hs hi hp hf hΓ)

end Lean4Lean.VEnv.Strengthening
