import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertPairSelection
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProofEtaElimination

/-! # The remaining eta cases of positive-stage constructor computation

At an exposed endpoint, a minimum-count computation from a rigid constructor
either preserves all argument paths or uses function/structure eta on the
original spine. Constant and identity wrappers cannot be that cut. For a closed
record, function eta requires a proper prefix and structure eta the whole major.
This classifies the unresolved positive-stage residual; it does not assume its
field readout or claim a sufficient frontier for strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private erase_app_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- Rigid roots have only core computation or administrative/eta expansion.
The guards retain their original ambient stage, strictly below the root stage;
they are not replaced by Pi-inert guard certificates. -/
theorem static_structure_rigid_expansion_root
    (heq : env.HasCanonicalEq) (hc : env.Rigid c)
    (H : ErasedStaticStructureEtaExpansionStage D n Δ source target)
    (HH : source.constHead = some c) :
    ErasedLevelCore D source target ∨ ConstantExpansion source target ∨
      ∃ k, k < n ∧
        (NativeIdentityExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ source target ∨
         NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ source target ∨
         NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ source target) := by
  induction n with
  | zero => exact H.elim Or.inl (fun H => .inr (.inl H))
  | succ n ih =>
    rcases H with H | H | H | H | H | H
    · rcases ih H with H | H | ⟨k, hk, H⟩
      · exact .inl H
      · exact .inr (.inl H)
      · exact .inr (.inr ⟨k, by omega, H⟩)
    · cases H.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans HH)
        exact (V.not_rigid (hn ▸ hc)).elim
    · cases H with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        exact (hc.pats _ _ hp (by
          simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj HH)).elim
    · exact .inr (.inr ⟨n, by omega, .inl H⟩)
    · exact .inr (.inr ⟨n, by omega, .inr (.inl H)⟩)
    · exact .inr (.inr ⟨n, by omega, .inr (.inr H)⟩)

/-- An actual eta cut of a minimum-count rigid-spine computation. All original
argument origins, both counted path segments, prefix typing and the original
root are retained. What remains unproved is how these eta cases preserve the
selected type field through their arbitrary continuation. -/
def RigidSpineEtaCut (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (c : Name) (ls : List VLevel) (args : List ProofShape) (out : ProofShape)
    (Root : Nat → List VLevel → List ProofShape → List ProofShape → ProofShape → Prop :=
      fun k levels pre _ target =>
        NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ
          (ProofShape.mkApps (.const c levels) pre) target ∨
        NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ
          (ProofShape.mkApps (.const c levels) pre) target) : Prop :=
  ∃ cost levels pre pending target before after,
    ScopedComputeCount (PiInertStage D n) cost Δ (ProofShape.mkApps (.const c ls) args) out ∧
    (∀ j, ScopedComputeCount (PiInertStage D n) j Δ
      (ProofShape.mkApps (.const c ls) args) out → cost ≤ j) ∧
    before + 1 + after ≤ cost ∧
    List.Forall₂ (· ≈ ·) ls levels ∧
    List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args (pre ++ pending) ∧
    ScopedComputeCount (PiInertStage D n) before Δ (ProofShape.mkApps (.const c ls) args)
      (ProofShape.mkApps (.const c levels) (pre ++ pending)) ∧
    TypedSource Δ (ProofShape.mkApps (.const c levels) pre) ∧
    PiInertStage D n Δ (ProofShape.mkApps (.const c levels) pre) target ∧
    ScopedComputeCount (PiInertStage D n) after Δ (ProofShape.mkApps target pending) out ∧
    ∃ k, k < n ∧ Root k levels pre pending target

/-- At every finite stage, an exposed computation from a rigid spine retains
all argument paths or has a genuine eta cut. Minimum primitive count excludes
both kinds of beta wrapper, even at proper prefixes with pending arguments. -/
theorem pi_inert_rigid_spine_readout_or_eta_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps (.const c ls) args))
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (R : ScopedCompute (PiInertStage D n) Δ (ProofShape.mkApps (.const c ls) args) out) :
    (∃ levels args', out = ProofShape.mkApps (.const c levels) args' ∧
      List.Forall₂ (· ≈ ·) ls levels ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) Δ) args args') ∨
    RigidSpineEtaCut D n Δ c ls args out := by
  have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) c := by
    intro Ω levels params target H
    exact erased_level_recovered_stage_spine_levels heq hc hD 0 (Δ := Ω) H
  obtain ⟨cost, RC, Hmin⟩ := R.minimal_count
  rcases RC.const_spine_or_cut @hroot with H |
      ⟨levels, pre, pending, target, before, after, HB, HL, HA, RP, HR, HN, RT⟩
  · exact .inl H
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
  have HP := RP.forget.spine_cut_source_typed @hd HT
  have hwrap : ∀ {Recovery},
      (ConstantExpansion (ProofShape.mkApps (.const c levels) pre) target ∨
       NativeIdentityExpansion Recovery Δ (ProofShape.mkApps (.const c levels) pre) target) → False := by
    intro Recovery H
    obtain ⟨j, hj, RJ⟩ := pi_inert_expansion_prefix_count_bypass_nonlambda heq hs HP H RT hout
    rw [← ProofShape.mkApps_append] at RJ
    have HM := Hmin _ (RP.trans RJ)
    omega
  rcases static_structure_rigid_expansion_root heq hc HR.1 (ProofShape.constHead_mkApps _ _) with
    H | H | ⟨k, hk, H | H | H⟩
  · exact (HN H).elim
  · exact (hwrap (Recovery := PiInertStage D n) (.inl H)).elim
  · exact (hwrap (.inr H)).elim
  · exact .inr ⟨cost, levels, pre, pending, target, before, after,
      RC, Hmin, HB, HL, HA, RP, HP, HR, RT, k, hk, .inl H⟩
  · exact .inr ⟨cost, levels, pre, pending, target, before, after,
      RC, Hmin, HB, HL, HA, RP, HP, HR, RT, k, hk, .inr H⟩

/-- Structure eta can only act on the whole typed spine, because a prefix
with an argument pending has a Pi assignment. This holds for arbitrary guards. -/
theorem TypedSource.structure_eta_pending_nil
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : TypedSource Δ (ProofShape.mkApps source pending))
    (H : NativeMaskedStructureExpansion Step Δ source target) : pending = [] := by
  cases pending with
  | nil => rfl
  | cons arg rest =>
    have HT' : TypedSource Δ (ProofShape.mkApps (.app source arg) rest) := HT
    obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := typed_spine_head HT'
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨A, B, hf, _⟩ := ht.app_inv henv hΓ
    rw [← Ef] at H
    cases H with
    | intro hi _ _ _ RN =>
      obtain ⟨F, hfF, EF⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
      obtain ⟨ps, rfl, _⟩ := proofErase_const_spine_inv EF
      obtain ⟨_, hF⟩ := hfF.isType henv hΓ
      exact (IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hF
        (hfF.uniqU henv hΓ hf)).elim

/-- The two unresolved eta positions for a closed record. Function eta acts
at a proper prefix with a retained nonproof argument next; structure eta acts
at the entire major. The original minimal computation and guards are retained. -/
def ClosedRecordEtaCut (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (c : Name) (ls : List VLevel) (args : List ProofShape) (out : ProofShape) : Prop :=
  RigidSpineEtaCut D n Δ c ls args out
    (fun k levels pre pending target =>
      (NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ
        (ProofShape.mkApps (.const c levels) pre) target ∧
        pre.length < args.length ∧ pending ≠ [] ∧ ∀ rest, pending ≠ .proof :: rest) ∨
      (NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ
        (ProofShape.mkApps (.const c levels) pre) target ∧
        pre.length = args.length ∧ pending = []))

/-- For a closed record's original constructor path, the eta cut has exactly
two positions: function eta at a proper prefix, or structure eta at the whole
major. The same minimum, root stage, argument paths and continuation are used.
The theorem does not perform eta elimination or read the selected field. -/
theorem RigidSpineEtaCut.closed_record
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (EM : proofErase Γ m = ProofShape.mkApps (.const info.ctorName ls) args)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (H : RigidSpineEtaCut D n (proofEraseCtx Γ) info.ctorName ls args out) :
    ClosedRecordEtaCut D n (proofEraseCtx Γ) info.ctorName ls args out := by
  obtain ⟨cost, levels, pre, pending, target, before, after,
    RC, Hmin, HB, HL, HA, RP, HP, HR, RT, k, hk, HE⟩ := H
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
  have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D k) :=
    erased_static_structure_eta_expansion_stage_descent heq hs k
  have HT : TypedSource (proofEraseCtx Γ) (ProofShape.mkApps (.const info.ctorName ls) args) :=
    ⟨Γ, m, _, hΓ, rfl, hm, EM⟩
  have HTwhole : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName levels) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using HT.pi_inert_compute heq hs RP.forget
  refine ⟨cost, levels, pre, pending, target, before, after,
    RC, Hmin, HB, HL, HA, RP, HP, HR, RT, k, hk, ?_⟩
  have hlength := HA.length_eq
  rw [List.length_append] at hlength
  rcases HE with HE | HE
  · have hne : pending ≠ [] := by
      intro E
      obtain ⟨m', HM, EM'⟩ := proofErase_scoped_compute_realize @hd hΓ hm rfl EM RP.forget
      rw [E, List.append_nil] at EM'
      rw [← EM'] at HE
      cases HE with
      | intro RN SD =>
        obtain ⟨A, B, hmPi, _, _⟩ := proofErase_scoped_recovered_pi_descend
          @hguard hΓ hΓ (Ctx.LiftN.zero []) HM.hasType.2
          (by simpa only [List.length_nil, ProofShape.liftN_zero] using RN)
        obtain ⟨u, hS⟩ := HM.hasType.2.isType henv hΓ
        exact IsDefEqU.rigidApp_forallE_inv (args := []) (ls := []) henv hΓ
          (henv.projectionRigid hi) hS (HM.hasType.2.uniqU henv hΓ hmPi)
    have hproof : ∀ rest, pending ≠ .proof :: rest := by
      intro rest E
      obtain ⟨j, hj, RJ⟩ := pi_inert_proof_eta_spine_count_eliminate_nonlambda heq hs
        @hguard (E ▸ HTwhole) HE (E ▸ RT) hout
      have RJ' : ScopedComputeCount (PiInertStage D n) j (proofEraseCtx Γ)
          (ProofShape.mkApps (.const info.ctorName levels) (pre ++ pending)) out := by
        simpa only [E, ProofShape.mkApps_append] using RJ
      have HM := Hmin _ (RP.trans RJ')
      omega
    exact .inl ⟨HE, by have := List.length_pos_iff.2 hne; omega, hne, hproof⟩
  · have E := TypedSource.structure_eta_pending_nil @hguard HTwhole HE
    exact .inr ⟨HE, by simp only [E, List.length_nil] at hlength; omega, E⟩

/-- At an exposed major, failure of a selected pair type field to retain its
directed computation has a concrete eta witness. The two original arguments
bound function eta to prefixes of length zero or one, and structure eta to
length two. No readout or elimination of these remaining cases is assumed. -/
theorem proofErase_pi_inert_pair_selection_residual_or_eta_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (RI : Primitive D (.proj family 0 (proofErase Γ m)) field)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ m) out) :
    (∃ selected, Primitive D (.proj family 0 out) selected ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) field selected) ∨
    ∃ value, proofErase Γ m = ProofShape.mkApps (.const info.ctorName []) [field, value] ∧
      ClosedRecordEtaCut D n (proofEraseCtx Γ) info.ctorName [] [field, value] out := by
  obtain ⟨value, EM⟩ := proofErase_closed_pair_selection_shape hi hp hf hz hadm hΓ hm RI
  have HT : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) := ⟨Γ, m, _, hΓ, rfl, hm, EM⟩
  rcases pi_inert_rigid_spine_readout_or_eta_cut heq hs (henv.projectionCtorRigid hi) hD
      HT hout (EM ▸ R) with ⟨levels, args, EO, HL, HA⟩ | HC
  · cases HL
    cases HA with | cons RF HA =>
      cases HA with | cons _ HA =>
        cases HA
        refine .inl ⟨_, ?_, RF⟩
        rw [EO]
        exact .projIota hi (by simp [hp, hf]) (by simp [hp])
  · exact .inr ⟨value, EM, HC.closed_record heq hs hi hΓ hm EM hout⟩

/-- Full positive-stage computation of a pair's type projection either reads
back from its originally selected field or exhibits one of the two retained
eta cuts on a major that selects the exact final output. The final output may
be a variable, sort or other exposed non-projection expression. This reduces
the computation branch of field readout to actual constructor eta histories,
without asserting comparison closure or a solution of those histories. -/
theorem proofErase_pi_inert_pair_projection_readout_or_eta_cut
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
    ∃ value major,
      proofErase Γ m = ProofShape.mkApps (.const info.ctorName []) [field, value] ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ m) major ∧
      Primitive D (.proj family 0 major) out ∧
      ClosedRecordEtaCut D n (proofEraseCtx Γ) info.ctorName [] [field, value] major := by
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  have HT : ControlTyping (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) (.sort (.succ .zero)) :=
    ⟨Γ, .proj family 0 m, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩
  obtain ⟨major, RM, RI'⟩ := pi_inert_sorted_projection_terminal_selection heq hs HT hout hproj R
  have hmajor : ∀ A b rest, major ≠ ProofShape.mkApps (.lam A b) rest := by
    cases RI' with
    | projIota =>
      intro A b rest E
      have HE := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HE
      cases HE
  rcases proofErase_pi_inert_pair_selection_residual_or_eta_cut
      heq hs hi hp hf hz hadm hD hΓ hm RI hmajor RM with ⟨selected, RS, RF⟩ | ⟨value, EM, HC⟩
  · exact .inl ((RS.projection_deterministic RI') ▸ RF)
  · exact .inr ⟨value, major, EM, RM, RI', HC⟩

end Lean4Lean.VEnv.Strengthening
