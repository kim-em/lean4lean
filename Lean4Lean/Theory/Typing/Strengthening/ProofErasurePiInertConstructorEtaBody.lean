import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGlobalProjectionMinimum
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaSpineCut

/-! # A smaller guarded body in the remaining constructor eta case

Global minimality survives annotation transport to a larger stage. The body
must use a non-level root on the original constructor spine; rigidity and
continuation bypass leave only nested function eta or structure eta there.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The remaining body roots at a rigid constructor. Their actual guards use
an earlier ambient stage; this is no assumption of field readout or closure. -/
def ConstructorEtaBodyRoot (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (source target : ProofShape) : Prop :=
  ∃ k, k < n ∧
    (NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ source target ∨
     NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ source target)

/-- The same minimum body cut at a rigid head has only function/structure eta
roots. Level, ordinary core, singleton, Eq, identity and constant roots are
excluded using its existing witnesses; no new cut or minimum is selected. -/
theorem CountedEtaBodySpineCut.constructor_roots
    (heq : env.HasCanonicalEq) (hc : env.Rigid c)
    (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : CountedEtaBodySpineCut D n Δ c ls pre A u args out ct) :
    CountedEtaBodySpineCut D n Δ c ls pre A u args out ct (ConstructorEtaBodyRoot D) := by
  obtain ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, _⟩ := H
  refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending, target, pb, tb,
    hcost, hfun, hbody, RF, RX, RS, RD, HL, HA, RP, HR, HN, RT, HM, HMC, HI, HT, WI, HC, ?_⟩
  rcases static_structure_rigid_expansion_root heq hc HR.1 (ProofShape.constHead_mkApps _ _) with
    H | H | ⟨k, hk, H | H | H⟩
  · rcases H with H | H
    · exact (erased_iota_primitive_no_rigid hc hD H (ProofShape.constHead_mkApps _ _)).elim
    · exact (HN H).elim
  · exact (HC H).elim
  · exact (HI _ H).elim
  · exact ⟨k, hk, .inl H⟩
  · exact ⟨k, hk, .inr H⟩

/-- A reachable pair with a globally minimal constructor eta continuation and
a strictly smaller minimum body/continuation cut. The body can end at arbitrary
syntax; its guarded root is nested function or structure eta. Handling those
roots across the retained endpoint substitution remains open. -/
def PairFunctionEtaBodyMinimum (D : Definitions) (Γ : List VExpr)
    (family : Name) (info : VProjectionInfo) (source out : ProofShape)
    (Root : List ProofShape → List ProofShape → VLevel → Nat → List ProofShape →
      ProofShape → ProofShape → Prop := fun _ _ _ => ConstructorEtaBodyRoot D) : Prop :=
  ∃ m field value major result stage cost pre pending A B u k before after,
    env.HasType univs Γ m (.const family []) ∧
    (∃ reachStage, ScopedCompute (PiInertStage D reachStage) (proofEraseCtx Γ) source (proofErase Γ m)) ∧
    proofErase Γ m = ProofShape.mkApps (.const info.ctorName []) [field, value] ∧
    ScopedComputeCount (PiInertStage D stage) cost (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) major ∧
    (∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) major → cost ≤ j) ∧
    before + 1 + after ≤ cost ∧ pre.length < 2 ∧ pending ≠ [] ∧
    (∀ rest, pending ≠ .proof :: rest) ∧
    List.Forall₂ (ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ)) [field, value] (pre ++ pending) ∧
    ScopedComputeCount (PiInertStage D stage) before (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value])
      (ProofShape.mkApps (.const info.ctorName []) (pre ++ pending)) ∧
    k < stage ∧
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) pre) (.forallE A B) ∧
    DomainSort (proofEraseCtx Γ) A u ∧
    ScopedComputeCount (PiInertStage D stage) after (proofEraseCtx Γ)
      (ProofShape.mkApps (.lam A (.app ((ProofShape.mkApps (.const info.ctorName []) pre).liftN 1)
        (etaArgument u))) pending) major ∧
    CountedEtaBodySpineCut D stage (proofEraseCtx Γ) info.ctorName [] pre A u pending major after
      (Root (proofEraseCtx Γ) pre u) ∧
    Primitive D (.proj family 0 major) result ∧
    ∃ tailStage, ScopedCompute (PiInertStage D tailStage) (proofEraseCtx Γ) result out

/-- Global major minimality yields a strictly smaller original-scope body cut
even when annotation replay increases the stage. The final major is a selected
constructor value, so the non-lambda endpoint formulation is essential here. -/
theorem GlobalPairFunctionEtaProjection.body_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : GlobalPairFunctionEtaProjection D Γ family info source out) :
    PairFunctionEtaBodyMinimum D Γ family info source out := by
  obtain ⟨m, field, value, major, result, stage, hm, Rreach, EM, HC, ⟨globalCost, RG, HG, _⟩, RI, Rtail⟩ := H
  obtain ⟨cost, levels, pre, pending, target, before, after,
    RC, Hmin, HB, HL, HA, RP, HP, HR, RT, k, hk, HE, hpre, hne, hproof⟩ := HC
  cases HL
  have HminAll : ∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) major → cost ≤ j := by
    intro later j RJ
    have Hleft := Hmin _ (EM ▸ RG)
    have Hright := HG later j (EM ▸ RJ)
    omega
  have hmajor : ∀ A b rest, major ≠ ProofShape.mkApps (.lam A b) rest := by
    cases RI with
    | projIota =>
      intro A b rest E
      have HH := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
      cases HH
  have HT : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) := ⟨Γ, m, _, hΓ, rfl, hm, EM⟩
  have HTwhole : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using HT.pi_inert_compute heq hs RP.forget
  cases HE with
  | intro RN SD =>
    rename_i A B u
    have HCbody := globally_minimal_pi_inert_eta_body_spine_cut_nonlambda heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole RN SD
      (by simpa only [ProofShape.mkApps_append] using RP) HR RT HB HminAll hmajor
    exact ⟨m, field, value, major, result, stage, cost, pre, pending, A, B, u, k, before, after,
      hm, Rreach, EM, RC, HminAll, HB, hpre, hne, hproof, HA, RP, hk, RN, SD, RT,
      HCbody.constructor_roots heq (henv.projectionCtorRigid hi) hD, RI, Rtail⟩

/-- Every exposed pair type-projection computation either reads the original
field at some finite stage or supplies an actual smaller guarded eta-body
minimum. No body-case hypothesis or globally minimal input is supplied by the
caller; both minima are constructed from the given finite computation. -/
theorem proofErase_pi_inert_pair_projection_readout_or_eta_body
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
    PairFunctionEtaBodyMinimum D Γ family info (proofErase Γ m) out := by
  obtain ⟨bound, RC⟩ := R.count
  rcases proofErase_pi_inert_pair_projection_global_count_readout_or_function_eta
      heq hs hi hp hf hz hadm hshape hD hΓ hm RI hout hproj RC with ⟨later, j, _, RJ⟩ | H
  · exact .inl ⟨later, RJ.forget⟩
  · exact .inr (H.body_cut heq hs hi hD hΓ)

end Lean4Lean.VEnv.Strengthening
