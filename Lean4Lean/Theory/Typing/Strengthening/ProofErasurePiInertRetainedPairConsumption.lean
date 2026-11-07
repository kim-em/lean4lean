import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertSameScopeArguments
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress

/-! # Consume a retained pair observer in the original body scope

Same-scope frames flatten to an application followed by a projection. At an
exposed output the projection selects a constructor, forcing the retained
lambda's consuming beta. The actual later body path pulls back across its
computed annotation. Competing body paths stay in the original scope and are
run before rebuilding the retained lambda, so no forward guarded substitution
or forward annotation transport is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout typed_lambda_argument_map
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- The computed annotation supplies a native identity image backwards for
any actual body typing in the new context. Primitive count and raw endpoints
are unchanged; only the finite stage grows. -/
theorem pi_inert_count_body_backward_annotation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u)
    (RD : ScopedComputeCount (PiInertStage D domainStage) cd Δ A A')
    (HT : TypedSource (A' :: Δ) body)
    (RB : ScopedComputeCount (PiInertStage D bodyStage) cb (A' :: Δ) body endpoint) :
    ScopedComputeCount (PiInertStage D (bodyStage+domainStage)) cb (A :: Δ) body endpoint := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := SD
  obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs domainStage))
    hΓ ha EΓ Ea RD.forget
  have W : StaticStructureEtaNativeSubstitution.ImageSubstitution D domainStage
      (proofEraseCtx (a' :: Γ)) (proofEraseCtx (a :: Γ)) ProofShape.Subst.id :=
    static_structure_native_backward_context heq hs hΓ HA
    (by simpa only [EA, Ea, EΓ] using RD.forget.mono pi_inert_stage_embed)
  have W' : StaticStructureEtaNativeSubstitution.ImageSubstitution D domainStage
      (A' :: Δ) (A :: Δ) ProofShape.Subst.id := by
    intro Γ₀ hΓ₀ EΓ₀
    have EE : proofEraseCtx Γ₀ = proofEraseCtx (a' :: Γ) := by
      simpa only [proofEraseCtx, EA, EΓ] using EΓ₀
    simpa only [proofEraseCtx, Ea, EΓ] using W hΓ₀ EE
  obtain ⟨Γ', b, T, hΓ', EΓ', hb, Eb⟩ := HT
  have RR := pi_inert_compute_count_native_transport heq hs RB hΓ' hb EΓ' Eb W'
  simpa only [ProofShape.subst_id] using RR

/-- A genuine consuming exit with its globally minimum body and application
continuation in the original binder context. There is no retained alternative
in this predicate. Recursive constructor-field readout remains separate. -/
def PiInertConsumedBinderMinimum (D : Definitions) (Δ : List ProofShape)
    (family : Name) (out A source : ProofShape) (cost : Nat) : Prop :=
  ∃ n cb endpoint x args suffixStage cs next K ck,
    TypedSource (A :: Δ) source ∧
    ScopedComputeCount (PiInertStage D n) cb (A :: Δ) source endpoint ∧
    ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) ∧
    TypedSource Δ (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) args) ∧
    ScopedComputeCount (PiInertStage D suffixStage) cs Δ
      (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) args) next ∧
    PiInertProjectionContinuationRun D Δ family 0 out Δ K next ck ∧ cb+cs+ck = cost ∧
    ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j (A :: Δ) source endpoint' →
      PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) args K endpoint' k → cost ≤ j+k

/-- A retained lambda in the observer's scope is eventually consumed before
an exposed pair projection result. Flattening all later identity frames and
pulling back the chosen body path gives a consuming minimum of no greater cost.
Competitors execute entirely under the original annotation before rebuilding
the retained lambda. The already-paid annotation change is never recharged. -/
theorem pi_inert_retained_pair_consumed_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (HT : TypedSource (A :: Δ) source)
    (RB : ScopedComputeCount (PiInertStage D n) cb (A :: Δ) source body)
    (SD : DomainSort Δ A u)
    (RD : ScopedComputeCount (PiInertStage D domainStage) cd Δ A A')
    (WI : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id)
    (HK : PiInertProjectionContinuationRun D Δ family 0 out Δ K
      (ProofShape.mkApps (.lam A' body) args) ck)
    (HM : ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j (A :: Δ) source endpoint' →
      K (ProofShape.mkApps (.lam A' endpoint') args) k → cb+ck ≤ j+k) :
    ∃ smaller, smaller ≤ cb+ck ∧ PiInertConsumedBinderMinimum D Δ family out A source smaller := by
  obtain ⟨extra, stage, cm, major, observerStage, co, hc, HTfull, RM, HP, RO, EK⟩ :=
    HK.same_scope_arguments heq hs rfl
  have HSort := TypedSource.pair_first_projection_sort hi hu hp hshape HP
  obtain ⟨selected, field, cp, ct, hsel, RP, RI, RT⟩ :=
    pi_inert_sorted_projection_selection_count heq hs HSort hout hproj RO
  have RMajor := (RM.mono (pi_inert_stage_mono (Nat.le_max_left stage observerStage))).trans
    (RP.mono (pi_inert_stage_mono (Nat.le_max_right stage observerStage)))
  have RMajor' : ScopedComputeCount (PiInertStage D (max stage observerStage)) (cm+cp) Δ
      (ProofShape.mkApps (.lam A' body) (args ++ extra)) selected := by
    simpa only [ProofShape.mkApps_append] using RMajor
  have HTfull' : TypedSource Δ (ProofShape.mkApps (.lam A' body) (args ++ extra)) := by
    simpa only [ProofShape.mkApps_append] using HTfull
  have hselected : ∀ C b rest, selected ≠ ProofShape.mkApps (.lam C b) rest := by
    cases RI with
    | projIota =>
      intro C b rest E
      have HH := congrArg ProofShape.constHead E
      simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at HH
      cases HH
  rcases RMajor'.pi_inert_lambda_spine_or_beta with ⟨C, b, rest, cf, ca, _, ES, _, _⟩ |
    ⟨C, finalBody, x, rest, cf, ca, cs, hsplit, RF, RX, RS⟩
  · exact (hselected C b rest ES).elim
  · have HTlam : TypedSource Δ (.lam A' body) := typed_spine_head HTfull'
    have HTbody : TypedSource (A' :: Δ) body := (ScopedHole.lamBody A' .hole).typed HTlam
    obtain ⟨v, domainCost, bodyCost, bodyStage, _, hfun, RDomain, RBody⟩ :=
      typed_lambda_readout heq hs HTlam RF
    have RBack := pi_inert_count_body_backward_annotation heq hs SD RD HTbody RBody
    have RBodyAll := (RB.mono (pi_inert_stage_mono (Nat.le_max_left n (bodyStage+domainStage)))).trans
      (RBack.mono (pi_inert_stage_mono (Nat.le_max_right n (bodyStage+domainStage))))
    have WX : ContextSubstitution (A' :: Δ) Δ (ProofShape.Subst.one x) :=
      typed_lambda_argument_map heq hs HTfull' RX
    have WOriginal : ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) := by
      intro Γ₀ hΓ₀ EΓ₀
      simpa only [ProofShape.Subst.comp, ProofShape.Subst.id, ProofShape.subst] using
        ContextSubstitution.comp WI WX hΓ₀ EΓ₀
    have Rbeta : ScopedComputeCount (PiInertStage D (max stage observerStage)) 0 Δ
        (ProofShape.mkApps (.lam C finalBody) (x :: rest))
        (ProofShape.mkApps (finalBody.inst x) rest) := by
      simpa only [ProofShape.mkApps] using
        (ScopedComputeCount.beta (BetaRed.beta (A := C) (b := finalBody) (a := x))).mkApps
          (ScopedArgumentsCount.refl (args := rest))
    have HTnext := HTfull'.pi_inert_compute heq hs (((RF.mkApps RX).trans Rbeta).forget)
    have HTselected := HTnext.pi_inert_compute heq hs RS.forget
    have RObserve : ScopedComputeCount (PiInertStage D observerStage) (1+ct) Δ
        (.proj family 0 selected) out :=
      (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans RT
    have HTobserve : TypedSource Δ (.proj family 0 selected) :=
      HP.pi_inert_compute heq hs RP.proj.forget
    have RS' : ScopedComputeCount (PiInertStage D (max stage observerStage)) cs Δ
        (ProofShape.mkApps (finalBody.subst (ProofShape.Subst.one x)) rest) selected := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
    have HTnext' : TypedSource Δ
        (ProofShape.mkApps (finalBody.subst (ProofShape.Subst.one x)) rest) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HTnext
    refine ⟨cb+bodyCost+cs+(1+ct), by omega,
      _, cb+bodyCost, finalBody, x, rest, _, cs, selected,
      PiInertProjectionContinuation D Δ family 0 out, 1+ct,
      HT, RBodyAll, WOriginal, HTnext', RS', .projection HTselected HTobserve RObserve, rfl, ?_⟩
    rintro later j endpoint k RJ ⟨suffixStage, suffixCost, last, tailCost, hsum, RK, tailStage, RL⟩
    have RLambda : ScopedComputeCount (PiInertStage D (max stage observerStage)) (domainCost+ca) Δ
        (ProofShape.mkApps (.lam A' endpoint) (args ++ extra))
        (ProofShape.mkApps (.lam C endpoint) (x :: rest)) := by
      simpa only [Nat.add_zero] using
        ((ScopedComputeCount.lam RDomain (ScopedComputeCount.beta BetaRed.refl)).mkApps RX)
    have RBeta : ScopedComputeCount (PiInertStage D (max stage observerStage)) 0 Δ
        (ProofShape.mkApps (.lam C endpoint) (x :: rest))
        (ProofShape.mkApps (endpoint.subst (ProofShape.Subst.one x)) rest) := by
      simpa only [ProofShape.mkApps, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        (ScopedComputeCount.beta (BetaRed.beta (A := C) (b := endpoint) (a := x))).mkApps
          (ScopedArgumentsCount.refl (args := rest))
    have RStart := (RLambda.trans RBeta).mono
      (pi_inert_stage_mono (Nat.le_max_left (max stage observerStage) suffixStage))
    have RChosen := RStart.trans
      (RK.mono (pi_inert_stage_mono (Nat.le_max_right (max stage observerStage) suffixStage)))
    have RFinal := (RChosen.mono (pi_inert_stage_mono (Nat.le_max_left _ tailStage))).proj.trans
      (RL.mono (pi_inert_stage_mono (Nat.le_max_right _ tailStage)))
    have HOld : K (ProofShape.mkApps (.lam A' endpoint) args) (domainCost+ca+suffixCost+tailCost) := by
      apply (EK _ _).2
      exact ⟨_, by simpa only [ProofShape.mkApps_append, Nat.add_zero] using RFinal⟩
    have HH := HM later j endpoint _ RJ HOld
    omega


/-- Both binder-exit alternatives normalize to an actual consuming minimum.
For retained exits the final exposed pair observer forces a later beta; the
body remains in the original annotation context and the count does not grow. -/
theorem PiInertBinderExitMinimum.pair_consumed
    (H : PiInertBinderExitMinimum D Δ family out A source cost)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major) :
    ∃ smaller, smaller ≤ cost ∧ PiInertConsumedBinderMinimum D Δ family out A source smaller := by
  cases H with
  | consumed HT RB W HNext RS HK hcost HM =>
    exact ⟨cost, Nat.le_refl _, _, _, _, _, _, _, _, _, _, _, HT, RB, W, HNext, RS, HK, hcost, HM⟩
  | retained HT RB SD RD WI HK hcost HM =>
    obtain ⟨smaller, hsmall, HC⟩ := pi_inert_retained_pair_consumed_minimum
      heq hs hi hu hp hshape hout hproj HT RB SD RD WI HK (by simpa only [hcost] using HM)
    exact ⟨smaller, by omega, HC⟩

/-- A smaller weighted lifted-pair minimum reaches native eta with the original
field budget intact. The former retained-lambda alternative is eliminated by
actual later beta consumption, not by assuming immediate consumption. Recursive
readout through the native eta root itself is still missing. -/
theorem PiInertPairProjectionBudgetFailure.lifted_pair_minimum_weighted_root
    (H : PiInertPairProjectionBudgetFailure D Δ family info original originalValue out budget)
    (HLeast : PiInertPairFailureBudgetMinimum D family info out budget)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ A b args, out ≠ ProofShape.mkApps (.lam A b) args)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort Δ A u) (HTfield : TypedSource Δ field)
    (RField : ScopedComputeCount (PiInertStage D fieldStage) charge Δ original field)
    (HMin : PiInertProjectionContinuationMinimum D Δ family 0 out (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) [field.liftN 1, etaArgument u]) cost)
    (hbudget : charge+cost < budget) :
    ∃ stage pre target, PiInertPairWeightedBodyRoot D Δ family info original u out budget
      stage (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) pre) target := by
  have HE := HMin.pair_binder_exit heq hs hi hp hz (by simp [hf])
  have hu := TypedSource.constructor_uvars_zero hi H.1
  obtain ⟨smaller, hsmall, n, cb, endpoint, x, args, suffixStage, cs, next, K, ck,
    HT, RB, W, HNext, RS, HK, hcost, HM⟩ := HE.pair_consumed heq hs hi hu hp hshape hout hproj
  obtain ⟨pre, bodyPending, target, cp, ct, ca, _, _, _, _, _, _, HG⟩ :=
    H.consumed_pair_weighted_root HLeast heq hs hi hp hf hz hshape hD hout hproj
      SD HTfield RField HT RB W HNext RS HK (by omega) (by simpa only [hcost] using HM)
  exact ⟨_, pre, target, HG⟩

end Lean4Lean.VEnv.Strengthening
