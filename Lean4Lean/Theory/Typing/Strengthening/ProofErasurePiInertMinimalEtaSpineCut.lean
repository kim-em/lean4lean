import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaBodyInterpretation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstantContinuation

/-! # A globally minimal eta must reach a non-level body-spine root

Minimization ranges over all finite guard stages. Thus annotation transport
may enlarge the stage without preventing a strict primitive-count bypass.
The surviving root lies on the original constant-headed eta body, with all
component origins and the exact post-root and post-beta suffixes retained.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params]

private theorem eta_argument_fixed
    (R : ScopedCompute (PiInertStage D n) Δ (etaArgument u) out) : out = etaArgument u := by
  unfold etaArgument at R ⊢
  split at R <;> simp only [*]
  · exact R.pi_inert_proof_fixed
  · exact R.pi_inert_bvar_fixed

/-- The counted first non-level root on a constant-headed eta body. It
retains the consuming beta, domain cost, component ancestry, and both suffixes.
Both decompositions have exact counts, and the body path is globally minimal.
The body together with its application continuation is also minimal when both
paths and their common endpoint vary. Identity and constant expansion are excluded
at the typed root; the actual argument interprets the endpoint substitution.
The optional `Root` predicate refines this same selected root, without choosing
a second decomposition; the default adds no restriction.
This is a witnessed decomposition, not an assumed closure property. -/
def CountedEtaBodySpineCut (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (c : Name) (ls : List VLevel) (pre : List ProofShape) (A : ProofShape) (u : VLevel)
    (args : List ProofShape) (out : ProofShape) (ct : Nat)
    (Root : Nat → List ProofShape → ProofShape → ProofShape → Prop := fun _ _ _ _ => True) : Prop :=
    ∃ A' body' x' xs' cf ca cs cd cb m ls' bodyPre bodyPending target pb tb,
      cf+ca+cs = ct ∧ cd+cb = cf ∧ pb+1+tb = cb ∧
      ScopedComputeCount (PiInertStage D n) cf Δ
        (.lam A (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))) (.lam A' body') ∧
      ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs') ∧
      ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') xs') out ∧
      ScopedComputeCount (PiInertStage D n) cd Δ A A' ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧
      List.Forall₂ (ScopedCompute (PiInertStage D m) (A :: Δ))
        (pre.map (·.liftN 1) ++ [etaArgument u]) (bodyPre ++ bodyPending) ∧
      ScopedComputeCount (PiInertStage D m) pb (A :: Δ)
        (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))
        (ProofShape.mkApps (.const c ls') (bodyPre ++ bodyPending)) ∧
      PiInertStage D m (A :: Δ) (ProofShape.mkApps (.const c ls') bodyPre) target ∧
      ¬ LevelPrimitive univs (ProofShape.mkApps (.const c ls') bodyPre) target ∧
      ScopedComputeCount (PiInertStage D m) tb (A :: Δ) (ProofShape.mkApps target bodyPending) body' ∧
      (∀ later j, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
        (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u)) body' → cb ≤ j) ∧
      (∀ later suffixStage j k endpoint,
        ScopedComputeCount (PiInertStage D later) j (A :: Δ)
          (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u)) endpoint →
        ScopedComputeCount (PiInertStage D suffixStage) k Δ
          (ProofShape.mkApps (endpoint.inst x') xs') out → cb+cs ≤ j+k) ∧
      (∀ Recovery, ¬ NativeIdentityExpansion Recovery (A :: Δ)
        (ProofShape.mkApps (.const c ls') bodyPre) target) ∧
      TypedSource (A :: Δ) (ProofShape.mkApps (.const c ls') bodyPre) ∧
      ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') ∧
      ¬ ConstantExpansion (ProofShape.mkApps (.const c ls') bodyPre) target ∧
      Root m (A :: Δ) (ProofShape.mkApps (.const c ls') bodyPre) target

/-- The body selected by the cut is a globally minimum path of strictly
smaller cost than the enclosing path, whose eta root costs one primitive.
The endpoint is retained without assuming that it exposes a carrier. -/
theorem CountedEtaBodySpineCut.smaller_minimum
    {Root : Nat → List ProofShape → ProofShape → ProofShape → Prop}
    (H : CountedEtaBodySpineCut D n Δ c ls pre A u args out ct Root)
    (hcost : cp+1+ct ≤ cost) :
    ∃ cb m body', cb < cost ∧
      ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
        (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u)) body' ∧
      ∀ later j, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
        (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u)) body' → cb ≤ j := by
  obtain ⟨_, body', _, _, cf, ca, cs, cd, cb, m, _, _, _, _, pb, tb,
    hc, hf, hb, _, _, _, _, _, _, RP, HR, _, RT, HM, _, _⟩ := H
  refine ⟨cb, m, body', by omega, ?_, HM⟩
  have RT' := ((ScopedComputeCount.base HR).mkApps ScopedArgumentsCount.refl).trans RT
  rw [← ProofShape.mkApps_append] at RT'
  simpa only [Nat.add_zero, ← Nat.add_assoc, hb] using RP.trans RT'

/-- In a minimum-count path over all finite stages, eta on a constant prefix
must encounter a non-level primitive on its original body spine before the
first consuming beta. Mere argument computation and level changes are bypassed.
This locates the body root; classification of that root, including nested eta,
remains a separate obligation. Combined body/continuation minimality rules out
identity and constant expansion even if they survive until after the enclosing
beta; the actual argument supplies the required typed context interpretation. -/
theorem globally_minimal_pi_inert_eta_body_spine_cut_nonlambda
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps (ProofShape.mkApps (.const c ls) pre) args))
    (RN : ScopedTypeRecovery Guard Δ (ProofShape.mkApps (.const c ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (ProofShape.mkApps (.const c ls) pre) args))
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const c ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))) args) out)
    (hcost : cp+1+ct ≤ cost)
    (hmin : ∀ later k, ScopedComputeCount (PiInertStage D later) k Δ original out → cost ≤ k)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest) :
    CountedEtaBodySpineCut D n Δ c ls pre A u args out ct := by
  rcases RT.pi_inert_lambda_spine_or_beta with ⟨A', b', args', cf, ca, _, EO, _, _⟩ |
      ⟨A', body', x', xs', cf, ca, cs, hc, RF, RX, RS⟩
  · exact (hout A' b' args' EO).elim
  · obtain ⟨cd, cb, m, hsplit, RD, RB⟩ := pi_inert_native_eta_count_body_readout
      heq hs hguard (typed_spine_head HT) (.intro RN SD) RF
    have RBspine : ScopedComputeCount (PiInertStage D m) cb (A :: Δ)
        (ProofShape.mkApps (.const c ls) (pre.map (·.liftN 1) ++ [etaArgument u])) body' := by
      simpa only [ProofShape.mkApps_snoc, ProofShape.liftN_mkApps, ProofShape.liftN] using RB
    obtain ⟨hexact, _, hminBody⟩ := pi_inert_counted_lambda_body_minimal
      RP HR RD RB RX RS (by omega) hmin
    obtain ⟨_, hminContinuation⟩ := pi_inert_counted_lambda_continuation_minimal
      RP HR RD RB RX RS (by omega) hmin
    have hcExact : cf+ca+cs = ct := by omega
    rcases RBspine.const_spine_components_or_cut (U := univs) with
      ⟨ls', rawArgs, ch, cc, hcomponents, EO, _, RH, RA⟩ |
      ⟨ls', bodyPre, bodyPending, target, pb, tb, hcut, HL, HA, RPB, HR, HN, RTB⟩
    · obtain ⟨pre', slot', cp', cx', rfl, hargs, Rpre, Rslot⟩ := RA.snoc_inv
      obtain rfl := eta_argument_fixed Rslot.forget
      have RG : ScopedComputeCount (PiInertStage D m) (ch+cp') (A :: Δ)
          ((ProofShape.mkApps (.const c ls) pre).liftN 1) (ProofShape.mkApps (.const c ls') pre') := by
        simpa only [ProofShape.liftN_mkApps, ProofShape.liftN] using RH.mkApps Rpre
      have EB : body' = .app (ProofShape.mkApps (.const c ls') pre') (etaArgument u) := by
        simpa only [ProofShape.mkApps_snoc] using EO
      have RR := pi_inert_retained_eta_body_count_bypass heq hs hguard HT RN SD RG RX (EB ▸ RS)
      have HM := hmin _ _ ((RP.mono (pi_inert_stage_mono (Nat.le_max_right m n))).trans RR)
      omega
    · have hcutExact : pb+1+tb = cb := by
        have RT' := ((ScopedComputeCount.base HR).mkApps ScopedArgumentsCount.refl).trans RTB
        rw [← ProofShape.mkApps_append] at RT'
        have R := RPB.trans RT'
        have HM := hminBody m (pb+1+tb) (by
          simpa only [Nat.add_zero, ← Nat.add_assoc,
            ProofShape.mkApps_snoc, ProofShape.liftN_mkApps, ProofShape.liftN] using R)
        omega
      have RPB' : ScopedComputeCount (PiInertStage D m) pb (A :: Δ)
          (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))
          (ProofShape.mkApps (.const c ls') (bodyPre ++ bodyPending)) := by
        simpa only [ProofShape.mkApps_snoc, ProofShape.liftN_mkApps, ProofShape.liftN] using RPB
      obtain ⟨HTbody, WI⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
      have HTroot := RPB'.forget.spine_cut_source_typed
        (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs m)) HTbody
      refine ⟨A', body', x', xs', cf, ca, cs, cd, cb, m, ls', bodyPre, bodyPending,
        target, pb, tb, hcExact, hsplit, hcutExact, RF, RX, RS, RD, HL, HA, RPB', HR, HN, RTB,
        hminBody, hminContinuation, ?_, HTroot, WI, ?_, trivial⟩
      · apply pi_inert_continuation_minimum_no_identity_nonlambda
          (by simpa only [ProofShape.mkApps_append] using RPB') RTB
          (by simpa only [ProofShape.inst_eq_subst] using RS) hcutExact
          (by simpa only [ProofShape.inst_eq_subst] using hminContinuation) hout
      · apply pi_inert_continuation_minimum_no_constant_nonlambda heq hs HTroot WI
          (by simpa only [ProofShape.mkApps_append] using RPB') RTB
          (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS) hcutExact
          (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using hminContinuation) hout

/-- The carrier-exposure specialization, retaining the existing interface. -/
theorem globally_minimal_pi_inert_eta_body_spine_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps (ProofShape.mkApps (.const c ls) pre) args))
    (RN : ScopedTypeRecovery Guard Δ (ProofShape.mkApps (.const c ls) pre) (.forallE A B))
    (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (ProofShape.mkApps (.const c ls) pre) args))
    (HR : PiInertStage D n Δ (ProofShape.mkApps (.const c ls) pre)
      (.lam A (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))))
    (RT : ScopedComputeCount (PiInertStage D n) ct Δ
      (ProofShape.mkApps (.lam A (.app ((ProofShape.mkApps (.const c ls) pre).liftN 1) (etaArgument u))) args) out)
    (hcost : cp+1+ct ≤ cost)
    (hmin : ∀ later k, ScopedComputeCount (PiInertStage D later) k Δ original out → cost ≤ k)
    (HE : CarrierExposure out) :
    CountedEtaBodySpineCut D n Δ c ls pre A u args out ct :=
  globally_minimal_pi_inert_eta_body_spine_cut_nonlambda heq hs hguard HT RN SD RP HR RT hcost hmin HE.not_lambda_spine

end Lean4Lean.VEnv.Strengthening
