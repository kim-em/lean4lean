import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCountedSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorSortDomain

/-! # Bypass consumed nested eta at a fresh type field

A fresh variable created by eta on the empty pair constructor prefix has an
exact native certificate at every later empty-prefix eta domain. If that later
eta consumes this variable in its selected path, counted native instantiation
replays the entire body and removes the eta charge. Retained lambda endpoints
are kept as an explicit remaining case.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
variable [Params] {D : Definitions}

/-- Exact native recovery of a consumed eta argument replays the entire
counted body, including all nested native roots, with unchanged body count.
The original domain path is discarded and the outer eta primitive is absent.
This concerns an actual consuming beta, not an arbitrary retained endpoint. -/
theorem pi_inert_consumed_eta_native_argument_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ
      (.lam A (.app (f.liftN 1) (etaArgument u))) (.lam A' body))
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x :: xs))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body.inst x) xs) out)
    (RArg : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k) Δ x A) :
    ∃ later cost, cost ≤ cf+ca+cs ∧
      ScopedComputeCount (PiInertStage D later) cost Δ (ProofShape.mkApps f args) out := by
  have HTf : TypedSource Δ f := typed_spine_head HT
  obtain ⟨cd, cb, m, hfun, RD, RB⟩ := pi_inert_native_eta_count_body_readout
    heq hs hguard HTf (NativeEtaExpansion.intro RN SD) RF
  obtain ⟨HTbody, WI⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  have RI := pi_inert_compute_count_native_inst heq hs RB HTbody WI RArg
  have RIargs := RI.mkApps (ScopedArgumentsCount.refl (args := xs))
  have RT := (RIargs.mono (pi_inert_stage_mono (Nat.le_max_right n (m+k)))).trans
    (RS.mono (pi_inert_stage_mono (Nat.le_max_left n (m+k))))
  have RT' : ScopedComputeCount (PiInertStage D (max n (m+k))) (cb+cs) Δ
      (ProofShape.mkApps ((ProofShape.app (f.liftN 1) (etaArgument u)).inst x) xs) out := by
    simpa only [Nat.add_zero] using RT
  have RBYP := pi_inert_retained_eta_body_count_bypass heq hs hguard HT RN SD
    (ScopedComputeCount.beta (Step := PiInertStage D 0) (BetaRed.refl (e := f.liftN 1)))
    (RX.mono (pi_inert_stage_mono (Nat.le_max_left n (m+k)))) RT'
  exact ⟨_, _, by omega, RBYP⟩

/-- A nested empty-prefix eta applied to the original fresh type-field
variable either survives as a lambda spine, or has a bypass costing no more
than its suffix (excluding the eta root). Both native domain certificates
come from the actual pair constructor recoveries. The variable argument's
computation is fixed, so its exact image certificate remains applicable. -/
theorem pi_inert_pair_fresh_field_eta_bypass_or_retained
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage) (A :: Δ)
      (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (A :: Δ) A' v)
    (HT : TypedSource (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) (etaArgument u :: args)))
    (R : ScopedComputeCount (PiInertStage D n) ct (A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        (etaArgument u :: args)) out) :
    (∃ domain body rest, out = ProofShape.mkApps (.lam domain body) (etaArgument u :: rest)) ∨
    (∃ later cost, cost ≤ ct ∧ ScopedComputeCount (PiInertStage D later) cost (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) (etaArgument u :: args)) out) := by
  obtain ⟨k, RArg⟩ := pi_inert_pair_fresh_field_native heq hs hi hu hshape SD RN RN'
  have Earg := pi_inert_pair_constructor_eta_slot heq hs hi hu hshape SD RN
  rw [Earg] at HT R ⊢
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨domain, body, rest, cf, ca, hc, E, RF, RX⟩ |
    ⟨domain, body, x, xs, cf, ca, cs, hc, RF, RX, RS⟩
  · cases RX with
    | cons RFirst RRest =>
      have EX := RFirst.forget.pi_inert_bvar_fixed
      exact .inl ⟨domain, body, _, by simpa only [EX] using E⟩
  · have EX : x = .bvar 0 := by
      cases RX with
      | cons RX _ => exact RX.forget.pi_inert_bvar_fixed
    subst x
    obtain ⟨later, cost, hcost, RB⟩ := pi_inert_consumed_eta_native_argument_bypass
      heq hs (erased_static_structure_eta_expansion_stage_descent heq hs innerStage)
      HT RN' SD' RF RX RS RArg
    exact .inr ⟨later, cost, by omega, RB⟩

/-- A globally minimum nested empty-prefix eta on the original fresh field
must survive as a lambda spine still applied to that same fresh field at the
selected endpoint. Otherwise native
instantiation bypasses all its body computation and saves the eta charge.
This isolates the retained endpoint as the remaining case without assuming
any native certificate for the original outer type-field argument. -/
theorem pi_inert_pair_fresh_field_eta_minimum_retained
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage) (A :: Δ)
      (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (A :: Δ) A' v)
    (HT : TypedSource (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) (etaArgument u :: args)))
    (R : ScopedComputeCount (PiInertStage D n) ct (A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        (etaArgument u :: args)) endpoint)
    (HK : K endpoint ck)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) (etaArgument u :: args)) tail →
      K tail k → 1+ct+ck ≤ j+k) :
    ∃ domain body rest, endpoint = ProofShape.mkApps (.lam domain body) (etaArgument u :: rest) := by
  rcases pi_inert_pair_fresh_field_eta_bypass_or_retained
    heq hs hi hu hshape SD RN RN' SD' HT R with ⟨domain, body, rest, E⟩ |
      ⟨later, cost, hcost, RB⟩
  · exact ⟨domain, body, rest, E⟩
  · have HH := HM later cost endpoint ck RB HK
    omega

/-- At a non-lambda selected endpoint, nested empty-prefix eta on the fresh
field is strictly unnecessary in any minimum that charged its root. The same
endpoint and continuation remain available, so no observer normalization or
assumed field readout is used for this contradiction. -/
theorem pi_inert_pair_fresh_field_eta_not_minimal
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage) (A :: Δ)
      (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (A :: Δ) A' v)
    (HT : TypedSource (A :: Δ) (ProofShape.mkApps (.const info.ctorName []) (etaArgument u :: args)))
    (R : ScopedComputeCount (PiInertStage D n) ct (A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        (etaArgument u :: args)) endpoint)
    (HNon : ∀ domain body rest, endpoint ≠ ProofShape.mkApps (.lam domain body) rest)
    (HK : K endpoint ck)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) (etaArgument u :: args)) tail →
      K tail k → 1+ct+ck ≤ j+k) : False := by
  obtain ⟨domain, body, rest, E⟩ := pi_inert_pair_fresh_field_eta_minimum_retained
    heq hs hi hu hshape SD RN RN' SD' HT R HK HM
  exact HNon _ _ _ E

end Lean4Lean.VEnv.Strengthening
