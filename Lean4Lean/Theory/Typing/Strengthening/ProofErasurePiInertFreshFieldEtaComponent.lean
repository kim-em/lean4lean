import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldEtaBypass

/-! # Nested fresh-field eta restores the outer component form

When the nested lambda survives at the fresh singleton argument, its entire
function computation is a component path from the original constructor.
The enclosing eta can therefore be bypassed when consumed. If the inner
lambda is consumed instead, its native fresh-variable bypass saves that
inner eta charge. Neither branch requires native recovery of the eventual
outer argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private lambda_tail_replace
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLaterEtaBodyCut
variable [Params] {D : Definitions}

private theorem const_eta_root
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k) Δ
      (.const c ls) (.forallE A B)) (SD : DomainSort Δ A u) :
    PiInertStage D (k+1) Δ (.const c ls)
      (.lam A (.app (.const c ls) (etaArgument u))) :=
  ⟨.inr (.inr (.inr (.inr (.inl (.intro RN SD))))), .inl trivial⟩

/-- For the singleton fresh argument, a retained nested eta yields an actual
function-component path, including the inner eta charge. Otherwise the whole
body has a replay saving that charge. Both alternatives keep the exact body
endpoint; arbitrary further pending arguments are deliberately absent. -/
theorem pi_inert_pair_fresh_eta_component_or_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage) (A :: Δ)
      (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (A :: Δ) A' v)
    (HT : TypedSource (A :: Δ) (.app (.const info.ctorName []) (etaArgument u)))
    (R : ScopedComputeCount (PiInertStage D n) ct (A :: Δ)
      (.app (.lam A' (.app (.const info.ctorName []) (etaArgument v))) (etaArgument u)) body) :
    (∃ later cg g, cg ≤ 1+ct ∧ body = .app g (etaArgument u) ∧
      ScopedComputeCount (PiInertStage D later) cg (A :: Δ) (.const info.ctorName []) g) ∨
    (∃ later cb, cb ≤ ct ∧ ScopedComputeCount (PiInertStage D later) cb (A :: Δ)
      (.app (.const info.ctorName []) (etaArgument u)) body) := by
  obtain ⟨k, RArg⟩ := pi_inert_pair_fresh_field_native heq hs hi hu hshape SD RN RN'
  have Earg := pi_inert_pair_constructor_eta_slot heq hs hi hu hshape SD RN
  rw [Earg] at HT R ⊢
  have Rsp : ScopedComputeCount (PiInertStage D n) ct (A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v))) [.bvar 0]) body := R
  rcases Rsp.pi_inert_lambda_spine_or_beta with
    ⟨domain, innerBody, rest, cf, ca, hc, E, RF, RX⟩ |
    ⟨domain, innerBody, x, xs, cf, ca, cs, hc, RF, RX, RS⟩
  · cases RX with
    | cons RFirst RRest =>
      cases RRest
      have EX := RFirst.forget.pi_inert_bvar_fixed
      have HR := const_eta_root RN' SD'
      have RG := (ScopedComputeCount.base
        (pi_inert_stage_mono (Nat.le_max_left (innerStage+1) n) HR)).trans
        (RF.mono (pi_inert_stage_mono (Nat.le_max_right (innerStage+1) n)))
      exact .inl ⟨_, _, _, by omega, by simpa only [ProofShape.mkApps, EX] using E, RG⟩
  · have EX : x = .bvar 0 := by
      cases RX with
      | cons RX _ => exact RX.forget.pi_inert_bvar_fixed
    subst x
    obtain ⟨later, cb, hcb, RB⟩ := pi_inert_consumed_eta_native_argument_bypass
      heq hs (erased_static_structure_eta_expansion_stage_descent heq hs innerStage)
      (args := [.bvar 0]) HT RN' SD' RF RX RS RArg
    exact .inr ⟨later, cb, by omega, RB⟩

/-- If the outer eta is consumed after this nested singleton computation,
one of the two eta charges is unnecessary. A retained inner lambda is
replayed as the outer function component; a consumed inner lambda is bypassed
inside the original outer binder. The outer argument needs only its actual
typing, even if it lacks native recovery at the outer domain. -/
theorem pi_inert_pair_nested_eta_outer_consumption_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage) (A :: Δ)
      (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (A :: Δ) A' v)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) args))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A domain)
    (R : ScopedComputeCount (PiInertStage D m) ct (A :: Δ)
      (.app (.lam A' (.app (.const info.ctorName []) (etaArgument v))) (etaArgument u)) body)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x :: xs))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body.inst x) xs) out) :
    ∃ later cost, cost ≤ 1+cd+ct+ca+cs ∧
      ScopedComputeCount (PiInertStage D later) cost Δ
        (ProofShape.mkApps (.const info.ctorName []) args) out := by
  have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D outerStage) :=
    erased_static_structure_eta_expansion_stage_descent heq hs outerStage
  obtain ⟨HTbody, _⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  rcases pi_inert_pair_fresh_eta_component_or_bypass heq hs hi hu hshape SD RN RN' SD' HTbody R with
    ⟨later, cg, g, hcg, Ebody, RG⟩ | ⟨later, cb, hcb, RB⟩
  · have RR := pi_inert_retained_eta_body_count_bypass heq hs hguard HT RN SD RG RX
      (Ebody ▸ RS)
    exact ⟨_, _, by omega, RR⟩
  · have RT := lambda_tail_replace RD RB RX RS
    have HR := const_eta_root RN SD
    have RR := (ScopedComputeCount.base (pi_inert_stage_mono
      (Nat.le_max_left (outerStage+1) (max later n)) HR)).mkApps
        (ScopedArgumentsCount.refl (args := args))
    have RS' := RT.mono (pi_inert_stage_mono (Nat.le_max_right (outerStage+1) (max later n)))
    exact ⟨_, _, by omega, RR.trans RS'⟩

/-- Charging both empty-prefix eta roots cannot be globally minimal when the
outer lambda is consumed after the singleton nested computation. The prefix,
exact output and arbitrary remaining continuation are preserved. This rules
out both nested-lambda branches, not just immediate inner consumption. -/
theorem pi_inert_pair_nested_eta_outer_consumption_not_minimal
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
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) args))
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (.const info.ctorName []) args))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A domain)
    (R : ScopedComputeCount (PiInertStage D m) ct (A :: Δ)
      (.app (.lam A' (.app (.const info.ctorName []) (etaArgument v))) (etaArgument u)) body)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x :: xs))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body.inst x) xs) out)
    (HK : K out ck) (hcost : cp+2+cd+ct+ca+cs+ck ≤ cost)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → cost ≤ j+k) : False := by
  obtain ⟨later, cb, hcb, RB⟩ := pi_inert_pair_nested_eta_outer_consumption_bypass
    heq hs hi hu hshape SD RN RN' SD' HT RD R RX RS
  have RR := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
    (RB.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
  have HH := HM _ _ out ck RR HK
  omega

/-- At a minimum that charges the inner eta, its singleton endpoint is an
outer component form with a counted short-function path in the lower scope.
The computed outer annotation shares an actual typed eta origin with that
short function. This witness survives later ordinary endpoint substitution;
it does not assert that arbitrary later computations remain component-only. -/
theorem pi_inert_pair_fresh_eta_minimum_lower_origin
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
    (HT : TypedSource Δ (.const info.ctorName []))
    (HTbody : TypedSource (A :: Δ) (.app (.const info.ctorName []) (etaArgument u)))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A domain)
    (R : ScopedComputeCount (PiInertStage D m) ct (A :: Δ)
      (.app (.lam A' (.app (.const info.ctorName []) (etaArgument v))) (etaArgument u)) body)
    (HK : K body ck)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (A :: Δ)
      (.app (.const info.ctorName []) (etaArgument u)) tail → K tail k → 1+ct+ck ≤ j+k) :
    ∃ later cg short, cg ≤ 1+ct ∧
      ScopedComputeCount (PiInertStage D later) cg Δ (.const info.ctorName []) short ∧
      body = .app (short.liftN 1) (etaArgument u) ∧ TypedEtaOrigin Δ domain short u := by
  rcases pi_inert_pair_fresh_eta_component_or_bypass heq hs hi hu hshape SD RN RN' SD' HTbody R with
    ⟨later, cg, g, hcg, Ebody, RG⟩ | ⟨later, cb, hcb, RB⟩
  · obtain ⟨short, RF, EG, HO⟩ := pi_inert_retained_eta_origin heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs outerStage) HT RN SD RD RG
    exact ⟨later, cg, short, hcg, RF, by simpa only [EG] using Ebody, HO⟩
  · have HH := HM later cb body ck RB HK
    omega

end Lean4Lean.VEnv.Strengthening
