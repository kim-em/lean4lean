import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldNativePrefix

/-! # Lower the retained empty-prefix function without losing its cost

When a fresh-field eta cannot be consumed, its retained function computation
starts at the closed constructor. Counted descent moves that entire function
path below the temporary telescope. The field is still pending, and the
remaining marked continuation has its own minimum at the exact endpoint.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

private theorem erased_context_suffix
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = controls ++ Δ) :
    ∃ telescope Ξ, Γ = telescope ++ Ξ ∧ telescope.length = controls.length ∧
      OnCtx Ξ (env.IsType univs) ∧ proofEraseCtx Ξ = Δ := by
  induction controls generalizing Γ with
  | nil => exact ⟨[], Γ, rfl, rfl, hΓ, EΓ⟩
  | cons C controls ih =>
    cases Γ with
    | nil => cases EΓ
    | cons c Γ =>
      obtain ⟨_, Etail⟩ := List.cons.inj EΓ
      obtain ⟨telescope, Ξ, rfl, hlen, hΞ, EΞ⟩ := ih hΓ.1 Etail
      exact ⟨c :: telescope, Ξ, rfl, by simp only [List.length_cons, hlen], hΞ, EΞ⟩

/-- Counted computation of an independently typed lower-scope source cannot
acquire any temporary binder. Its exact endpoint is a lift of a lower-scope
endpoint, with identical stage and primitive cost. The upper well-formed
context is supplied by its actual typed source, not an assumed embedding. -/
theorem pi_inert_telescope_component_count_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ f) (HU : TypedSource (controls ++ Δ) source)
    (R : ScopedComputeCount (PiInertStage D n) cost (controls ++ Δ)
      (f.liftN controls.length) endpoint) :
    ∃ short, TypedSource Δ short ∧ ScopedComputeCount (PiInertStage D n) cost Δ f short ∧
      endpoint = short.liftN controls.length := by
  obtain ⟨Γ, a, T, hΓ, EΓ, ha, Ea⟩ := HU
  obtain ⟨telescope, Ξ, rfl, hlen, hΞ, EΞ⟩ := erased_context_suffix hΓ EΓ
  obtain ⟨Ω, g, S, hΩ, EΩ, hg, Eg⟩ := HT
  have W := proofEraseCtx_defeq hΩ hΞ (EΩ.trans EΞ.symm)
  have hg' := hg.defeqDFC henv W
  have Eg' : proofErase Ξ g = f := (proofErase_defeqCtx hΩ W hg).symm.trans Eg
  have WI : Ctx.LiftN controls.length 0 Ξ (telescope ++ Ξ) := .zero telescope hlen
  obtain ⟨g', HE, RG, EG⟩ := proofErase_scoped_compute_count_descend
    (pi_inert_stage_rule_descent heq hs) hΞ hΓ WI hg' EΓ
    (by simpa only [Eg'] using R)
  exact ⟨proofErase Ξ g', ⟨Ξ, g', S, hΞ, EΞ, HE.hasType.2, rfl⟩,
    by simpa only [EΞ, Eg'] using RG, EG.symm⟩

/-- Fixing an actual complete prefix gives a marked minimum at its endpoint.
The prefix charge is retained in the caller's budget, while the new minimum
quantifies over every raw suffix at every stage. -/
theorem pi_inert_fresh_field_endpoint_minimum
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource (controls ++ A :: Δ) source)
    (RP : ScopedComputeCount (PiInertStage D n) cb (controls ++ A :: Δ) source endpoint)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x controls K endpoint ck frames)
    (hcost : cb+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      source tail → K tail k → cost ≤ j+k) :
    PiInertFreshFieldMinimum D Ω Δ family out A x controls endpoint ck frames := by
  refine ⟨K, n, 0, ck, endpoint, HT.pi_inert_compute heq hs RP.forget,
    ScopedComputeCount.beta BetaRed.refl, HK, by omega, ?_⟩
  intro later j tail k RJ RK
  have RR := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
    (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
  have HH := HM _ _ tail k RR RK
  omega

/-- The retained alternative of an actual charged empty-prefix eta cut has
a function computed in the supply base. Its exact function count includes
the eta root; its lifted endpoint is the retained lambda. The fresh field is
still the first pending argument, and the remaining marked minimum keeps the
same future supply. Function, argument and continuation charges fit together
in the original budget; none of the function path is substituted. -/
theorem pi_inert_fresh_field_empty_eta_retained_descent
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage)
      (controls ++ A :: Δ) (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (controls ++ A :: Δ) A' v)
    (HTlower : TypedSource Δ (.const info.ctorName []))
    (HT : TypedSource (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)))
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) original
      (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)))
    (HR : PiInertStage D n (controls ++ A :: Δ) (.const info.ctorName [])
      (.lam A' (.app (.const info.ctorName []) (etaArgument v))))
    (RT : ScopedComputeCount (PiInertStage D n) ct (controls ++ A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        (.bvar controls.length :: args)) endpoint)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x controls K endpoint ck frames)
    (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      original tail → K tail k → cost ≤ j+k) :
    ∃ short domain body rest cg ca,
      TypedSource Δ short ∧
      ScopedComputeCount (PiInertStage D n) cg Δ (.const info.ctorName []) short ∧
      short.liftN (controls.length+1) = .lam domain body ∧
      endpoint = ProofShape.mkApps (short.liftN (controls.length+1)) (.bvar controls.length :: rest) ∧
      ScopedArgumentsCount (PiInertStage D n) (controls ++ A :: Δ) ca
        (.bvar controls.length :: args) (.bvar controls.length :: rest) ∧
      cg+ca = 1+ct ∧ cp+cg+ca+ck ≤ cost ∧ ck < cost ∧
      PiInertFreshFieldMinimum D Ω Δ family out A x controls endpoint ck frames := by
  obtain ⟨k, RArg⟩ := pi_inert_pair_fresh_field_prefix_native heq hs hi hu hshape SD RN HT RN'
  rcases RT.pi_inert_lambda_spine_or_beta with
    ⟨domain, body, rest, cf, ca, hc, E, RF, RX⟩ |
    ⟨domain, body, y, ys, cf, ca, cs, hc, RF, RX, RS⟩
  · have EFirst : ∃ rest', rest = .bvar controls.length :: rest' := by
      cases RX with
      | cons RFirst RRest => exact ⟨_, by rw [RFirst.forget.pi_inert_bvar_fixed]⟩
    obtain ⟨rest', rfl⟩ := EFirst
    have RG := (ScopedComputeCount.base HR).trans RF
    have HU : TypedSource ((controls ++ [A]) ++ Δ)
        (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using HT
    have RG' : ScopedComputeCount (PiInertStage D n) (1+cf) ((controls ++ [A]) ++ Δ)
        ((ProofShape.const info.ctorName []).liftN (controls ++ [A]).length) (.lam domain body) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append, ProofShape.liftN] using RG
    obtain ⟨short, HTshort, RShort, EShort⟩ :=
      pi_inert_telescope_component_count_descend heq hs HTlower HU RG'
    have EL : short.liftN (controls.length+1) = .lam domain body := by
      simpa only [List.length_append, List.length_cons, List.length_nil] using EShort.symm
    have RTotal := ((ScopedComputeCount.base HR).mkApps
      (ScopedArgumentsCount.refl (args := .bvar controls.length :: args))).trans RT
    have HLocal : ∀ later j tail l, ScopedComputeCount (PiInertStage D later) j
        (controls ++ A :: Δ)
        (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)) tail →
        K tail l → 1+ct+ck ≤ j+l := by
      intro later j tail l RJ RK
      have RR := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
        (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
      have HH := HM _ _ tail l RR RK
      omega
    have HMin := pi_inert_fresh_field_endpoint_minimum heq hs HT RTotal HK
      (cost := 1+ct+ck) (by omega) HLocal
    have HExact := HLocal _ _ endpoint ck
      (by simpa only [E] using RG.mkApps RX) HK.forget.forget.holds
    refine ⟨short, domain, body, rest', 1+cf, ca, HTshort, RShort, EL, ?_, ?_,
      ?_, ?_, ?_, HMin⟩
    · simpa only [EL] using E
    · exact RX
    · omega
    · omega
    · omega
  · have EY : y = .bvar controls.length := by
      cases RX with
      | cons RFirst _ => exact RFirst.forget.pi_inert_bvar_fixed
    subst y
    obtain ⟨later, cb, hcb, RB⟩ := pi_inert_consumed_eta_native_argument_bypass
      heq hs (erased_static_structure_eta_expansion_stage_descent heq hs innerStage)
      HT RN' SD' RF RX RS RArg
    have RR := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
      (RB.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
    have HH := HM _ _ endpoint ck RR HK.forget.forget.holds
    omega

end Lean4Lean.VEnv.Strengthening
