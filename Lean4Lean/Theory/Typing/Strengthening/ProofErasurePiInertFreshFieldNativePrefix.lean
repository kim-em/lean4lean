import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldProgress

/-! # Exact fresh-field recovery below arbitrary temporary binders

A field binder whose annotation was computed from a literal universe retains
an exact stage-zero universe certificate beneath every well-formed temporary
prefix. Later empty-constructor eta domains are reachable from that same
universe, so consuming this fresh field admits the counted native eta bypass.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : Definitions}

/-- A computed-universe field binder has its exact original universe at any
temporary depth. The actual well-formed context supplies each weakening; no
native typing of a future supplied argument is assumed. -/
theorem pi_inert_computed_sort_prefix_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (EΓ : proofEraseCtx Γ = controls ++ A :: Δ) (hv : v.WF univs)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.sort v) A) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (controls ++ A :: Δ) (.bvar controls.length) (.sort v) := by
  induction controls generalizing Γ with
  | nil =>
    cases Γ with
    | nil => cases EΓ
    | cons a Γ =>
      obtain ⟨EA, EΔ⟩ := List.cons.inj EΓ
      have RBack := static_structure_computed_sort_returns heq hs hΓ.1 hv
        (by simpa only [EA, EΔ] using RA)
      have RL := RBack.rename (erased_static_structure_eta_expansion_stage_rename heq hs 0)
        (ContextRenaming.of_liftN hΓ.1 hΓ Ctx.LiftN.one)
      have RL' : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0)
          (A :: Δ) (A.liftN 1) (.sort v) := by
        simpa only [subst_bvar_liftN, proofEraseCtx, EA, EΔ, ProofShape.liftN] using RL
      exact (ScopedTypeRecovery.bvar (i := 0)).convert RL'
  | cons C controls ih =>
    cases Γ with
    | nil => cases EΓ
    | cons c Γ =>
      obtain ⟨EC, EΔ⟩ := List.cons.inj EΓ
      have RN := ih hΓ.1 EΔ
      have RL := (show ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
        (proofEraseCtx Γ) (.bvar controls.length) (.sort v) from EΔ ▸ RN).rename
        (erased_static_structure_eta_expansion_stage_rename heq hs 0)
        (ContextRenaming.of_liftN hΓ.1 hΓ Ctx.LiftN.one)
      simpa only [subst_bvar_liftN, proofEraseCtx, EC, EΔ, List.cons_append,
        List.length_cons, ProofShape.liftN, liftVar, Nat.zero_le, ↓reduceIte,
        Nat.add_comm, ProofShape.subst, Nat.not_lt_zero, List.append_eq] using RL

/-- The distinguished fresh field recovers every later empty-constructor eta
domain, even beneath arbitrary temporary binders. The original domain history
comes from the original native constructor recovery; the later domain history
comes from its actual recovery in the larger context. -/
theorem pi_inert_pair_fresh_field_prefix_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (HT : TypedSource (controls ++ A :: Δ) source)
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage)
      (controls ++ A :: Δ) (.const info.ctorName []) (.forallE A' B')) :
    ∃ k, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k)
      (controls ++ A :: Δ) (.bvar controls.length) A' := by
  obtain ⟨Γ, a, hΓ, EΓ, ha, Ea⟩ := SD
  have RA := pi_inert_pair_constructor_domain_history heq hs hi hu hshape hΓ
    (by simpa only [EΓ] using RN)
  obtain ⟨Ξ, e, T, hΞ, EΞ, ht, Ee⟩ := HT
  have RB := pi_inert_pair_constructor_domain_history heq hs hi hu hshape hΞ
    (by simpa only [EΞ] using RN')
  have RF := pi_inert_computed_sort_prefix_native heq hs hΞ EΞ
    (v := .succ .zero) (by trivial) (by simpa only [EΓ] using RA)
  have RB' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (controls ++ A :: Δ) (.sort (.succ .zero)) A' := by
    simpa only [EΞ] using RB
  exact ((RF.mono (fun H => ⟨0, H⟩)).convert RB').finite_stage
      (Stages := ErasedStaticStructureEtaExpansionStage D)
      (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)

/-- At any temporary depth, an empty-constructor eta applied to the tracked
fresh field either remains a lambda spine applied to that same field or can
be bypassed at no more than its suffix cost. The consumed branch uses exact
native recovery derived above, preserving the entire counted body endpoint. -/
theorem pi_inert_pair_fresh_field_prefix_eta_bypass_or_retained
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero)) C)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (RN' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D innerStage) (controls ++ A :: Δ)
      (.const info.ctorName []) (.forallE A' B'))
    (SD' : DomainSort (controls ++ A :: Δ) A' v)
    (HT : TypedSource (controls ++ A :: Δ) (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)))
    (R : ScopedComputeCount (PiInertStage D n) ct (controls ++ A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        (.bvar controls.length :: args)) out) :
    (∃ domain body rest, out = ProofShape.mkApps (.lam domain body) (.bvar controls.length :: rest)) ∨
    (∃ later cost, cost ≤ ct ∧ ScopedComputeCount (PiInertStage D later) cost (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)) out) := by
  obtain ⟨k, RArg⟩ := pi_inert_pair_fresh_field_prefix_native heq hs hi hu hshape SD RN HT RN'
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨domain, body, rest, cf, ca, hc, E, RF, RX⟩ |
    ⟨domain, body, x, xs, cf, ca, cs, hc, RF, RX, RS⟩
  · cases RX with
    | cons RFirst RRest =>
      have EX := RFirst.forget.pi_inert_bvar_fixed
      exact .inl ⟨domain, body, _, by simpa only [EX] using E⟩
  · have EX : x = .bvar controls.length := by
      cases RX with
      | cons RX _ => exact RX.forget.pi_inert_bvar_fixed
    subst x
    obtain ⟨later, cost, hcost, RB⟩ := pi_inert_consumed_eta_native_argument_bypass
      heq hs (erased_static_structure_eta_expansion_stage_descent heq hs innerStage)
      HT RN' SD' RF RX RS RArg
    exact .inr ⟨later, cost, by omega, RB⟩

/-- A charged empty-prefix root in an actual global minimum cannot consume
the tracked fresh field, at any temporary depth. Its selected endpoint must
retain a lambda spine with that exact field as its first pending argument.
The actual prefix and arbitrary continuation are preserved in the bypass
contradiction. Further execution of the retained endpoint remains necessary. -/
theorem pi_inert_pair_fresh_field_prefix_eta_cut_retained
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
    (HT : TypedSource (controls ++ A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)))
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) original
      (ProofShape.mkApps (.const info.ctorName []) (.bvar controls.length :: args)))
    (RT : ScopedComputeCount (PiInertStage D n) ct (controls ++ A :: Δ)
      (ProofShape.mkApps (.lam A' (.app (.const info.ctorName []) (etaArgument v)))
        (.bvar controls.length :: args)) endpoint)
    (HK : K endpoint ck) (hcost : cp+1+ct+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      original tail → K tail k → cost ≤ j+k) :
    ∃ domain body rest,
      endpoint = ProofShape.mkApps (.lam domain body) (.bvar controls.length :: rest) := by
  rcases pi_inert_pair_fresh_field_prefix_eta_bypass_or_retained
    heq hs hi hu hshape SD RN RN' SD' HT RT with
      ⟨domain, body, rest, E⟩ | ⟨later, cb, hcb, RB⟩
  · exact ⟨domain, body, rest, E⟩
  · have RR := (RP.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
      (RB.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
    have HH := HM _ _ endpoint ck RR HK
    omega

end Lean4Lean.VEnv.Strengthening
