import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortedEtaOrigins

/-! # Exact fresh-argument reflection through the full level core

Primitive patterns cannot consume the classified fresh argument. Typed beta
reflection and exact lift reflection therefore retain the endpoint of the
opened body, even across arbitrary interleavings of universe and ordinary steps.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Full-core roots commute with insertion of a local binder block. -/
theorem erased_level_core_liftN (H : ErasedLevelCore D a b) :
    ErasedLevelCore D (a.liftN n k) (b.liftN n k) := by
  rcases H with H | H
  · exact .inl (erased_iota_primitive_liftN H)
  · cases H with
    | sort H hw => exact .inr (.sort H hw)
    | const H hw => exact .inr (.const H hw)

omit [Params] in
/-- Every visible match excludes a bare variable as its entire matched term. -/
theorem ProofShape.Matches.ne_bvar (H : Matches p e ls captures) : e ≠ .bvar i := by
  cases H <;> simp

/-- An applied registered pattern cannot consume the classified fresh eta
argument, whether it is retained as a variable or erased to a proof marker. -/
theorem erased_pattern_no_eta_argument (hp : Pat p r)
    (hm : Matches p (.app f (etaArgument u)) ls captures) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  cases sp with
  | defn => cases hm
  | iota recursor major ctor fields =>
    cases hm with
    | app hf ha =>
      unfold etaArgument at ha
      split at ha
      · exact ha.ne_proof rfl
      · exact ha.ne_bvar rfl

/-- Neither ordinary primitives nor universe roots cross the fresh eta
application boundary. This statement does not require source typing. -/
theorem erased_level_core_no_eta_application
    (H : ErasedLevelCore D (.app f (etaArgument u)) out) : False := by
  rcases H with ((H | H) | H) | H
  · cases H
  · cases H with
    | select hp _ hm => exact erased_pattern_no_eta_argument hp hm
    | apply hp _ hm => exact erased_pattern_no_eta_argument hp hm
  · cases H with
    | intro hp _ _ hm => exact erased_pattern_no_eta_argument hp hm
  · cases H

/-- The fresh eta argument is fixed by all level-core paths, in both sorts. -/
theorem ProofShape.Compute.level_core_eta_argument_fixed
    (R : Compute (ErasedLevelCore D) (etaArgument u) out) : out = etaArgument u := by
  apply NormalSyntax.fixed (Step := ErasedLevelCore D) ?_ R
  unfold etaArgument
  split <;> refine ⟨?_, trivial⟩ <;> intro out H
  all_goals
    rcases H with H | H
    · exact erased_iota_primitive_head H
    · cases H

/-- A typed opened eta body reflects into a full level-core function path with
its exact endpoint. If beta crosses the fresh boundary, the reflected function
is a lambda with that exact body. No confluence, normalization, native recovery,
concrete-pattern premise or compatibility assumption on unfolding is needed. -/
theorem proofErase_level_core_fresh_application_classified
    (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (R : Compute (ErasedLevelCore D)
      (.app ((proofErase Γ f).liftN 1) (etaArgument u)) body) :
    ∃ g, Compute (ErasedLevelCore D) (proofErase Γ f) g ∧ ClassifiedEtaBody u body g := by
  generalize E : ProofShape.app ((proofErase Γ f).liftN 1) (etaArgument u) = source at R
  induction R generalizing f with
  | base H => exact (erased_level_core_no_eta_application (E ▸ H)).elim
  | beta H =>
    obtain ⟨g, RG, HG⟩ := proofErase_beta_fresh_application_classified hΓ hA hf hn (E ▸ H)
    exact ⟨g, .beta RG, HG⟩
  | trans R1 R2 ih1 ih2 =>
    obtain ⟨g, RG, HG⟩ := ih1 hf hn E
    rcases HG with EE | ⟨C, rfl⟩
    · obtain ⟨g₀, HE, EG⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
        hΓ hf rfl rfl (RG.scoped (fun H => .base H))
      have hng := mt (isProof_congr hΓ HE).2 hn
      obtain ⟨g', RG', HG'⟩ := ih2 HE.hasType.2 hng (by rw [EG]; exact EE.symm)
      rw [EG] at RG'
      exact ⟨g', RG.trans RG', HG'⟩
    · exact ⟨_, RG.trans (.lam .refl R2), .inr ⟨C, rfl⟩⟩
  | app RF RX =>
    cases E
    obtain rfl := RX.level_core_eta_argument_fixed
    obtain ⟨g, RG, rfl⟩ := RF.level_core_lift_inv
    exact ⟨g, RG, .inl rfl⟩
  | proj | lam | forallE => cases E

end Lean4Lean.VEnv.Strengthening
