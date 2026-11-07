import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertComputedPairObservation

/-! # Move a counted lower function history into an actual application suffix

Exact renaming replays the observer-scope history below a well-formed target
prefix. Competitors begin at the original constructor in that target, and
are compared by fixing the earlier argument path and executing the actual
application. Thus the restored source has a genuine all-raw minimum.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erased_context_suffix
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldRetainedDescent
open private subst_bvar_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : Definitions}

/-- Exact interpreted renaming preserves every outer primitive count, including
under changing lambda and Pi annotations. This uses primitive renaming only;
it does not transport guards by arbitrary expression substitution. -/
theorem ProofShape.ScopedComputeCount.rename
    (hstep : ∀ {Δ Θ a b τ}, Step Δ a b → ContextRenaming Δ Θ τ →
      Target Θ (a.subst τ) (b.subst τ))
    (H : ScopedComputeCount Step cost Δ a b) (W : ContextRenaming Δ Θ τ) :
    ScopedComputeCount Target cost Θ (a.subst τ) (b.subst τ) := by
  induction H generalizing Θ τ with
  | base H => exact .base (hstep H W)
  | beta H => exact .beta H.subst
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ W) (ih₂ W)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ W) (ih₂ W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ W) (ih₂ W.cons)
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ W) (ih₂ W.cons)

/-- The actual upper typed source supplies an exact interpreted weakening
from its literal erased context suffix. No additional context realization
or native argument certificate is assumed. -/
theorem TypedSource.telescope_renaming
    (HU : TypedSource (controls ++ Δ) source) :
    ContextRenaming Δ (controls ++ Δ) (fun i => .bvar (liftVar controls.length i 0)) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HU
  obtain ⟨telescope, Ξ, rfl, hlen, hΞ, EΞ⟩ := erased_context_suffix hΓ EΓ
  have W : Ctx.LiftN controls.length 0 Ξ (telescope ++ Ξ) := .zero telescope hlen
  simpa only [EΞ, EΓ] using ContextRenaming.of_liftN hΞ hΓ W

/-- Rebuild an observer-scope computation under any actual well-formed target
prefix, preserving its exact stage and primitive count. Only variable
weakening is used, even when that target was reached by a consuming frame. -/
theorem pi_inert_lift_count_to_typed_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HU : TypedSource (controls ++ Δ) source)
    (R : ScopedComputeCount (PiInertStage D n) cost Δ f short) :
    ScopedComputeCount (PiInertStage D n) cost (controls ++ Δ)
      (f.liftN controls.length) (short.liftN controls.length) := by
  have HR := R.rename (pi_inert_stage_rename heq hs n) (TypedSource.telescope_renaming HU)
  simpa only [subst_bvar_liftN] using HR

/-- Move the reserved constructor-function history past an actual application
above the distinguished field binder. The resulting marked minimum starts at
the constructor, rather than at its computed function. The same future x and
all tail frames remain, while the application itself is no longer present.
Minimality is replayed from the original prefix and argument path; it is not
inferred by prepending a path to a different minimum. -/
theorem pi_inert_fresh_field_commute_head_application
    {K : ProofShape → Nat → Prop}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTlower : TypedSource Δ (.const ctor levels))
    (RF : ScopedComputeCount (PiInertStage D functionStage) cg Δ (.const ctor levels) short)
    (RP : ScopedComputeCount (PiInertStage D n) cp (controls ++ A :: Δ) source
      (ProofShape.mkApps (.const ctor levels) args))
    (RX : ScopedArgumentsCount (PiInertStage D n) (controls ++ A :: Δ) ca args fields)
    (W : PiInertEndpointMap (controls ++ A :: Δ) (nextControls ++ A :: Δ) τ)
    (HNext : TypedSource (nextControls ++ A :: Δ) (ProofShape.mkApps
      ((ProofShape.mkApps (short.liftN (controls.length+1)) fields).subst τ) pending))
    (RNext : ScopedComputeCount (PiInertStage D suffixStage) cs (nextControls ++ A :: Δ)
      (ProofShape.mkApps ((ProofShape.mkApps (short.liftN (controls.length+1)) fields).subst τ) pending) endpoint)
    (HK : PiInertFreshFieldRun D Ω Δ family out A x nextControls K endpoint ck frames)
    (hcost : cp+ca+cg+cs+ck ≤ cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (controls ++ A :: Δ)
      source tail → PiInertApplicationContinuation D (nextControls ++ A :: Δ) τ pending K tail k →
      cost ≤ j+k) :
    PiInertFreshFieldMinimum D Ω Δ family out A x nextControls
      (ProofShape.mkApps (.const ctor levels) (fields.map (·.subst τ) ++ pending)) (cg+cs+ck) frames := by
  have EH := W.pending_head_transport (f := short) 0
  simp only [Nat.zero_add, ProofShape.Subst.liftN] at EH
  have EImage : ProofShape.mkApps
      ((ProofShape.mkApps (short.liftN (controls.length+1)) fields).subst τ) pending =
      ProofShape.mkApps (short.liftN (nextControls.length+1)) (fields.map (·.subst τ) ++ pending) := by
    rw [ProofShape.subst_mkApps, EH, ProofShape.mkApps_append]
  have HU : TypedSource ((nextControls ++ [A]) ++ Δ) (ProofShape.mkApps
      (short.liftN (nextControls.length+1)) (fields.map (·.subst τ) ++ pending)) := by
    simpa only [EImage, List.append_assoc, List.cons_append, List.nil_append] using HNext
  have RL : ScopedComputeCount (PiInertStage D functionStage) cg (nextControls ++ A :: Δ)
      (.const ctor levels) (short.liftN (nextControls.length+1)) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append,
      List.length_append, List.length_cons, List.length_nil, ProofShape.liftN] using
      pi_inert_lift_count_to_typed_context heq hs HU RF
  have HTctor : TypedSource (nextControls ++ A :: Δ) (.const ctor levels) := by
    have HH := HTlower.subst (TypedSource.telescope_renaming HU).interpretation
    simpa only [List.append_assoc, List.cons_append, List.nil_append, ProofShape.subst] using HH
  have HTsource := TypedSource.pi_inert_head_preimage heq hs HTctor (by intro E; cases E) RL.forget
    (by simpa only [EImage] using HNext)
  have RHead := RL.mkApps (ScopedArgumentsCount.refl (args := fields.map (·.subst τ) ++ pending))
  have RBody := (RHead.mono (pi_inert_stage_mono (Nat.le_max_left functionStage suffixStage))).trans
    ((EImage ▸ RNext).mono (pi_inert_stage_mono (Nat.le_max_right functionStage suffixStage)))
  refine ⟨K, max functionStage suffixStage, cg+cs, ck, endpoint, HTsource,
    by simpa only [Nat.add_zero] using RBody, HK, rfl, ?_⟩
  intro later j tail k RJ RK
  have RArgs := (ScopedComputeCount.beta (Step := PiInertStage D n)
    (BetaRed.refl (e := .const ctor levels))).mkApps RX
  have RPre := RP.trans RArgs
  have HH := HM n _ (ProofShape.mkApps (.const ctor levels) fields) (j+k) RPre
    ⟨later, j, tail, k, rfl, ?_, RK⟩
  · omega
  · simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append] using RJ

end Lean4Lean.VEnv.Strengthening
