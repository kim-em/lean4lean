import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCarrierHistory

/-! # Dependent function and subsingleton carrier histories

Full-core computation changes a function's domain and codomain independently.
The retained typed-substitution history transports the recursive guard into the
computed domain context, so no unrestricted checker-context conversion is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
variable [Params] {D : Definitions}

/-- Structural subsingletons survive full-core computation, including universe
conversion, arbitrary computed parameters, and dependent function codomains. -/
theorem ProofShape.SubsingletonCarrier.level_core_compute
    (heq : env.HasCanonicalEq)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : SubsingletonCarrier A) (R : Compute (ErasedLevelCore D) A B) : SubsingletonCarrier B := by
  induction H generalizing B with
  | unit hi hx hf hp =>
    rename_i family info ls ps
    have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) family := by
      intro Δ ls args out H
      exact erased_level_recovered_stage_spine_levels heq (henv.projectionRigid hi)
        (hRigid (henv.projectionRigid hi)) 0 (Δ := Δ) H
    obtain ⟨ls', ps', rfl, _, Hps⟩ := (R.scoped (Δ := []) (fun H => .base H)).const_spine_levels @hroot
    exact .unit hi hx hf (Hps.length_eq.symm.trans hp)
  | forallE H ih =>
    obtain ⟨A', B', rfl, _, RB⟩ := R.pi_parts (fun H => erased_level_core_no_pi H)
    exact .forallE (ih RB)

/-- Every structural subsingleton constructs the full hereditary carrier
history. This includes parameterized empty structures and iterated functions
into them, with no chosen endpoint typings or native recovery premise. -/
theorem PiInertCarrierHistory.subsingleton
    (heq : env.HasCanonicalEq)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : SubsingletonCarrier C) : PiInertCarrierHistory D stage Δ C a b := by
  refine ⟨fun RC _ _ => .carrierSubsingleton (H.level_core_compute heq hRigid RC), ?_⟩
  intro Δ' τ _ C' a' b' RC _ _
  exact .carrierSubsingleton ((H.subst τ).level_core_compute heq hRigid RC)

/-- A function guard can follow independent paths of the carrier and both
functions. Typed substitution reinterprets its body history beneath the new
domain; the chosen fresh argument retains the domain's original sort. -/
theorem PiInertCarrierHistory.function_residual
    (hs : D.Sound env univs) (S : DomainSort Δ A u)
    (H : PiInertCarrierHistory D stage (A :: Δ) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u))) :
    PiInertCarrierResidual D stage Δ (.forallE A B) a b := by
  intro C p q RC RA RB
  obtain ⟨A', B', rfl, RD, RT⟩ := RC.pi_parts (fun R => erased_level_core_no_pi R)
  have H' := H.substitute (ContextSubstitution.core_binder hs RD)
  simp only [ProofShape.subst_id] at H'
  exact .carrierFunction (S.level_core hs RD)
    (H'.base RT (.app (RA.liftN (fun R => level_lift R)) .refl)
      (.app (RB.liftN (fun R => level_lift R)) .refl))

/-- Function extensionality preserves the complete carrier history at the
same stage. Future substitution may expose new redexes in every position. -/
theorem PiInertCarrierHistory.function
    (hs : D.Sound env univs) (S : DomainSort Δ A u)
    (H : PiInertCarrierHistory D stage (A :: Δ) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u))) :
    PiInertCarrierHistory D stage Δ (.forallE A B) a b := by
  refine ⟨H.function_residual hs S, ?_⟩
  intro Δ' τ W
  have H' := H.substitute W.cons
  simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst] at H'
  intro C p q RC RA RB
  exact PiInertCarrierHistory.function_residual hs (W.sort S) H' RC RA RB

/-- An explicit domain-comparison child changes the binder of a retained
body history. Domains are arbitrary actual types at one sort; neither a
terminal-domain restriction nor checker-context conversion completeness is
assumed. This constructs a function guard from its body, not by inverting an
arbitrary completed function-carrier certificate. -/
theorem PiInertCarrierHistory.function_domain_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (HD : PiInertEvidence D stage (.compare true) (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C))
    (H : PiInertCarrierHistory D stage (proofErase Γ A :: proofEraseCtx Γ) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u))) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (.forallE (proofErase Γ C) B) a b := by
  have HAC := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs stage) hΓ hA hC
    (.carrierChecked ((HD.base .refl .refl).mono (fun R => pi_inert_stage_embed R)))
  have W : ContextSubstitution (proofErase Γ A :: proofEraseCtx Γ)
      (proofErase Γ C :: proofEraseCtx Γ) ProofShape.Subst.id :=
    ContextSubstitution.of_defeqCtx hΓ (.succ .zero HAC)
  have H' := H.substitute W
  simp only [ProofShape.subst_id] at H'
  exact H'.function hs (DomainSort.of_typed hΓ hC)

end Lean4Lean.VEnv.Strengthening
