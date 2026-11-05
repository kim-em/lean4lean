import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorControlContinuation

/-! # A constructor-head wrapper escapes the saturated-payload observer

Constant expansion is an actual admitted primitive. Applied to the bare
constructor function, it produces a source beta-equivalent to the original
saturated constructor but not representable by ConstructorControlObservation.
Thus its PrefixPreservation premise is false in the displayed realizable case;
the observer must represent constructor functions, not only saturated payloads.
This is a representation counterexample, not a counterexample to strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A constant wrapper around a bare constant cannot carry any demand in
this observer: its control lambda would have to observe the bare constant. -/
theorem ConstructorControlObservation.Obs.not_wrapped_const
    (H : ConstructorControlObservation.Obs D Γ r info origin n Δ S
      (constantExpansion (.const c ls)) o) : False := by
  cases H with
  | payload HP => have E := HP.head; cases E
  | app HF _ =>
    cases HF with
    | lam _ _ HB => exact HB.not_const

/-- Supplying an argument does not fix the missing constructor-function
observation. The whole application has a lambda control head, so it cannot
use the saturated-constructor payload rule instead. -/
theorem ConstructorControlObservation.Obs.not_wrapped_const_app
    (H : ConstructorControlObservation.Obs D Γ r info origin n Δ S
      (.app (constantExpansion (.const c ls)) p) o) : False := by
  cases H with
  | payload HP => have E := HP.head; cases E
  | app HF _ => exact HF.not_wrapped_const

/-- An actual typed one-parameter constructor state observes its source,
but one allowed constructor-head expansion leaves the observer. The result
beta-contracts to the source, so failure is entirely in the representation. -/
theorem constructor_head_wrapper_observation_escape
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (H : ConstructorFamilyState D Γ r info origin (.app (.const info.ctorName []) p)) :
    ConstructorControlObservation.Obs D Γ r info origin 0 (proofEraseCtx Γ) (fun _ _ => False)
        (.app (.const info.ctorName []) p) .pi ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.app (.const info.ctorName []) p) (.app (constantExpansion (.const info.ctorName [])) p) ∧
      BetaRed (.app (constantExpansion (.const info.ctorName [])) p) (.app (.const info.ctorName []) p) ∧
      ¬ ConstructorControlObservation.Obs D Γ r info origin 0 (proofEraseCtx Γ) (fun _ _ => False)
        (.app (constantExpansion (.const info.ctorName [])) p) .pi := by
  refine ⟨.payload (H.type_payload heq hs hΓ hi hp hx), ?_, ?_, fun H => H.not_wrapped_const_app⟩
  · exact .app (.base ⟨0, .inr (.intro ProofShape.noConfusion)⟩) .refl
  · exact .app (constantExpansion_beta _) .refl

/-- The named prefix premise fails already at a typed fieldless constructor
with one parameter. It cannot be discharged for this observer merely by a
stronger induction; constructor-function observations must first be added. -/
theorem ConstructorControlObservation.PrefixPreservation.refuted_at_constructor_head
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (H : ConstructorFamilyState D Γ r info origin (.app (.const info.ctorName []) p)) :
    ¬ ConstructorControlObservation.PrefixPreservation D Γ r info origin := by
  intro HP
  have Hpayload := H.type_payload heq hs hΓ hi hp hx
  obtain ⟨e, T, _, _, ht, Ee, _⟩ := H
  have HR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.const info.ctorName []) (constantExpansion (.const info.ctorName [])) :=
    .base ⟨0, .inr (.intro ProofShape.noConfusion)⟩
  exact (HP (S := fun _ _ => False) hΓ (Ctx.LiftN.zero []) ht rfl Ee (fun _ _ h => h.elim) Hpayload HR .refl).not_wrapped_const_app

/-- Ordinary typing of a retained fieldless constructor supplies the failing
state, so the counterexample needs no assumed observation or history invariant.
The computed-header premise used by positive preservation is also unnecessary. -/
theorem constructor_prefix_preservation_refuted_of_typing
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0) (hz : info.numFields = 0)
    (ht : env.HasType univs Γ (.app (.const info.ctorName []) p) T)
    (hn : ¬ IsProof Γ (.app (.const info.ctorName []) p)) :
    ¬ ConstructorControlObservation.PrefixPreservation D Γ r info
      (.app (.const r []) (proofErase Γ p)) := by
  have EE : proofErase Γ (.app (.const info.ctorName []) p) =
      .app (.const info.ctorName []) (proofErase Γ p) := by
    simpa [VExpr.mkApps, ProofShape.mkApps] using
      proofErase_const_spine (c := info.ctorName) (ls := []) (args := [p]) hΓ ht hn
  apply ConstructorControlObservation.PrefixPreservation.refuted_at_constructor_head
    heq hs hΓ hi hp hx
  exact ⟨_, T, proofErase Γ p, [], ht, EE, rfl, hz.symm, .refl⟩

end Lean4Lean.VEnv.Strengthening
