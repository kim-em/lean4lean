import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureControlReturn

/-! # Neutral control demands for type variables

The marked-Pi control machinery with an empty payload predicate preserves
a neutral demand for a type variable. Its existing operational interpretation
then supplies exact beta readout through full structure/function eta.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- With an empty payload predicate, a marked-Pi observation is entirely
neutral and retains its free-variable demands. -/
theorem ProofShape.PiOriginObservation.Obs.neutral
    (H : PiOriginObservation.Obs (fun _ _ => False) n S e o) :
    VariableObservation S e o := by
  induction H with
  | var h => exact .var h
  | payload h => exact h.elim
  | app _ _ ihf ihx => exact .app ihf (fun key hk => ihx key hk)
  | lam _ ih => exact .lam ih

variable [Params] {D : PureObservation.Definitions}

/-- Full enriched computation from a variable assigned a universe returns to
that variable by beta. Proposition variables, arbitrary temporary frames,
changed annotations and every finite eta guard depth are included. -/
theorem static_structure_neutral_type_variable_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.bvar i) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) out) :
    BetaRed out (.bvar i) := by
  have E : proofErase Γ (.bvar i) = .bvar i := if_neg (not_isProof_of_sort hΓ ht)
  have HC : ControlTyping (proofEraseCtx Γ) (.bvar i) (.sort u) := ⟨Γ, _, hΓ, rfl, ht, E⟩
  let S : ControlObservation.Sets := fun j t o => j = i ∧ t = .sort u ∧ o = .pi
  have HS : S.Typed (proofEraseCtx Γ) := by
    intro j t o hj
    obtain ⟨rfl, rfl, rfl⟩ := hj
    exact HC
  have H : ControlObservation.Obs (fun _ _ => False) 0 (proofEraseCtx Γ) S
      (.bvar i) (.sort u) .pi := .var HC .payload ⟨rfl, rfl, rfl⟩
  have HP : PiOriginComponentClosure (ErasedStaticStructureEtaExpansionUnion D) Γ
      (fun _ _ => False) := by
    intro Γ' n X Y outX outY hΓ' W hP RX RY
    exact hP.elim
  have HO := proofErase_scoped_compute_controlObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_controlObservation heq hs) HP R hΓ (Ctx.LiftN.zero [])
    ht rfl E HS H
  have HN := HO.forget (T := fun j o => j = i ∧ o = .pi)
    (fun j t key hj => ⟨hj.1, hj.2.2⟩)
  exact HN.neutral.variable_exposure

end Lean4Lean.VEnv.Strengthening
