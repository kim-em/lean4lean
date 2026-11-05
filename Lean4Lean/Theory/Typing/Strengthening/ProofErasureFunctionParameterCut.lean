import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidFunctionSelectedReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionHeadExpansion

/-! # Dependent native application with a retained function parameter

Keep the constructor's dependent codomain computation in the original function
parameter context. Ordinary observed beta substitution supplies the current
argument; no exact native certificate for that argument or directed substitution
of its native derivation is required. The whole constructor term's arbitrary
computation is not covered by this application-cut result.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
open _root_.Lean4Lean Params ProofShape
open AtomicControl (Atom)
variable [Params] [Atom]

/-- The ordinary family assignment builds a lambda demanding its fresh function
parameter. This is a typed frame, not a claim of native eta at that annotation. -/
theorem family_lambda_observation
    (EA : Atom.type = .const s [])
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (hΓ : OnCtx Γ (env.IsType univs)) :
    Obs c r v (proofEraseCtx Γ) V
      (.lam (.forallE (.const s []) (.const s [])) (.app (.const r []) (.bvar 0)))
      (.arrow (.arrow .atom .atom) (.sort v)) (.app [.app [] .pi] .pi) := by
  let Q : VExpr := .forallE (.const s []) (.const s [])
  have hQ : env.HasType univs Γ Q (.sort (.imax (.succ u) (.succ u))) :=
    .forallE (hS.weak0 henv.ordered) (hS.weak0 henv.ordered)
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have EQ := unit_arrow_erasure hS hΓ
  have EΓQ : proofEraseCtx (Q :: Γ) = .forallE (.const s []) (.const s []) :: proofEraseCtx Γ := by
    simp only [proofEraseCtx, Q, EQ]
  have hx : env.HasType univs (Q :: Γ) (.bvar 0)
      (AtomicControl.ControlType.arrow .atom .atom).expr := by
    simpa only [AtomicControl.ControlType.expr, EA, Q, VExpr.lift, VExpr.liftN] using (HasType.bvar (Γ := Q :: Γ) Lookup.zero)
  have hf : env.HasType univs (Q :: Γ) (.const r [])
      (AtomicControl.ControlType.arrow (.arrow .atom .atom) (.sort v)).expr := by
    simpa only [AtomicControl.ControlType.expr, EA] using hF.weak0 (Γ := Q :: Γ) henv.ordered
  have hb : env.HasType univs (Q :: Γ) (.app (.const r []) (.bvar 0)) (.sort v) := hf.app hx
  have EX : proofErase (Q :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (AtomicControl.ControlType.not_isProof hΓQ hx)
  have EF : proofErase (Q :: Γ) (.const r []) = .const r [] :=
    if_neg (AtomicControl.ControlType.not_isProof hΓQ hf)
  have EB : proofErase (Q :: Γ) (.app (.const r []) (.bvar 0)) = .app (.const r []) (.bvar 0) := by
    rw [show proofErase _ (.app _ _) = .app _ _ from if_neg (not_isProof_of_sort hΓQ hb), EF, EX]
  have hl : env.HasType univs Γ (.lam Q (.app (.const r []) (.bvar 0)))
      (AtomicControl.ControlType.arrow (.arrow .atom .atom) (.sort v)).expr := by
    simpa only [AtomicControl.ControlType.expr, EA, Q] using HasType.lam hQ hb
  have EL : proofErase Γ (.lam Q (.app (.const r []) (.bvar 0))) =
      .lam (.forallE (.const s []) (.const s [])) (.app (.const r []) (.bvar 0)) := by
    rw [show proofErase Γ (.lam _ _) = .lam _ _ from
      if_neg (AtomicControl.ControlType.not_isProof hΓ hl), EB]
    exact congrArg (fun A => ProofShape.lam A _) EQ
  refine .lam ⟨Γ, _, hΓ, rfl, hl, EL⟩ ?_ ?_
  · intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .fn (by simp) .atom
  · refine .app ⟨_, _, hΓQ, EΓQ, hb, EB⟩ (.rigid ⟨_, _, hΓQ, EΓQ, hf, EF⟩) ?_
    intro key hk
    obtain rfl := List.mem_singleton.1 hk
    exact .var ⟨_, _, hΓQ, EΓQ, hx, EX⟩ (.fn (by simp) .atom) ⟨rfl, by simp⟩

/-- Dependent body computation, independent argument computation, ordinary beta
substitution, and all later type computation preserve the family observation.
The argument supplies only its finite observation, never native recovery. -/
theorem pending_function_codomain_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hz : info.numFields = 0)
    (EA : Atom.type = .const s [])
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (hΓ : OnCtx Γ (env.IsType univs)) (HV : V.Typed (proofEraseCtx Γ))
    (HP : Obs info.ctorName r v (proofEraseCtx Γ) V p (.arrow .atom .atom) (.app [] .pi))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (.forallE (.const s []) (.const s []) :: proofEraseCtx Γ) (.app (.const r []) (.bvar 0)) Y)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) p a)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (Y.inst a) out) :
    Obs info.ctorName r v (proofEraseCtx Γ) V out (.sort v) .pi := by
  have HL := family_lambda_observation (c := info.ctorName) (V := V) EA hS hF hΓ
  have H : Obs info.ctorName r v (proofEraseCtx Γ) V
      (.app (.lam (.forallE (.const s []) (.const s [])) (.app (.const r []) (.bvar 0))) p) (.sort v) .pi :=
    .app (HL.typing.apply HP.typing) HL (by
      intro key hk; obtain rfl := List.mem_singleton.1 hk; exact HP)
  exact H.static_structure_union heq hs hi hz EA (henv.projectionCtorRigid hi) hD hr hDr
    ((ScopedCompute.app (.lam .refl RB) RX).trans ((ScopedCompute.beta .beta).trans RC)) HV

/-- The computed Pi's codomain history stays in its ORIGINAL parameter context.
Consequently a demanded function argument can be supplied after arbitrary
whole-header computation, including changed domains and control wrappers. -/
theorem pending_function_pi_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hz : info.numFields = 0)
    (EA : Atom.type = .const s [])
    (hD : ∀ ls rhs, ¬ D.unfolds info.ctorName ls rhs)
    (hS : env.HasType univs [] (.const s []) (.sort (.succ u)))
    (hr : env.Rigid r) (hDr : ∀ ls rhs, ¬ D.unfolds r ls rhs)
    (hF : env.HasType univs [] (.const r [])
      (.forallE (.forallE (.const s []) (.const s [])) (.sort v)))
    (hΓ : OnCtx Γ (env.IsType univs)) (HV : V.Typed (proofEraseCtx Γ))
    (HP : Obs info.ctorName r v (proofEraseCtx Γ) V p (.arrow .atom .atom) (.app [] .pi))
    (RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE (.forallE (.const s []) (.const s []))
        (.app (.const r []) (.bvar 0)))) (.forallE X Y))
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) p a)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (Y.inst a) out) :
    Obs info.ctorName r v (proofEraseCtx Γ) V out (.sort v) .pi := by
  let Q : VExpr := .forallE (.const s []) (.const s [])
  have hQ : env.HasType univs Γ Q (.sort (.imax (.succ u) (.succ u))) :=
    .forallE (hS.weak0 henv.ordered) (hS.weak0 henv.ordered)
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hf : env.HasType univs (Q :: Γ) (.const r []) (.forallE Q (.sort v)) := hF.weak0 henv.ordered
  have hx : env.HasType univs (Q :: Γ) (.bvar 0) Q := .bvar .zero
  have hb : env.HasType univs (Q :: Γ) (.app (.const r []) (.bvar 0)) (.sort v) := hf.app hx
  have EP : proofErase Γ (.forallE Q (.app (.const r []) (.bvar 0))) =
      .forallE (proofErase Γ Q) (proofErase (Q :: Γ) (.app (.const r []) (.bvar 0))) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hQ hb))
  rw [EP] at RP
  obtain ⟨_, _, _, _, _, _, _, RB⟩ := proofErase_static_structure_union_pi_components heq hs hΓ hQ hb RP
  have EX : proofErase (Q :: Γ) (.bvar 0) = .bvar 0 := by
    apply if_neg
    apply AtomicControl.ControlType.not_isProof (t := .arrow .atom .atom) hΓQ
    simpa only [AtomicControl.ControlType.expr, EA] using hx
  have EB : proofErase (Q :: Γ) (.app (.const r []) (.bvar 0)) = .app (.const r []) (.bvar 0) := by
    rw [show proofErase _ (.app _ _) = .app _ _ from if_neg (not_isProof_of_sort hΓQ hb),
      show proofErase (Q :: Γ) (.const r []) = .const r [] from if_neg (not_isProof_function_to_sort hΓQ hf), EX]
  have EΓQ : proofEraseCtx (Q :: Γ) = .forallE (.const s []) (.const s []) :: proofEraseCtx Γ := by
    simp only [proofEraseCtx, Q, unit_arrow_erasure hS hΓ]
  rw [EB, EΓQ] at RB
  exact pending_function_codomain_observation heq hs hi hz EA hD hS hr hDr hF hΓ HV HP RB RX RC

end Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
