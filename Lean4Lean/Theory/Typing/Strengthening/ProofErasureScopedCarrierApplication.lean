import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierPairedBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecoveryDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierApplication

/-! # Contextual recovery licenses carrier-aware application checking

Contextual recovery permits explicit-carrier type computations. Its Pi supplies the
argument carrier. Only one function needs recovery. The root rule descends,
including below arbitrary block insertion. General substitution is not claimed:
after substitution the domain and its argument guard must be re-synthesized
together, rather than preserving an arbitrary selected type exactly.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params]

namespace ProofShape
/-- A recovered function domain supplies the argument carrier. The codomain is
existential bookkeeping; the root rule does not prescribe an output type. -/
inductive ScopedRecoveredCarrierApplication
    (Recovery : List ProofShape → ProofShape → ProofShape → Prop)
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) : ProofShape → ProofShape → Prop where
  | app : ScopedTypeRecovery Recovery Δ f (.forallE A B) →
      ScopedCompare Step Δ false f g → StructureCarrierGuard Step Δ A x y →
      ScopedRecoveredCarrierApplication Recovery Step Δ (.app f x) (.app g y)


/-- Existing recovered application roots embed under contextual simulation of
their recovery computations; function comparison and argument guards are kept. -/
theorem RecoveredCarrierApplication.scoped
    (hrec : ∀ {Δ a b}, Recovery a b → ScopedCompute Recovery' Δ a b)
    (H : RecoveredCarrierApplication Recovery Step Δ a b) :
    ScopedRecoveredCarrierApplication Recovery' Step Δ a b := by
  cases H with
  | app R HF HX => exact .app (R.scoped hrec) HF HX

end ProofShape

/-- Application reflection uses the recovered lower domain, not the upper
typing of an argument or an inverse typing-weakening principle. Independent
endpoint types suffice because the inferred function comparison aligns them. -/
theorem proofErase_scoped_recovered_carrier_application_descend
    (hrec : ErasedScopedPrimitiveDescent Recovery) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (H : ProofShape.ScopedRecoveredCarrierApplication Recovery Step (proofEraseCtx Γ')
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    env.IsDefEqU univs Γ a b := by
  generalize Ea : (proofErase Γ a).liftN n k = sa at H
  generalize Eb : (proofErase Γ b).liftN n k = sb at H
  cases H with
  | app R HF HX =>
    obtain ⟨_, _, Eaa, Eaf, Eax⟩ := ProofShape.liftN_app_inv Ea
    obtain ⟨_, _, Ebb, Ebg, Eby⟩ := ProofShape.liftN_app_inv Eb
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Eaa
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Ebb
    rw [← Ef] at Eaf
    rw [← Ex] at Eax
    rw [← Eg] at Ebg
    rw [← Ey] at Eby
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    rw [← Eaf] at R
    obtain ⟨D, C, hfPi, ED, EC⟩ := proofErase_scoped_recovered_pi_descend hrec hΓ hΓ' W hf R
    rw [← Eaf, ← Ebg] at HF
    have Hfg := (proofErase_scoped_compare_descend hstep hΓ hΓ' W rfl hf hg HF).2 rfl
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have HfgPi := Hfg.of_l henv hΓ hfPi
    have hxD := argument_at_displayed_domain hΓ hf hfPi hx
    have hyD := argument_at_displayed_domain hΓ hg HfgPi.hasType.2 hy
    rw [← ED, ← Eax, ← Eby] at HX
    have Hxy := proofErase_structure_carrier_descend hstep hΓ hΓ' W hxD hyD HX
    exact ⟨_, IsDefEq.appDF HfgPi (Hxy.of_l henv hΓ hxD)⟩

/-- At the original context the recovered application root reflects at its
supplied left type. No global recovery-existence hypothesis is used. -/
theorem proofErase_scoped_recovered_carrier_application_reflect
    (hrec : ErasedScopedPrimitiveDescent Recovery) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (H : ProofShape.ScopedRecoveredCarrierApplication Recovery Step (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b)) : env.IsDefEq univs Γ a b T := by
  apply IsDefEqU.of_l henv hΓ _ ha
  apply proofErase_scoped_recovered_carrier_application_descend hrec hstep hΓ hΓ (Ctx.LiftN.zero []) ha hb
  simpa only [List.length_nil, ProofShape.liftN_zero] using H

/-- Typed non-proof applications expose the new root guard. The recovered
codomain need not be the selected original codomain; only its domain is used
to index the argument certificate. -/
theorem proofErase_scoped_recovered_carrier_application_forward
    (_hΓ : OnCtx Γ (env.IsType univs))
    (_hf : env.HasType univs Γ f (.forallE A B)) (_hg : env.HasType univs Γ g (.forallE A B))
    (_hx : env.HasType univs Γ x A) (_hy : env.HasType univs Γ y A)
    (hnl : ¬ IsProof Γ (.app f x)) (hnr : ¬ IsProof Γ (.app g y))
    (R : ProofShape.ScopedTypeRecovery Recovery (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE (proofErase Γ A) C))
    (HF : ProofShape.ScopedCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g))
    (HX : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ScopedRecoveredCarrierApplication Recovery Step (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hnl,
    show proofErase Γ (.app g y) = .app _ _ from if_neg hnr]
  exact .app R HF HX

end Lean4Lean.VEnv.Strengthening
