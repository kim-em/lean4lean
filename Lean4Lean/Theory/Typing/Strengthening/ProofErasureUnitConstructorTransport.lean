import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitConstructorObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureUniverseJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiOriginTransport

/-! # Compatible computation of constructor controls

Beta substitutes demanded unit values rather than consulting their current
native types. Changed lambda annotations are transported by ordinary context
conversion. Root structure expansion still needs native parameter coverage;
this file proves no unconditional preservation for that primitive.
-/
namespace Lean4Lean.VEnv.Strengthening.UnitConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open HeterogeneousControl (ControlType ControlTyping)
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {c r : Name} {unit record : AtomicControl.Atom}

/-- Primitive observation preservation extends to all compatible paths. Node
typings supply the ordinary context interpretations needed at changed binders. -/
theorem Obs.compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b S t o}, Step Δ a b → Obs unit record c r Δ S a t o → Obs unit record c r Δ S b t o)
    (R : ScopedCompute Step Δ source out) (HS : S.Typed Δ) (H : Obs unit record c r Δ S source t o) :
    Obs unit record c r Δ S out t o := by
  induction R using ScopedCompute.rootBeta_induction generalizing S t o with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward HS
  | trans _ _ ih₁ ih₂ => exact ih₂ HS (ih₁ HS H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF RX)
    cases H with
    | app _ HF HX => exact .app HT (ihf HS HF) (fun key hk => ihx HS (HX key hk))
  | proj => exact H.not_proj.elim
  | forallE => exact H.not_pi.elim
  | @lam Δ D D' b b' RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.lam RA RB)
    obtain ⟨Γ, f, hΓ, EΓ, hf, Ef⟩ := H.typing
    obtain ⟨A, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
    have EΓA : proofEraseCtx (A :: Γ) = D :: Δ := by simp only [proofEraseCtx, EA, EΓ]
    have SD : DomainSort Δ D u := ⟨Γ, A, hΓ, EΓ, hA, EA⟩
    obtain ⟨A', HA', EA'⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA RA
    have HC : IsDefEqCtx env univs [] (A :: Γ) (A' :: Γ) := .succ (.refl hΓ) HA'
    have WC : ContextSubstitution (D :: Δ) (D' :: Δ) ProofShape.Subst.id := by
      intro Γ₀ hΓ₀ EΓ₀
      have HH := AtomicControl.control_context_substitution HC hΓ₀ (EΓA.trans EΓ₀.symm).symm
      simpa only [proofEraseCtx, EA', EΓ] using HH
    cases H with
    | lam HL HK HB =>
      exact .lam HT HK ((ihb (HS.cons HL.lam_parts.2 SD) HB).context WC)

end Lean4Lean.VEnv.Strengthening.UnitConstructorObservation
