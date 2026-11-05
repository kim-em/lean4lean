import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasDemandReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureControlWorlds

/-! # Initializing finite alias observations from actual stored declarations

Aliases carry actual stored equations, ordinary sort typing, and independently
observed bodies. Arbitrary dependent beta wrappers and finite alias chains can
be nested; no argument native-type certificate is requested.
-/
namespace Lean4Lean.VEnv.Strengthening.AliasDemandProfile
open _root_.Lean4Lean Params ProofShape DemandProfile
variable [Params]

/-- A stored type alias inherits its independently observed body. Closed-body
erasure is transported from the declaration context to the actual context. -/
theorem Obs.stored_alias
    (HD : (PureObservation.Definitions.ofEnv env univs henv).unfolds name [] rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hB : env.HasType univs Γ rhs (.sort u))
    (HB : Obs c arity (proofEraseCtx Γ) S (proofErase Γ rhs) .sort .pi) :
    Obs c arity (proofEraseCtx Γ) S (proofErase Γ (.const name [])) .sort .pi := by
  have hs := PureObservation.Definitions.ofEnv_sound (U := univs) henv
  have ht := ((hs Γ name [] rhs HD).of_r henv hΓ hB).hasType.1
  have EE : proofErase Γ (.const name []) = .const name [] := if_neg (not_isProof_of_sort hΓ ht)
  obtain ⟨T, HE⟩ := hs [] name [] rhs HD
  have EC := proofErase_closed_context
    ((PureObservation.Definitions.ofEnv env univs henv).closed HD) HE.hasType.2 hΓ
  obtain ⟨_, hU⟩ := ht.isType henv hΓ
  rw [EE]
  exact .delta ⟨Γ, _, _, hΓ, rfl, ht, Fits.of_sortTelescope hΓ hU .sort, EE⟩ HD (EC ▸ HB)

/-- A typed type-valued beta wrapper carries its body's family demand with
no demand on the supplied argument. The displayed domain may be open or Prop. -/
theorem Obs.typed_wrapper
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (hx : env.HasType univs Γ x A)
    (H : Obs family arity (proofEraseCtx (A :: Γ)) (fun _ _ _ => False)
      (proofErase (A :: Γ) B) .sort .pi) :
    Obs family arity (proofEraseCtx Γ) (fun _ _ _ => False)
      (proofErase Γ (.app (.lam A B) x)) .sort .pi := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hf := HasType.lam hA hB
  have ht : env.HasType univs Γ (.app (.lam A B) x) (.sort v) := .app hf hx
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, hV⟩ := ht.isType henv hΓ
  have EF : proofErase Γ (.lam A B) = .lam (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have EE : proofErase Γ (.app (.lam A B) x) =
      .app (.lam (proofErase Γ A) (proofErase (A :: Γ) B)) (proofErase Γ x) := by
    rw [show proofErase Γ (.app (.lam A B) x) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ ht), EF]
  rw [EE]
  refine .app (A := .ignored) (keys := [])
    ⟨Γ, _, _, hΓ, rfl, ht, DemandProfile.Fits.of_sortTelescope hΓ hV .sort, EE⟩
    (.lam ⟨Γ, _, _, hΓ, rfl, hf, DemandProfile.Fits.of_sortTelescope hΓ hPi (.forallE .sort), EF⟩
      (by simp) ?_) (by simp)
  simpa only [ProofShape.subst_id, proofEraseCtx] using
    H.rename ContextRenaming.identity.interpretation
      (T := DemandProfile.Sets.cons .ignored [] (fun _ _ _ => False)) (by intro i t k h; cases h)


/-- An actual stored alias of a rigid family is outside the old observation
grammar, even when its body has an old observation. Registry separation ensures
that the alias name differs from the designated rigid family. -/
theorem stored_alias_not_rigid_observation
    (hc : env.Rigid c)
    (HD : (PureObservation.Definitions.ofEnv env univs henv).unfolds name [] rhs) :
    ¬ RigidDemandProfile.Obs c arity Δ S (.const name []) t o := by
  intro H
  cases H with
  | const => exact PureObservation.Definitions.ofEnv_no_rigid henv hc HD

/-- A declared alias with an independently observed body remains observable
through the full enriched union, and exposes its family after raw substitution. -/
theorem stored_alias_full_readout
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid c)
    (HD : (PureObservation.Definitions.ofEnv env univs henv).unfolds name [] rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hB : env.HasType univs Γ rhs (.sort u))
    (HB : Obs c arity (proofEraseCtx Γ) (fun _ _ _ => False) (proofErase Γ rhs) .sort .pi)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion
      (PureObservation.Definitions.ofEnv env univs henv)) (proofEraseCtx Γ)
      (proofErase Γ (.const name [])) out) :
    HeadResult c arity (out.subst σ) :=
  (HB.stored_alias HD hΓ hB).full_readout heq hcon hc R

end Lean4Lean.VEnv.Strengthening.AliasDemandProfile
