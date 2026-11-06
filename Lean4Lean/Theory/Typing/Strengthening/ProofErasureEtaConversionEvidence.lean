import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCoreReadoutTransport

/-! # Conversion evidence inside arguments supplies eta readout after beta

A retained comparison of a lambda's assigned and written domains constructs
its complete eta readout evidence. Function computation and identity wrappers
then preserve it, without relying on the wrapper's outer native certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A literal lambda's full eta readout follows from retained comparisons of
its assigned and written domain residuals. The body need not have a native
certificate or normalize. Actual input sorts validate inferred lambda readout. -/
theorem eta_core_readout_lambda_of_domains (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hC : env.HasType univs Γ C (.sort u))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (HD : ∀ {X Y}, Compute (ErasedLevelCore D) (proofErase Γ A) X →
      Compute (ErasedLevelCore D) (proofErase Γ C) Y →
      ComputedJointCompare Step (proofEraseCtx Γ) true X Y) :
    EtaCoreReadout D Step (proofEraseCtx Γ) u (proofErase Γ A) (proofErase Γ (.lam C b)) := by
  have EF : proofErase Γ (.lam C b) = .lam (proofErase Γ C) (proofErase (C :: Γ) b) := if_neg hn
  constructor
  · intro X Y HG
    rcases HG with ⟨RA, body, RF⟩ | ⟨RA, body, RF⟩
    · rw [EF] at RF
      obtain ⟨C', b', E, RC, _⟩ := RF.level_core_lam_inv
      cases E
      exact HD RA RC
    · rw [EF] at RF
      obtain ⟨C', b', E, RC, _⟩ := RF.level_core_lam_inv
      cases E
      exact (HD RA RC).symm
  · intro X g mode HG
    obtain ⟨RA, RF⟩ := HG
    have RF₀ := RF
    rw [EF] at RF
    obtain ⟨Y, body, rfl, RC, _⟩ := RF.level_core_lam_inv
    have RB := sorted_eta_lambda_beta_of_core_origin hs hΓ hA hf RF₀ X
    exact .compute (.beta RB) .refl (.lamSorted
      (proofErase_level_core_domain_sort hs hΓ hA RA)
      (proofErase_level_core_domain_sort hs hΓ hC RC)
      (HD RA RC) (.leaf .refl))

/-- A concrete earlier conversion certificate supplies every domain residual
check used by lambda eta readout at the same stage. Its evidence is retained
from the conversion, rather than reconstructed from the assigned function type. -/
theorem eta_core_readout_lambda_of_conversion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hC : env.HasType univs Γ C (.sort u))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (HD : CoreFamilyCast D stage (.compare true) (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C)) :
    EtaCoreReadout D (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) u
      (proofErase Γ A) (proofErase Γ (.lam C b)) :=
  eta_core_readout_lambda_of_domains hs hΓ hA hC hf hn
    (fun RA RC => HD.forward heq hs hl hcon hc hreg hoff hD RA RC)

/-- The argument's retained evidence supplies eta comparison inside every
consumer of its identity wrapper, after arbitrary independent core paths.
This carries the inner conversion dependency through beta at the same stage. -/
theorem EtaCoreReadout.identity_consumer
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hcore : ∀ {Δ a b}, ErasedLevelCore D a b → Step Δ a b)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (H : EtaCoreReadout D Step (proofEraseCtx Γ) u (proofErase Γ A) (proofErase Γ f))
    (RL : Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (.lam A (.app (VExpr.app (.lam (.forallE A B) (.bvar 0)) f).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (.app (.lam (.forallE A B) (.bvar 0)) f))) right) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode left right := by
  have HW := (eta_core_readout_identity_iff (fun H => hcore H) hc hΓ hf).2 H
  exact HW.consumer hs hc (fun H => hcore H) (fun H W => hrename H W)
    hΓ hA (nativeIdentityExpansion_equal hf).hasType.1 ht RL RR

end Lean4Lean.VEnv.Strengthening
