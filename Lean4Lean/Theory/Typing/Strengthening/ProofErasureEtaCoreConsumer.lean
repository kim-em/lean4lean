import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCorePrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAmbientBetaCompute

/-! # Full-core transport in arbitrary typed consumers of sorted eta

Actual source typing, primitive exposure and exact eta-origin simulation give
closure under arbitrary finite core computation, including all local binders.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params] {D : Definitions}

/-- Every full-core path from a typed consumer of a sorted eta variant has a
matching target path. Domain and function histories are concrete full-core
paths; no native certificate, normalization or comparison premise is required. -/
theorem sorted_eta_core_left (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (R : Compute (ErasedLevelCore D) a a')
    (V : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ b', Compute (ErasedLevelCore D) b b' ∧
      AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n a' b' := by
  induction R generalizing n b Γ e T with
  | base R => exact sorted_eta_core_primitive hs hΓ₀ hA hf hn R V hΓ ht Ee W
  | beta R =>
    apply ambient_variant_typed_beta_compute_left
      (Guard := EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (Atom := SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f)))
      (fun H R => H.compute_left (.beta R))
      (fun H R => sorted_eta_origin_core hs hΓ₀ hA hf hn H (.beta R)) ?_ R V hΓ ht Ee W
    intro n A body g x y Γ e T H VX hΓ ht Ee W
    obtain ⟨out, RB, VB⟩ := sorted_eta_core_origin_apply hs hΓ₀ hA hf hn H VX hΓ ht Ee W
    exact ⟨out, .beta RB, VB⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨b₁, RB, V₁⟩ := ih₁ V hΓ ht Ee W
    obtain ⟨e₁, RE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ ht rfl Ee (R₁.scoped (fun H => .base H))
    obtain ⟨b₂, RC, V₂⟩ := ih₂ V₁ hΓ RE.hasType.2 EE W
    exact ⟨b₂, RB.trans RC, V₂⟩
  | app RF RX ihf ihx =>
    cases V with
    | refl => exact ⟨_, .app RF RX, .refl⟩
    | app VF VX =>
      obtain ⟨f, x, rfl, _, EF, EX⟩ := erase_app_inv Ee
      obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
      obtain ⟨g, RG, VG⟩ := ihf VF hΓ hf EF W
      obtain ⟨y, RY, VY⟩ := ihx VX hΓ hx EX W
      exact ⟨_, .app RG RY, .app VG VY⟩
    | origin HO => exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.app RF RX)
  | proj R ih =>
    cases V with
    | refl => exact ⟨_, .proj R, .refl⟩
    | proj V =>
      obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
      obtain ⟨b, RB, VB⟩ := ih V hΓ hm.hasType.2 EM W
      exact ⟨_, .proj RB, .proj VB⟩
    | origin HO => exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.proj R)
  | lam RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .lam RA RB, .refl⟩
    | lam VA VB =>
      obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
      obtain ⟨C, RC, VC⟩ := ihA VA hΓ hA EA W
      obtain ⟨c, Rc, Vc⟩ := ihB (Γ := A :: Γ) VB ⟨hΓ, u, hA⟩ hb EB (ambient_cons W hΓ hA)
      exact ⟨_, .lam RC Rc, .lam VC Vc⟩
    | marked HG VB =>
      obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
      obtain ⟨A', RA', rfl⟩ := RA.level_core_lift_inv
      obtain ⟨c, Rc, Vc⟩ := ihB (Γ := A :: Γ) VB ⟨hΓ, u, hA⟩ hb EB (ambient_cons W hΓ hA)
      exact ⟨_, .lam .refl Rc, .marked (HG.compute_left RA') Vc⟩
    | origin HO => exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.lam RA RB)
  | forallE RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
      obtain ⟨C, RC, VC⟩ := ihA VA hΓ hA EA W
      obtain ⟨c, Rc, Vc⟩ := ihB (Γ := A :: Γ) VB ⟨hΓ, u, hA⟩ hb EB (ambient_cons W hΓ hA)
      exact ⟨_, .forallE RC Rc, .forallE VC Vc⟩
    | origin HO => exact sorted_eta_origin_core hs hΓ₀ hA hf hn HO (.forallE RA RB)

end Lean4Lean.VEnv.Strengthening
