import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProofNeutralEtaCorePrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProofNeutralEtaBeta

/-! # Typed full-core simulation of proof-domain neutral eta

Primitive steps preserve matching and captures. At beta steps source typing
justifies the erased proof argument. Exact ambient renaming and replay retain
that justification through arbitrary finite paths and under local binders.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params] {D : Definitions} {Guard : ProofShape → Nat → Prop}

private theorem proof_neutral_body_core_fixed
    (R : Compute (ErasedLevelCore D) (.app (.bvar i) .proof) out) :
    out = .app (.bvar i) .proof := by
  apply NormalSyntax.fixed (Step := ErasedLevelCore D) ?_ R
  refine ⟨?_, (by intro A b H; cases H), ⟨?_, trivial⟩, ⟨?_, trivial⟩⟩
  all_goals
    intro out H
    rcases H with H | H
    · exact erased_iota_primitive_head H
    · cases H

/-- Full ordinary-core paths preserve the proof-domain variants. Actual source
typing supplies erased proof arguments at beta steps; primitive simulation,
replay and exact ambient renaming retain this justification under binders. -/
theorem proof_neutral_eta_core_left
    (hs : D.Sound env univs)
    (hg : ∀ {A i A'}, Guard A i → Compute (ErasedLevelCore D) A A' → Guard A' i)
    (hsort : ∀ {A i}, Guard A i → DomainSort Δ A .zero)
    (R : Compute (ErasedLevelCore D) a a') (V : ProofNeutralEtaVariant Guard n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ b', Compute (ErasedLevelCore D) b b' ∧ ProofNeutralEtaVariant Guard n a' b' := by
  induction R generalizing n b Γ e T with
  | base R =>
    obtain ⟨b', RB, VB⟩ := erased_level_core_proof_neutral_eta_variant R V
    exact ⟨b', .base RB, VB⟩
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
  | proj R ih =>
    cases V with
    | refl => exact ⟨_, .proj R, .refl⟩
    | proj V =>
      obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
      obtain ⟨b, RB, VB⟩ := ih V hΓ hm.hasType.2 EM W
      exact ⟨_, .proj RB, .proj VB⟩
  | lam RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .lam RA RB, .refl⟩
    | lam VA VB =>
      obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
      obtain ⟨C, RC, VC⟩ := ihA VA hΓ hA EA W
      obtain ⟨c, Rc, Vc⟩ := ihB (Γ := A :: Γ) VB ⟨hΓ, u, hA⟩ hb EB (ambient_cons W hΓ hA)
      exact ⟨_, .lam RC Rc, .lam VC Vc⟩
    | etaL HG =>
      obtain ⟨A', RA', rfl⟩ := RA.level_core_lift_inv
      obtain rfl := proof_neutral_body_core_fixed RB
      exact ⟨_, .refl, .etaL (hg HG RA')⟩
  | forallE RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
      obtain ⟨C, RC, VC⟩ := ihA VA hΓ hA EA W
      obtain ⟨c, Rc, Vc⟩ := ihB (Γ := A :: Γ) VB ⟨hΓ, u, hA⟩ hb EB (ambient_cons W hΓ hA)
      exact ⟨_, .forallE RC Rc, .forallE VC Vc⟩
  | beta R =>
    obtain ⟨b', RB, VB⟩ := proof_neutral_eta_beta_left
      (Guard := Guard) (fun H R => hg H (.beta R)) (fun H => hsort H) R V hΓ ht Ee W
    exact ⟨b', .beta RB, VB⟩

end Lean4Lean.VEnv.Strengthening
