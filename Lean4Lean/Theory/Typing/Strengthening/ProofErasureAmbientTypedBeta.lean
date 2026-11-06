import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAmbientEtaConsumer

/-! # Typed beta transport for protected ambient origins

Typing is needed only when an applied origin selects an erased proof argument.
All local substitutions remain paired; actual typed replay supplies the left
representative after each intermediate beta path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv beta_eq
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking

/-- A proof marker stays a proof marker when no ambient atom starts at proof. -/
theorem ProofShape.AmbientVariant.proof_right
    (ha : ∀ {a b}, Atom a b → a ≠ .proof) (V : AmbientVariant Guard Atom n .proof b) : b = .proof := by
  cases V with
  | refl => rfl
  | origin HO =>
    obtain ⟨x, y, HO, EX, _⟩ := HO
    have E : x = .proof := by cases x <;> cases EX; rfl
    exact (ha HO E).elim

variable [Params]

/-- Typed consumer beta transport requires actual typing only at the applied
origin interaction. Origin computation itself may use retained ambient typing.
No untyped proof-argument substitution law is assumed. -/
theorem ambient_variant_typed_beta_left
    (hg : ∀ {A C A'}, Guard A C → ProofShape.BetaRed A A' → Guard A' C)
    (ho : ∀ {n a a' b}, LiftedOrigin Atom n a b → ProofShape.BetaRed a a' →
      ∃ b', ProofShape.BetaRed b b' ∧ AmbientVariant Guard Atom n a' b')
    (hap : ∀ {n A body g x y Γ e T}, LiftedOrigin Atom n (.lam A body) g →
      AmbientVariant Guard Atom n x y → OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofErase Γ e = .app (.lam A body) x →
      ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i+n)) →
      ∃ out, ProofShape.BetaRed (.app g y) out ∧ AmbientVariant Guard Atom n (body.inst x) out)
    (R : ProofShape.BetaRed a a') (V : AmbientVariant Guard Atom n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ b', ProofShape.BetaRed b b' ∧ AmbientVariant Guard Atom n a' b' := by
  induction R generalizing n b Γ e T with
  | refl => exact ⟨_, .refl, V⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨b₁, RB, V₁⟩ := ih₁ V hΓ ht Ee W
    obtain ⟨e₁, RE, EE⟩ := proofErase_beta_replay hΓ ht (Ee ▸ R₁)
    obtain ⟨b₂, RC, V₂⟩ := ih₂ V₁ hΓ (beta_eq hΓ ht RE).hasType.2 EE W
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
    | origin HO => exact ho HO (.app RF RX)
  | proj R ih =>
    cases V with
    | refl => exact ⟨_, .proj R, .refl⟩
    | proj V =>
      obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
      obtain ⟨b, RB, VB⟩ := ih V hΓ hm.hasType.2 EM W
      exact ⟨_, .proj RB, .proj VB⟩
    | origin HO => exact ho HO (.proj R)
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
      obtain ⟨A', RA', rfl⟩ := RA.liftN_inv
      obtain ⟨c, Rc, Vc⟩ := ihB (Γ := A :: Γ) VB ⟨hΓ, u, hA⟩ hb EB (ambient_cons W hΓ hA)
      exact ⟨_, .lam .refl Rc, .marked (hg HG RA') Vc⟩
    | origin HO => exact ho HO (.lam RA RB)
  | forallE RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
      obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
      obtain ⟨C, RC, VC⟩ := ihA VA hΓ hA EA W
      obtain ⟨c, Rc, Vc⟩ := ihB (Γ := A :: Γ) VB ⟨hΓ, u, hA⟩ hb EB (ambient_cons W hΓ hA)
      exact ⟨_, .forallE RC Rc, .forallE VC Vc⟩
    | origin HO => exact ho HO (.forallE RA RB)
  | beta =>
    cases V with
    | refl => exact ⟨_, .beta, .refl⟩
    | app VF VX =>
      cases VF with
      | refl => exact ⟨_, .beta, AmbientVariant.refl.inst_pair VX⟩
      | lam _ VB => exact ⟨_, .beta, VB.inst_pair VX⟩
      | marked _ VB => exact ⟨_, .beta, VB.inst_pair VX⟩
      | origin HO => exact hap HO VX hΓ ht Ee W
    | origin HO => exact ho HO .beta

end Lean4Lean.VEnv.Strengthening
