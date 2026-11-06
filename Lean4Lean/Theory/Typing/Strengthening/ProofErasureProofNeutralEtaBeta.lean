import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProofNeutralEtaVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralEtaChecking

/-! # Typed beta simulation for proof-domain neutral eta

A proof-domain mark may erase its bound argument. Source typing ensures that
applying that marked wrapper also supplies a proof-erased argument. This closes
the beta case without assuming a false raw substitution principle.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv beta_eq
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons subst_shift
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params] {Guard : ProofShape → Nat → Prop}

/-- A sort witness for the written domain of an actual beta redex forces its
argument to erase to proof. The witness may use a different typed representative
of that domain; erasure reflection transfers its sort. -/
theorem proofErase_beta_proof_argument
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.app (.lam A body) x) T)
    (SA : DomainSort (proofEraseCtx Γ) (proofErase Γ A) .zero) :
    proofErase Γ x = .proof := by
  have hx := ht.app_lam_arg hΓ
  obtain ⟨v, hA⟩ := hx.isType henv hΓ
  have hA0 : env.HasType univs Γ A (.sort .zero) := by
    obtain ⟨A', hA', EA'⟩ := SA.realize hΓ
    have HU := proofErase_sort_levels hΓ hA hA' EA'.symm
    exact (IsDefEq.sortDF (hA.sort_r henv hΓ) (hA'.sort_r henv hΓ) HU).defeq hA
  exact proofErase_eq_proof.2 ⟨A, hx, hA0⟩

omit [Params] in
private theorem proof_neutral_body_beta_fixed
    (R : ProofShape.BetaRed (.app (.bvar i) .proof) out) :
    out = .app (.bvar i) .proof := by
  apply R.fixed_of_normal (Step := fun _ _ => False)
  exact ⟨fun _ H => H, (by intro A b H; cases H),
    ⟨fun _ H => H, trivial⟩, ⟨fun _ H => H, trivial⟩⟩

/-- Actual source typing supplies the erased proof at each applied eta mark.
All other beta cases use protected paired substitution. The ambient domain
sorts and exact renaming are retained beneath every consumer binder. -/
theorem proof_neutral_eta_beta_left
    (hg : ∀ {A i A'}, Guard A i → ProofShape.BetaRed A A' → Guard A' i)
    (hsort : ∀ {A i}, Guard A i → DomainSort Δ A .zero)
    (R : ProofShape.BetaRed a a') (V : ProofNeutralEtaVariant Guard n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ b', ProofShape.BetaRed b b' ∧ ProofNeutralEtaVariant Guard n a' b' := by
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
      obtain ⟨A', RA', rfl⟩ := RA.liftN_inv
      obtain rfl := proof_neutral_body_beta_fixed RB
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
  | beta =>
    cases V with
    | refl => exact ⟨_, .beta, .refl⟩
    | app VF VX =>
      cases VF with
      | refl => exact ⟨_, .beta, ProofNeutralEtaVariant.refl.inst_pair VX⟩
      | lam _ VB => exact ⟨_, .beta, VB.inst_pair VX⟩
      | etaL HG =>
        obtain ⟨f, x, rfl, _, EF, EX⟩ := erase_app_inv Ee
        obtain ⟨A, body, rfl, _, EA, _⟩ := erase_lam_inv EF
        have SA := ContextSubstitution.sort W.interpretation (hsort HG)
        simp only [subst_shift, ← EA] at SA
        have EP := proofErase_beta_proof_argument hΓ ht SA
        have EX' := EX.symm.trans EP
        subst_vars
        simp only [EP] at VX ⊢
        obtain rfl := VX.proof_right
        refine ⟨_, .refl, ?_⟩
        simpa [ProofShape.inst, instVar] using (ProofNeutralEtaVariant.refl (Guard := Guard) (n := n)
          (a := ProofShape.app (.bvar _) .proof))

end Lean4Lean.VEnv.Strengthening
