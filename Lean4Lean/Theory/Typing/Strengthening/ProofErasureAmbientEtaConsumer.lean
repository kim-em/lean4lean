import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAmbientEtaBeta

/-! # Actual consumers of arbitrary functions retain eta origins through beta

The domain guard records exactly the lambda annotations exposed by beta paths
from the supplied function. No native recovery or semantic comparison is used
to construct the residual relation. Readout keeps these obligations explicit.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private beta_eq erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons subst_shift
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking

namespace ProofShape
/-- The written annotation and short function retain their separate beta origins. -/
def EtaBetaOrigin (A₀ f₀ A f : ProofShape) : Prop := BetaRed A₀ A ∧ BetaRed f₀ f

/-- Emerging annotation marks retain an exposed lambda domain of the supplied
function, paired with a reduct of its original eta domain, in either direction. -/
def EtaBetaDomains (A₀ f₀ A C : ProofShape) : Prop :=
  (BetaRed A₀ A ∧ ∃ b, BetaRed f₀ (.lam C b)) ∨
  (BetaRed A₀ C ∧ ∃ b, BetaRed f₀ (.lam A b))

/-- Reversing an annotation mark retains its two original histories. -/
theorem EtaBetaDomains.symm (H : EtaBetaDomains A₀ f₀ A C) : EtaBetaDomains A₀ f₀ C A :=
  Or.symm H

/-- Further annotation beta computation stays in its recorded origin. On the
exposed side it is replayed under the original function's lambda. -/
theorem EtaBetaDomains.beta_left (H : EtaBetaDomains A₀ f₀ A C) (R : BetaRed A A') :
    EtaBetaDomains A₀ f₀ A' C := by
  rcases H with ⟨HA, b, HF⟩ | ⟨HC, b, HF⟩
  · exact .inl ⟨HA.trans R, b, HF⟩
  · exact .inr ⟨HC, b, HF.trans (.lam R .refl)⟩

/-- Concrete source histories discharge all guard premises of beta simulation. -/
theorem eta_beta_origin_residuals
    (V : AmbientVariant (EtaBetaDomains A₀ f₀) (RetainedEtaAtom (EtaBetaOrigin A₀ f₀)) n a b)
    (RA : BetaRed a p) (RB : BetaRed b q) :
    ∃ p' q', BetaRed p p' ∧ BetaRed q q' ∧
      AmbientVariant (EtaBetaDomains A₀ f₀) (RetainedEtaAtom (EtaBetaOrigin A₀ f₀)) n p' q' :=
  ambient_eta_beta_residuals
    (Guard := EtaBetaDomains A₀ f₀) (EtaGuard := EtaBetaOrigin A₀ f₀)
    (fun H => H.symm) (fun H R => H.beta_left R)
    (fun H RA RF => ⟨H.1.trans RA, H.2.trans RF⟩)
    (fun H => .inl ⟨H.1, _, H.2⟩) V RA RB
end ProofShape

variable [Params]

/-- An arbitrary actual function supplies the protected eta origin. Only the
input domain is required to retain the fresh argument; proof-valued functions
are allowed and their two erasures coincide. -/
theorem proofErase_ambient_eta_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hu : ¬ u ≈ .zero) :
    AmbientVariant (EtaBetaDomains (proofErase Γ A) (proofErase Γ f))
      (RetainedEtaAtom (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f))) 0
      (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) (proofErase Γ f) := by
  by_cases hn : IsProof Γ f
  · rw [proofErase_eq_proof.2 hn,
      proofErase_eq_proof.2 ((isProof_congr hΓ (IsDefEq.eta hf)).2 hn)]
    exact .refl
  · rw [proofErase_nativeEtaExpansion hΓ hA hf hn]
    exact .origin ⟨retainedEta (proofErase Γ A) (proofErase Γ f), proofErase Γ f,
      .etaL ⟨.refl, .refl⟩, by simp only [ProofShape.liftN_zero, retainedEta, etaArgument, if_neg hu],
      by simp only [ProofShape.liftN_zero]⟩

/-- Every occurrence in a typed consumer retains the original eta certificate,
including occurrences in dependent annotations. The short function is arbitrary. -/
theorem proofErase_ambient_eta_consumer_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T) :
    AmbientVariant (EtaBetaDomains (proofErase Γ A) (proofErase Γ f))
      (RetainedEtaAtom (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f))) 0
      (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) := by
  have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  rw [proofErase_instN hΓF (IsDefEq.eta hf).hasType.1 Ctx.InstN.zero ht,
    proofErase_instN hΓF hf Ctx.InstN.zero ht]
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
  apply AmbientVariant.subst_images
  intro i
  cases i with
  | zero => exact proofErase_ambient_eta_variant hΓ hA hf hu
  | succ i => exact .refl

/-- Unconditional beta residual coverage for arbitrary supplied functions with
retained input arguments. The relation records the domains exposed during
computation; there is no native coverage, comparison, or head-exposure premise. -/
theorem proofErase_ambient_eta_consumer_beta_residuals
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : ProofShape.BetaRed (proofErase Γ (t.inst f)) right) :
    ∃ left' right', ProofShape.BetaRed left left' ∧ ProofShape.BetaRed right right' ∧
      AmbientVariant (EtaBetaDomains (proofErase Γ A) (proofErase Γ f))
        (RetainedEtaAtom (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f))) 0 left' right' :=
  eta_beta_origin_residuals (proofErase_ambient_eta_consumer_variant hΓ hA hf hu ht) RL RR

/-- Every exposed domain pair has actual representatives at the original
input sort and an actual equality there. The body retains its erasure in the
exposed binder context. This semantic origin does not itself supply the
strengthening-safe inferred certificate required by consumer readout. -/
theorem proofErase_eta_beta_domain_origin
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RA : ProofShape.BetaRed (proofErase Γ A) X)
    (RF : ProofShape.BetaRed (proofErase Γ f) (.lam C body)) :
    ∃ A' C' b, env.HasType univs Γ A' (.sort u) ∧ env.HasType univs Γ C' (.sort u) ∧
      env.IsDefEq univs Γ A' C' (.sort u) ∧ proofErase Γ A' = X ∧
      proofErase Γ C' = C ∧ proofErase (C' :: Γ) b = body := by
  obtain ⟨A', RA', EA⟩ := proofErase_beta_replay hΓ hA RA
  have HA := beta_eq hΓ hA RA'
  obtain ⟨g, RG, EG⟩ := proofErase_beta_replay hΓ hf RF
  have hg := (beta_eq hΓ hf RG).hasType.2
  obtain ⟨C', b, rfl, _, EC, EB⟩ := erase_lam_inv EG
  obtain ⟨⟨v, hC⟩, _, hb⟩ := hg.lam_inv henv hΓ
  obtain ⟨⟨_, HCA⟩, _⟩ := ((HasType.lam hC hb).uniqU henv hΓ hg).forallE_inv henv hΓ
  have HAC := HCA.toU.symm.of_l henv hΓ hA
  exact ⟨A', C', b, HA.hasType.2, HAC.hasType.2, HA.symm.trans HAC, EA, EC, EB⟩

/-- Retained ambient atom and domain comparisons read out the complete consumer
syntax. Exact renaming transports them under binders; arbitrary substitution
closure of the comparison relation is not assumed. -/
theorem ambient_variant_computed_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hguard : ∀ {A C}, Guard A C → ComputedJointCompare Step Δ false A C)
    (horigin : ∀ {a b mode}, Atom a b → ComputedJointCompare Step Δ mode a b)
    (V : AmbientVariant Guard Atom n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode a b := by
  induction V generalizing Γ e T mode with
  | refl => exact .leaf .refl
  | app VF VX ihf ihx =>
    obtain ⟨f, x, rfl, _, EF, EX⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EF W) (ihx hΓ hx EX W)
  | proj V ih =>
    obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ih hΓ hm.hasType.2 EM W)
  | lam VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    apply ComputedJointCheck.lam (ihA hΓ hA EA W)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    simpa only [proofEraseCtx, EA] using ihB hΓA hb EB (ambient_cons W hΓ hA)
  | forallE VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
    apply ComputedJointCheck.forallE (ihA hΓ hA EA W)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    simpa only [proofEraseCtx, EA] using ihB hΓA hb EB (ambient_cons W hΓ hA)
  | marked HG VB ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HB := ihB (mode := mode) hΓA hb EB (ambient_cons W hΓ hA)
    have HG' := (hguard HG).rename hrename W
    simp only [JointCheckKind.subst, subst_shift] at HG'
    simp only [proofEraseCtx, EA] at HB
    exact .lam HG' HB
  | origin HO =>
    obtain ⟨a, b, HO, rfl, rfl⟩ := HO
    have H := (horigin (mode := mode) HO).rename hrename W
    simpa only [JointCheckKind.subst, subst_shift] using H

/-- Arbitrary consumer beta residuals compare once every recorded eta origin
and emerging lambda-domain pair has an ambient inferred certificate. Those two
coverage premises are still missing in general; the theorem supplies consumer
transport and does not assume global comparison stability under substitution. -/
theorem proofErase_ambient_eta_consumer_beta_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (hguard : ∀ {C E}, EtaBetaDomains (proofErase Γ A) (proofErase Γ f) C E →
      ComputedJointCompare Step (proofEraseCtx Γ) false C E)
    (heta : ∀ {C g mode}, EtaBetaOrigin (proofErase Γ A) (proofErase Γ f) C g →
      ComputedJointCompare Step (proofEraseCtx Γ) mode (retainedEta C g) g)
    (RL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : ProofShape.BetaRed (proofErase Γ (t.inst f)) right) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode left right := by
  obtain ⟨left', right', PL, PR, V⟩ :=
    proofErase_ambient_eta_consumer_beta_residuals hΓ hA hf hu ht RL RR
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  obtain ⟨e, RE, EE⟩ := proofErase_beta_replay hΓ hleft (RL.trans PL)
  have HO {a b mode} (H : RetainedEtaAtom (EtaBetaOrigin (proofErase Γ A) (proofErase Γ f)) a b) :
      ComputedJointCompare Step (proofEraseCtx Γ) mode a b := by
    cases H with
    | etaL H => exact heta H
    | etaR H => exact (heta H).symm
  exact .compute (.beta PL) (.beta PR)
    (ambient_variant_computed_check hrename (fun H => hguard H) (fun H => HO H) V
      hΓ (beta_eq hΓ hleft RE).hasType.2 EE ContextRenaming.identity)

/-- Native-domain certificates for the actual beta descendants discharge the
eta-origin readout. The only remaining comparison premise concerns the exposed
lambda-domain pairs recorded by EtaBetaDomains. Both coverage assumptions are
explicit; no arbitrary consumer substitution principle is supplied by the caller. -/
theorem proofErase_ambient_eta_consumer_beta_check_of_native_domains
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (hguard : ∀ {C E}, EtaBetaDomains (proofErase Γ A) (proofErase Γ f) C E →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
        (proofEraseCtx Γ) false C E)
    (Hnative : ∀ {C g}, EtaBetaOrigin (proofErase Γ A) (proofErase Γ f) C g →
      ∃ X Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
        (proofEraseCtx Γ) g (.forallE X Y) ∧ DomainSort (proofEraseCtx Γ) X u ∧
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
          (proofEraseCtx Γ) false C X)
    (RL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : ProofShape.BetaRed (proofErase Γ (t.inst f)) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode left right := by
  apply proofErase_ambient_eta_consumer_beta_check
    (erased_static_structure_eta_expansion_stage_rename heq hs (stage+1))
    hΓ hA hf hu ht (fun H => hguard H) ?_ RL RR
  intro C g mode H
  obtain ⟨X, Y, RN, SC, HX⟩ := Hnative H
  obtain ⟨g₀, RG, EG⟩ := proofErase_beta_replay hΓ hf H.2
  have hg := (beta_eq hΓ hf RG).hasType.2
  rw [← EG] at RN ⊢
  apply classified_eta_native_domain_check hΓ hA hg ?_ RN SC HX
  exact .inl (by simp only [etaArgument, if_neg hu])

end Lean4Lean.VEnv.Strengthening
