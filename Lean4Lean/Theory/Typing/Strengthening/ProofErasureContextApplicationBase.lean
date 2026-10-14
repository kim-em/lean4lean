import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextApplicationSupport
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalApplication

/-! # Applying the raw base of contextual comparison

Typed head eta has a normal certificate, while structure eta cannot compare
functions. Computation is replayed at the supplied common function type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
variable [Params]

/-- A head eta certificate between common-typed originals has a bidirectional
normal certificate. The retained or erased fresh argument is typed explicitly. -/
theorem proofErase_eta_head_normal (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (hf : env.HasType univs Γ f T)
    (H : ProofShape.EtaHead (proofErase Γ e) (proofErase Γ f)) :
    ∃ n, BiNormal true n Γ e f := by
  obtain ⟨_, arg, HE, Harg⟩ := H.shape
  obtain ⟨A, body, rfl, _, _, Hb⟩ := erase_lam_inv HE
  obtain ⟨g, a, rfl, hnb, Hg, Ha⟩ := erase_app_inv Hb
  obtain ⟨⟨u, hA⟩, B, hb⟩ := he.lam_inv henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hfPi : env.HasType univs Γ f (.forallE A B) :=
    hf.defeqU_r henv hΓ (he.uniqU henv hΓ (HasType.lam hA hb))
  have hfw := hfPi.weak henv (B := A)
  have Ef := proofErase_liftN hΓ hΓA Ctx.LiftN.one hfPi
  have Eg : proofErase (A :: Γ) g = proofErase (A :: Γ) f.lift := Hg.trans Ef.symm
  obtain ⟨_, _, hg, ha⟩ := HasType.app_inv henv hΓA hb
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓA hg hfw Eg).2 (not_isProof_fn hΓA hg ha hnb)
  have Hgf := (HC.defeq hΓA).of_l henv hΓA hg
  obtain ⟨⟨_, hCA⟩, _⟩ := (Hgf.hasType.2.uniqU henv hΓA hfw).forallE_inv henv hΓA
  have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hxC := hCA.symm.defeq hx
  have Harg' : ∃ n, BiNormal true n (A :: Γ) a (.bvar 0) := by
    rcases Harg with rfl | rfl
    · obtain rfl := erase_bvar_inv Ha
      exact ⟨_, .refl ha⟩
    · obtain ⟨P, haP, hP⟩ := proofErase_eq_proof.1 Ha
      exact ⟨_, .proofIrrel hP haP (hxC.defeqU_r henv hΓA (ha.uniqU henv hΓA haP))⟩
  obtain ⟨_, HFn⟩ := HC.toBiNormal
  obtain ⟨_, HAn⟩ := Harg'
  exact ⟨_, .etaL hfPi (.appDF hg Hgf.hasType.2 ha hxC HFn HAn)⟩

/-- Applying a beta join yields a contextual certificate by erasing both paths
and embedding its terminal normal comparison. -/
theorem BiBetaJoin.context_compare (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : BiBetaJoin mode Γ a b) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) := by
  obtain ⟨_, _, _, Ra, Rb, HC⟩ := H
  exact .compute (.beta (proofErase_beta_forward hΓ ha Ra))
    (.beta (proofErase_beta_forward hΓ hb Rb)) (HC.context_compare hΓ)

/-- Common-typed head eta can be applied to the same argument without turning
its function certificate into inferred mode. -/
theorem proofErase_context_apply_eta_head (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.EtaHead (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  obtain ⟨_, HC⟩ := proofErase_eta_head_normal hΓ hf hg H
  exact (HC.apply_same_arg hΓ hf hg hx).context_compare hΓ (.app hf hx) (.app hg hx)

/-- Structure eta cannot have a function-typed long endpoint: its saturated
constructor has the registered rigid family as its natural type. -/
theorem proofErase_function_not_structure_eta (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e (.forallE A B)) :
    ¬ ProofShape.StructureEtaHead (proofErase Γ e) m := by
  intro H
  generalize Ee : proofErase Γ e = er at H
  cases H with
  | intro hi hx hp hf _ _ =>
    obtain ⟨args, rfl, Hargs⟩ := proofErase_const_spine_inv Ee
    have hlen := congrArg List.length Hargs
    simp only [List.length_append, List.length_map, hp, hf] at hlen
    have hnat := structure_constructor_family hΓ hi hx hlen.symm ht
    obtain ⟨_, hfamily⟩ := hnat.isType henv hΓ
    exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi)
      hfamily (hnat.uniqU henv hΓ ht)

/-- Raw lambda heads expose the typed body comparison needed for application.
The raw binder context is rewritten to the actual left lambda context. -/
theorem proofErase_context_apply_lam_shapes
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (Ef : proofErase Γ f = .lam D b) (Eg : proofErase Γ g = .lam D' b')
    (H : ProofShape.ContextCompare Step (D :: proofEraseCtx Γ) true b b') :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  obtain ⟨_, _, rfl, _, rfl, rfl⟩ := erase_lam_inv Ef
  obtain ⟨_, _, rfl, _, rfl, rfl⟩ := erase_lam_inv Eg
  exact proofErase_context_apply_lams hsubst hΓ hf hg hx H

/-- The original raw comparison applies to a shared typed argument. This holds
in either mode; common lambda bodies are instantiated instead of promoted. -/
theorem proofErase_compare_apply_same
    (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.Compare Step mode (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  generalize Ef : proofErase Γ f = sf at H
  generalize Eg : proofErase Γ g = sg at H
  induction H generalizing f g A B with
  | refl =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (.base (by rw [Ef, Eg]; exact .refl)))
  | sort H =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (.base (by rw [Ef, Eg]; exact .sort H)))
  | const H =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (.base (by rw [Ef, Eg]; exact .const H)))
  | app Hf Hx =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (.base (by rw [Ef, Eg]; exact .app Hf Hx)))
  | proj H =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (.base (by rw [Ef, Eg]; exact .proj H)))
  | lam HD Hb =>
    exact proofErase_context_apply_lam_shapes hsubst hΓ hf hg hx Ef Eg (.base (.base Hb.common))
  | forallE HD HB =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (.base (by rw [Ef, Eg]; exact .forallE HD HB)))
  | etaL H => exact proofErase_context_apply_eta_head hΓ hf hg hx (by rwa [Ef, Eg])
  | etaR H => exact .symm (proofErase_context_apply_eta_head hΓ hg hf hx (by rwa [Ef, Eg]))
  | structL H => exact (proofErase_function_not_structure_eta hΓ hf (Ef ▸ H)).elim
  | structR H => exact (proofErase_function_not_structure_eta hΓ hg (Eg ▸ H)).elim
  | etaLams HD H =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (.base (by rw [Ef, Eg]; exact .etaLams HD H)))
  | compute Rf Rg HC ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨f', HF, EF⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero, Ef] using Rf)
    obtain ⟨g', HG, EG⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hg
      (by simpa only [ProofShape.liftN_zero, Eg] using Rg)
    simp only [ProofShape.liftN_zero] at EF EG
    exact .compute
      (proofErase_compute_apply_same hΓ hf HF.hasType.2 hx (by rwa [Ef, EF]))
      (proofErase_compute_apply_same hΓ hg HG.hasType.2 hx (by rwa [Eg, EG]))
      (ih HF.hasType.2 HG.hasType.2 hx EF EG)

/-- Oracle-free common lambda checking also preserves same-argument application.
Every computation node is replayed at the actual common Pi type. -/
theorem proofErase_rawChecked_apply_same
    (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.RawCheckedCompare Step mode (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  generalize Ef : proofErase Γ f = sf at H
  generalize Eg : proofErase Γ g = sg at H
  induction H generalizing f g A B with
  | base H => exact proofErase_compare_apply_same hstep hsubst hΓ hf hg hx (by rwa [Ef, Eg])
  | app Hf Hx =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .app Hf Hx))
  | proj H =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .proj H))
  | lam HD Hb =>
    exact proofErase_context_apply_lam_shapes hsubst hΓ hf hg hx Ef Eg (.base Hb.common)
  | lamCommon Hb =>
    exact proofErase_context_apply_lam_shapes hsubst hΓ hf hg hx Ef Eg (.base Hb)
  | forallE HD HB =>
    exact proofErase_context_apply_inferred hΓ hf hg hx (.base (by rw [Ef, Eg]; exact .forallE HD HB))
  | compute Rf Rg HC ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨f', HF, EF⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero, Ef] using Rf)
    obtain ⟨g', HG, EG⟩ := proofErase_compute_typed_descend hstep hΓ hΓ W hg
      (by simpa only [ProofShape.liftN_zero, Eg] using Rg)
    simp only [ProofShape.liftN_zero] at EF EG
    exact .compute
      (proofErase_compute_apply_same hΓ hf HF.hasType.2 hx (by rwa [Ef, EF]))
      (proofErase_compute_apply_same hΓ hg HG.hasType.2 hx (by rwa [Eg, EG]))
      (ih HF.hasType.2 HG.hasType.2 hx EF EG)

end Lean4Lean.VEnv.Strengthening
