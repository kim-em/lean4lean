import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedEtaApplication

/-! # Common application reduced to paired body instantiation

The missing law substitutes independently compared arguments into two bodies
that already compare at a common type. Assuming precisely that law, every
constructor of scoped comparison supports common function application. This is
an explicit open obligation, not a proved smaller strengthening front.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private function_not_constructor from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedApplication
variable [Params]

/-- Missing common-mode paired instantiation. Both bodies have one type in the
same well-formed binder context, and both arguments have its declared domain.
Their input comparisons need not have literal computational joins. This property
is not proved here or claimed strictly smaller than PropositionFront. Its
beta-only instance is refuted in `ProofErasureScopedLoopBoundary`, and its full
ordinary-core instance in `ProofErasureScopedCorePairedBoundary`. The latter
obstruction is repaired by a contextual K-prefix stage; coverage of installed
equations alone is insufficient. Higher-stage or stage-increasing instances
remain open. -/
def ScopedPairedInstantiation (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ A b b' B x y}, OnCtx (A :: Γ) (env.IsType univs) →
    env.HasType univs (A :: Γ) b B → env.HasType univs (A :: Γ) b' B →
    env.HasType univs Γ x A → env.HasType univs Γ y A →
    ProofShape.ScopedCompare Step (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) b') →
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y) →
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y))

private theorem apply_lams (hinst : ScopedPairedInstantiation Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam D b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam D' b') (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx (D :: Γ)) true
      (proofErase (D :: Γ) b) (proofErase (D' :: Γ) b'))
    (HX : ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app (.lam D b) x)) (proofErase Γ (.app (.lam D' b') y)) := by
  obtain ⟨⟨u, hD⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨_, hD'⟩, C', hb'⟩ := hg.lam_inv henv hΓ
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have hPi := (hf.uniqU henv hΓ (HasType.lam hD hb)).symm.trans henv hΓ
    (hg.uniqU henv hΓ (HasType.lam hD' hb'))
  obtain ⟨⟨_, HDD⟩, _, HCC⟩ := hPi.forallE_inv henv hΓ
  have hctx := IsDefEqCtx.succ .zero HDD.symm
  have Eb := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hb'
  rw [Eb] at H
  have hxD := argument_at_displayed_domain hΓ hf (HasType.lam hD hb) hx
  have hyD := argument_at_displayed_domain hΓ hf (HasType.lam hD hb) hy
  have hbD : env.HasType univs (D :: Γ) b' C' := hb'.defeqDFC henv hctx
  have hb'' := hbD.defeqU_r henv hΓD ⟨_, HCC.symm⟩
  exact .compute (.beta (proofErase_beta_forward hΓ (HasType.app hf hx) .beta))
    (.beta (proofErase_beta_forward hΓ (HasType.app hg hy) .beta))
    (hinst hΓD hb hb'' hxD hyD H HX)

private theorem apply_lam_shapes (hinst : ScopedPairedInstantiation Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (Ef : proofErase Γ f = .lam D b) (Eg : proofErase Γ g = .lam D' b')
    (H : ProofShape.ScopedCompare Step (D :: proofEraseCtx Γ) true b b')
    (HX : ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  obtain ⟨_, _, rfl, _, rfl, rfl⟩ := erase_lam_inv Ef
  obtain ⟨_, _, rfl, _, rfl, rfl⟩ := erase_lam_inv Eg
  exact apply_lams hinst hΓ hf hg hx hy H HX

private theorem apply_eta_shape (hinst : ScopedPairedInstantiation Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (Ef : proofErase Γ f = .lam D b)
    (SD : ProofShape.DomainSort (proofEraseCtx Γ) D u)
    (H : ProofShape.ScopedCompare Step (D :: proofEraseCtx Γ) true b
      (.app ((proofErase Γ g).liftN 1) (ProofShape.etaArgument u)))
    (HX : ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  obtain ⟨D₀, b₀, rfl, hn, ED, Eb⟩ := erase_lam_inv Ef
  obtain ⟨⟨_, hD₀⟩, C, hb⟩ := hf.lam_inv henv hΓ
  have W : Ctx.LiftN 0 0 Γ Γ := .zero []
  have hD := ProofShape.DomainSort.descend
    (by simpa only [ProofShape.liftN_zero, ED] using SD) hΓ hΓ W hD₀
  have hfPi := HasType.lam hD hb
  have hgPi := hg.defeqU_r henv hΓ (hf.uniqU henv hΓ hfPi)
  have hxD := argument_at_displayed_domain hΓ hf hfPi hx
  have hyD := argument_at_displayed_domain hΓ hf hfPi hy
  have hng : ¬ IsProof Γ g := fun hp => hn (isProof_of_common_type hΓ hg hf hp)
  have Eη := proofErase_eta_body hΓ hD hgPi hng
  have hη : env.HasType univs (D₀ :: Γ) (.app g.lift (.bvar 0)) C := by
    simpa only [lift, liftN, inst_liftN_bvar] using HasType.app (hgPi.weak henv) (.bvar .zero)
  have HC := hinst ⟨hΓ, _, hD⟩ hb hη hxD hyD
    (by simpa only [proofEraseCtx, ED, Eb, Eη] using H) HX
  simp only [inst, instVar_zero, inst_lift] at HC
  exact .compute (.beta (proofErase_beta_forward hΓ (HasType.app hf hx) .beta)) .refl HC

/-- Common application for all scoped certificates follows from paired
instantiation alone, in addition to primitive descent. Inferred cases and
literal eta need no paired law; the law is used only for compared lambda and
recursive eta bodies. No comparison transitivity is assumed. -/
theorem proofErase_scoped_apply_of_paired_inst
    (hstep : ErasedScopedPrimitiveDescent Step) (hinst : ScopedPairedInstantiation Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ f) (proofErase Γ g))
    (HX : ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ x) (proofErase Γ y)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) := by
  generalize EΔ : proofEraseCtx Γ = Δ at H
  generalize Ef : proofErase Γ f = sf at H
  generalize Eg : proofErase Γ g = sg at H
  induction H generalizing f g A B x y with
  | leaf H =>
    cases H with
    | refl =>
      rw [← EΔ]
      exact proofErase_scoped_apply_independent hstep hΓ hf hg hx hy
        (by rw [Ef, Eg]; exact .refl) HX
    | sort H =>
      rw [← EΔ]
      exact proofErase_scoped_apply_independent hstep hΓ hf hg hx hy
        (by rw [Ef, Eg]; exact .leaf (.sort H)) HX
    | const H =>
      rw [← EΔ]
      exact proofErase_scoped_apply_independent hstep hΓ hf hg hx hy
        (by rw [Ef, Eg]; exact .leaf (.const H)) HX
    | etaL H =>
      rw [← EΔ]
      exact proofErase_scoped_apply_eta_independent hstep hΓ hf hg hx hy (by rwa [Ef, Eg]) HX
    | etaR H =>
      rw [← EΔ]
      exact .symm (proofErase_scoped_apply_eta_independent hstep hΓ hg hf hy hx
        (by rwa [Ef, Eg]) HX.symm)
  | app Hf Hx =>
    rw [← EΔ]
    exact proofErase_scoped_apply_independent hstep hΓ hf hg hx hy
      (by rw [EΔ, Ef, Eg]; exact .app Hf Hx) HX
  | proj H =>
    rw [← EΔ]
    exact proofErase_scoped_apply_independent hstep hΓ hf hg hx hy
      (by rw [EΔ, Ef, Eg]; exact .proj H) HX
  | lam HD Hb =>
    rw [← EΔ]
    exact apply_lam_shapes hinst hΓ hf hg hx hy Ef Eg (by rw [EΔ]; exact Hb.common) HX
  | forallE HD HB =>
    rw [← EΔ]
    exact proofErase_scoped_apply_independent hstep hΓ hf hg hx hy
      (by rw [EΔ, Ef, Eg]; exact .forallE HD HB) HX
  | lamSorted SD SD' HD Hb =>
    rw [← EΔ]
    exact apply_lam_shapes hinst hΓ hf hg hx hy Ef Eg (by rw [EΔ]; exact Hb.common) HX
  | forallSorted SD SD' HD SB SB' HB =>
    rw [← EΔ]
    exact proofErase_scoped_apply_independent hstep hΓ hf hg hx hy
      (by rw [EΔ, Ef, Eg]; exact .forallSorted SD SD' HD SB SB' HB) HX
  | lamCommon Hb =>
    rw [← EΔ]
    exact apply_lam_shapes hinst hΓ hf hg hx hy Ef Eg (by rw [EΔ]; exact Hb) HX
  | etaBodyL SD Hb =>
    rw [← EΔ]
    exact apply_eta_shape hinst hΓ hf hg hx hy Ef (by rwa [EΔ]) (by rwa [EΔ, Eg]) HX
  | etaBodyR SD Hb =>
    rw [← EΔ]
    exact .symm (apply_eta_shape hinst hΓ hg hf hy hx Eg
      (by rwa [EΔ]) (by rw [EΔ, Ef]; exact .symm Hb) HX.symm)
  | structFields hi hindices hp hfields _ _ =>
    exact (function_not_constructor hΓ hf hi hindices hp hfields Ef).elim
  | etaLams HD H =>
    rw [← EΔ]
    exact proofErase_scoped_apply_independent hstep hΓ hf hg hx hy
      (by rw [EΔ, Ef, Eg]; exact .etaLams HD H) HX
  | compute Rf Rg HC ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨f', HF, EF⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hf EΔ
      (by simpa only [ProofShape.liftN_zero, Ef] using Rf)
    obtain ⟨g', HG, EG⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hg EΔ
      (by simpa only [ProofShape.liftN_zero, Eg] using Rg)
    simp only [ProofShape.liftN_zero] at EF EG
    exact .compute
      (proofErase_scoped_compute_apply_same hΓ hf HF.hasType.2 hx (by rwa [Ef, EF]))
      (proofErase_scoped_compute_apply_same hΓ hg HG.hasType.2 hy (by rwa [Eg, EG]))
      (ih HF.hasType.2 HG.hasType.2 hx hy HX EΔ EF EG)
  | symm H ih => exact .symm (ih hg hf hy hx HX.symm EΔ Eg Ef)

end Lean4Lean.VEnv.Strengthening
