import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePiTelescopeReification

/-! # Restarting literal Pi histories after application

Keep the original family function's native guard, together with a computation
of its lambda telescope. Opening that computation on fresh variables supplies
the body history for a later Pi conversion. Native recovery of the computed
lambda is never assumed. Literal residual telescopes delimit each phase.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Function computations can be opened on a whole fresh dependent telescope.
The functions share a sort-ending assignment; no native certificate is needed
for either endpoint or any fresh argument. -/
theorem proofErase_static_structure_compute_etaOpen
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u)))
    (hg : env.HasType univs Γ g (VExpr.wrapForalls ds (.sort u)))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (ds.reverse ++ Γ))
      (proofErase (ds.reverse ++ Γ) (etaOpen ds.length f))
      (proofErase (ds.reverse ++ Γ) (etaOpen ds.length g)) := by
  induction ds generalizing Γ f g with
  | nil => exact R
  | cons A ds ih =>
    obtain ⟨⟨v, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    have hf' := hf.weak henv (B := A)
    have hg' := hg.weak henv (B := A)
    have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
    have hfa : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0))
        (VExpr.wrapForalls ds (.sort u)) := by
      simpa only [VExpr.lift, VExpr.inst_liftN_bvar, VExpr.wrapForalls] using HasType.app hf' hx
    have hga : env.HasType univs (A :: Γ) (.app g.lift (.bvar 0))
        (VExpr.wrapForalls ds (.sort u)) := by
      simpa only [VExpr.lift, VExpr.inst_liftN_bvar, VExpr.wrapForalls] using HasType.app hg' hx
    have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
        ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
      intro Δ Δ' a b τ ⟨stage, HR⟩ W
      exact ⟨stage, erased_static_structure_eta_expansion_stage_rename heq hs stage HR W⟩
    have RL := R.rename hrename (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
    simp only [subst_bvar_liftN] at RL
    rw [← proofErase_liftN hΓ hΓA Ctx.LiftN.one hf,
      ← proofErase_liftN hΓ hΓA Ctx.LiftN.one hg] at RL
    have RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) (.app f.lift (.bvar 0)))
        (proofErase (A :: Γ) (.app g.lift (.bvar 0))) := by
      rw [show proofErase (A :: Γ) (.app f.lift (.bvar 0)) = .app _ _ from
        if_neg (not_isProof_telescope_to_sort hΓA hfa),
        show proofErase (A :: Γ) (.app g.lift (.bvar 0)) = .app _ _ from
        if_neg (not_isProof_telescope_to_sort hΓA hga)]
      exact .app RL .refl
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      List.length_cons, etaOpen] using ih hΓA hfa hga RA

/-- A computation to a literal lambda telescope supplies a fresh generic-body
history, by opening the function path and contracting only those lambdas. -/
theorem proofErase_static_structure_open_computed_lambdas
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u)))
    (hb : env.HasType univs (ds.reverse ++ Γ) B (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ (VExpr.wrapLams ds B))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (ds.reverse ++ Γ))
      (proofErase (ds.reverse ++ Γ) (etaOpen ds.length f)) (proofErase (ds.reverse ++ Γ) B) := by
  have hctx := (hf.etaOpen_wf henv.ordered hΓ).1
  have hL := HasType.wrapLams_of hctx hb
  have RO := proofErase_static_structure_compute_etaOpen heq hs hΓ hf hL R
  exact RO.trans (.beta (proofErase_beta_forward hctx
    (hL.etaOpen_wf henv.ordered hΓ).2 (EtaTelescope.etaOpen_wrapLams_beta ds B)))

/-- A native family and its current literal type telescope. The retained
function path is not itself a native certificate for the computed lambda. -/
structure NativePiHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (f : VExpr) (u : VLevel) (ds : List VExpr) (B : VExpr) : Prop where
  typed : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u))
  native : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
    (proofErase Γ f) (proofErase Γ (VExpr.wrapForalls ds (.sort u)))
  body : env.HasType univs (ds.reverse ++ Γ) B (.sort u)
  path : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
    (proofErase Γ f) (proofErase Γ (VExpr.wrapLams ds B))

/-- An exact native family starts a history at its generic eta opening. -/
theorem NativePiHistory.initial
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds (.sort u)))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ (VExpr.wrapForalls ds (.sort u)))) :
    NativePiHistory D Γ f u ds (etaOpen ds.length f) :=
  ⟨hf, RF, (hf.etaOpen_wf henv.ordered hΓ).2,
    static_structure_native_eta_telescope heq hs hΓ hf (fun _ => RF)⟩

private theorem sort_headers_congr
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.IsType univs Γ (VExpr.wrapForalls ds (.sort u)))
    (hlen : ds.length = ds'.length)
    (HE : env.IsDefEqU univs Γ (VExpr.wrapForalls ds B) (VExpr.wrapForalls ds' B')) :
    env.IsDefEqU univs Γ (VExpr.wrapForalls ds (.sort u))
      (VExpr.wrapForalls ds' (.sort u)) := by
  induction ds generalizing Γ ds' with
  | nil =>
    have : ds' = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ds'
    exact hF.choose_spec.toU
  | cons A ds ih =>
    cases ds' with
    | nil => simp at hlen
    | cons A' ds' =>
      obtain ⟨⟨v, HA⟩, w, HB⟩ := HE.forallE_inv henv hΓ
      obtain ⟨_, hRest⟩ := IsType.forallE_inv henv.ordered hF
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, HA.hasType.1⟩
      have HR := ih hΓA hRest (Nat.succ.inj hlen) HB.toU
      exact ⟨_, IsDefEq.forallEDF HA (HR.of_l henv hΓA hRest.choose_spec)⟩

/-- A literal type-telescope conversion advances the history and preserves the
original family head. All changed domains and the new body are retained. -/
theorem NativePiHistory.convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativePiHistory D Γ f u ds B)
    (hlen : ds.length = ds'.length)
    (hT' : env.IsType univs Γ (VExpr.wrapForalls ds' B'))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.wrapForalls ds B)) (proofErase Γ (VExpr.wrapForalls ds' B'))) :
    NativePiHistory D Γ f u ds' B' := by
  have hctx := (H.typed.etaOpen_wf henv.ordered hΓ).1
  obtain ⟨v, hT⟩ := VExpr.wrapForalls_defeq hctx H.body
  obtain ⟨T, HT, ET⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT.hasType.1 rfl rfl R
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ HT.hasType.2 hT'.choose_spec ET).2
    (not_isProof_of_sort hΓ HT.hasType.2)
  have HE := HT.toU.trans henv hΓ (HN.defeq hΓ)
  have HF := sort_headers_congr hΓ (H.typed.isType henv hΓ) hlen HE
  have hf' := H.typed.defeqU_r henv hΓ HF
  have hctx' := (hf'.etaOpen_wf henv.ordered hΓ).1
  have RP := R
  rw [proofErase_wrapForalls_type hΓ hT'] at RP
  obtain ⟨RT, RB⟩ := static_structure_pi_telescope_components heq hs hΓ ⟨v, hT.hasType.1⟩
    (by simpa only [proofEraseDomains_length] using hlen) RP
  have RF := static_structure_native_computed_telescope_domains hΓ H.typed H.native RT
  have EF := proofErase_wrapForalls_type hΓ (hf'.isType henv hΓ)
  obtain ⟨_, hSort⟩ := (hf'.etaOpen_wf henv.ordered hΓ).2.isType henv hctx'
  rw [show proofErase (ds'.reverse ++ Γ) (.sort u) = .sort u from
    if_neg (not_isProof_of_sort hctx' hSort)] at EF
  rw [← EF] at RF
  have RO := proofErase_static_structure_open_computed_lambdas heq hs hΓ H.typed H.body H.path
  have RE := static_structure_native_eta_telescope heq hs hΓ H.typed (fun _ => H.native)
  have hη := H.typed.etaOpen_defeq henv hΓ
  rw [proofErase_wrapLams_nonproof hctx (not_isProof_telescope_to_sort hΓ hη.hasType.2)] at RE
  have RL := RE.trans (RT.wrapLams (proofEraseDomains_context ▸ (RO.trans RB)))
  obtain ⟨_, w, hB'⟩ := IsType.wrapForalls_inv henv hΓ hT'
  have hL' := HasType.wrapLams_of hctx' hB'
  rw [← proofErase_wrapLams_nonproof hctx' (not_isProof_telescope_to_sort hΓ hL')] at RL
  obtain ⟨L, HL, EL⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hf' rfl rfl RL
  obtain ⟨_, HNL⟩ := (proofErase_reflect hΓ HL.hasType.2 hL' EL).2
    (not_isProof_telescope_to_sort hΓ HL.hasType.2)
  have hL'u := ((HNL.defeq hΓ).of_l henv hΓ HL.hasType.2).hasType.2
  exact ⟨hf', RF, (hL'u.wrapLams_inv henv hΓ).2, RL⟩

/-- Supplying an ordinary argument preserves the history at the literal
instantiated residual telescope. The next conversion may run after this step;
no native certificate is requested for the supplied argument. -/
theorem NativePiHistory.apply
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativePiHistory D Γ f u (A :: ds) B)
    (hx : env.HasType univs Γ x A) :
    NativePiHistory D Γ (.app f x) u (VExpr.instDomains ds x 0) (B.inst x ds.length) := by
  have hctx := (H.typed.etaOpen_wf henv.ordered hΓ).1
  have hL := HasType.wrapLams_of hctx H.body
  have hf : env.HasType univs Γ (.app f x)
      (VExpr.wrapForalls (VExpr.instDomains ds x 0) (.sort u)) := by
    have HT := H.typed.app hx
    change env.HasType univs Γ (.app f x) ((VExpr.wrapForalls ds (.sort u)).inst x) at HT
    simpa only [VExpr.wrapForalls_inst, VExpr.inst] using HT
  have hLa : env.HasType univs Γ (.app (VExpr.wrapLams (A :: ds) B) x)
      (VExpr.wrapForalls (VExpr.instDomains ds x 0) (.sort u)) := by
    have HT := hL.app hx
    change env.HasType univs Γ (.app (VExpr.wrapLams (A :: ds) B) x)
      ((VExpr.wrapForalls ds (.sort u)).inst x) at HT
    simpa only [VExpr.wrapForalls_inst, VExpr.inst] using HT
  have RN := static_structure_exact_native_app hΓ H.typed hx (fun _ => H.native)
    (not_isProof_telescope_to_sort hΓ hf)
  change ScopedTypeRecovery _ _ _ (proofErase Γ ((VExpr.wrapForalls ds (.sort u)).inst x)) at RN
  simp only [VExpr.wrapForalls_inst, VExpr.inst] at RN
  have RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (proofErase Γ (.app (VExpr.wrapLams (A :: ds) B) x)) := by
    rw [show proofErase Γ (.app f x) = .app _ _ from
      if_neg (not_isProof_telescope_to_sort hΓ hf),
      show proofErase Γ (.app (VExpr.wrapLams (A :: ds) B) x) = .app _ _ from
      if_neg (not_isProof_telescope_to_sort hΓ hLa)]
    exact .app H.path .refl
  have hctxTail : OnCtx (ds.reverse ++ A :: Γ) (env.IsType univs) := by
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hctx
  have hBT : env.HasType univs (A :: Γ) (VExpr.wrapLams ds B) (VExpr.wrapForalls ds (.sort u)) :=
    HasType.wrapLams_of hctxTail (by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using H.body)
  have HE := IsDefEq.beta hBT hx
  have Rβ := proofErase_beta_forward hΓ HE.hasType.1 VExpr.BetaRed.beta
  simp only [VExpr.wrapLams_inst, VExpr.wrapForalls_inst, VExpr.inst, Nat.zero_add] at HE Rβ
  exact ⟨hf, RN, (HE.hasType.2.wrapLams_inv henv hΓ).2, RA.trans (.beta Rβ)⟩

/-- An independently computed actual argument is realized at its original
domain, then supplied to the history. The old family application computes to
this new head, so its ancestry is retained without native image evidence. -/
theorem NativePiHistory.apply_computed
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NativePiHistory D Γ f u (A :: ds) B)
    (hx : env.HasType univs Γ x A)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) image) :
    ∃ y, env.IsDefEq univs Γ x y A ∧ proofErase Γ y = image ∧
      NativePiHistory D Γ (.app f y) u (VExpr.instDomains ds y 0) (B.inst y ds.length) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f x)) (proofErase Γ (.app f y)) := by
  obtain ⟨y, HE, EY⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hx rfl rfl RX
  have HX := H.apply hΓ hx
  have HY := H.apply hΓ HE.hasType.2
  refine ⟨y, HE, EY, HY, ?_⟩
  rw [show proofErase Γ (.app f x) = .app _ _ from
    if_neg (not_isProof_telescope_to_sort hΓ HX.typed),
    show proofErase Γ (.app f y) = .app _ _ from
    if_neg (not_isProof_telescope_to_sort hΓ HY.typed), EY]
  exact .app .refl RX

/-- At the end of a literal history, its terminal type is reached from the
family application. No native evidence for that computed type is assumed. -/
theorem NativePiHistory.finish (H : NativePiHistory D Γ f u [] B) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ B) := H.path

/-- A finite selected-type history with literal residual telescope checkpoints.
Conversions may occur repeatedly before or after any argument. Each argument
may compute independently before it is supplied. This is an explicit class of
native histories, not a normal-form theorem for arbitrary native derivations. -/
inductive LiteralPiHistory (D : PureObservation.Definitions) (Γ : List VExpr) :
    List VExpr → VExpr → List VExpr → List ProofShape → ProofShape → Prop where
  | done : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ B) out → LiteralPiHistory D Γ [] B [] [] out
  | convert : ds.length = ds'.length → env.IsType univs Γ (VExpr.wrapForalls ds' B') →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls ds B)) (proofErase Γ (VExpr.wrapForalls ds' B')) →
      LiteralPiHistory D Γ ds' B' args images out →
      LiteralPiHistory D Γ ds B args images out
  | app : env.HasType univs Γ x A → env.HasType univs Γ y A →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ x) (proofErase Γ y) →
      LiteralPiHistory D Γ (VExpr.instDomains ds y 0) (B.inst y ds.length) args images out →
      LiteralPiHistory D Γ (A :: ds) B (x :: args) (proofErase Γ y :: images) out

/-- Every explicit literal history is an actual native recovery of the supplied
head. The argument computations label its images but are not native premises. -/
theorem LiteralPiHistory.recovery
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : LiteralPiHistory D Γ ds B args images out)
    (hT : env.IsType univs Γ (VExpr.wrapForalls ds B))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) f
      (proofErase Γ (VExpr.wrapForalls ds B))) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps f images) out := by
  induction H generalizing f with
  | done R => exact RN.convert R
  | convert _ hT' R _ ih => exact ih hT' (RN.convert R)
  | @app x A y ds args images out B hx hy RX H ih =>
    obtain ⟨u, hT⟩ := hT
    obtain ⟨⟨v, hA⟩, w, hRest⟩ := hT.forallE_inv henv
    change env.HasType univs (A :: Γ) (VExpr.wrapForalls ds B) (.sort w) at hRest
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    rw [show proofErase Γ (VExpr.wrapForalls (A :: ds) B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hT)] at RN
    have RA := ScopedTypeRecovery.app (a := proofErase Γ y) RN
    change ScopedTypeRecovery _ _ _ ((proofErase (A :: Γ) (VExpr.wrapForalls ds B)).inst
      (proofErase Γ y)) at RA
    rw [← proofErase_instN hΓA hy Ctx.InstN.zero hRest, VExpr.wrapForalls_inst, Nat.zero_add] at RA
    have hI := hRest.instN henv.ordered Ctx.InstN.zero hy
    rw [VExpr.wrapForalls_inst, Nat.zero_add] at hI
    exact ih ⟨w, hI⟩ RA

/-- Arbitrarily many literal conversion/application phases retain the original
family application as a computation ancestor of the final selected type. All
argument images may compute; no argument has a native premise. -/
theorem LiteralPiHistory.family_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (W : LiteralPiHistory D Γ ds B args images out)
    (H : NativePiHistory D Γ f u ds B) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (proofErase Γ f) (args.map (proofErase Γ))) out := by
  induction W generalizing f with
  | done R => exact H.finish.trans R
  | convert hlen hT' R _ ih => exact ih (H.convert heq hs hΓ hlen hT' R)
  | @app x A y ds args images out B hx hy RX W ih =>
    have HY := H.apply hΓ hy
    have RI := ih HY
    rw [show proofErase Γ (.app f y) = .app _ _ from
      if_neg (not_isProof_telescope_to_sort hΓ HY.typed)] at RI
    exact (ScopedCompute.mkApps (.app .refl RX)
      (List.Forall₂.rfl (fun _ _ => .refl))).trans RI

/-- The same finite-history conclusion has the actual typed family application
as its source when its supplied spine is known to be a type. -/
theorem LiteralPiHistory.typed_family_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (W : LiteralPiHistory D Γ ds B args images out)
    (H : NativePiHistory D Γ f u ds B)
    (ht : env.HasType univs Γ (VExpr.mkApps f args) (.sort v)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps f args)) out := by
  rw [proofErase_mkApps hΓ ht (not_isProof_of_sort hΓ ht)]
  exact W.family_origin heq hs hΓ H

end Lean4Lean.VEnv.Strengthening
