import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMixedFamilyObservation

/-! # Exact native results across parameters followed by ignored fields

Parameter and field histories are retained together, so supplying parameters
never requires a literal residual field telescope. The final selected native
result computes from the family applied to the original parameter values.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private spine_head_type spine_function_eq
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveNativePiSupply
open private wrap_append
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursivePiObservation
variable [Params] {D : PureObservation.Definitions}

/-- Follow a selected native type history through every parameter and field.
The family consumes only parameters; the term consumes both. Ordinary typing
validates each selected domain and each independently computed argument image.
Conversions may occur before, between, and after applications. -/
theorem MixedFamilyPiObservation.supply_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : MixedFamilyPiObservation D Γ g u fields.length args.length [] (proofErase Γ T))
    (hf : env.HasType univs Γ f T)
    (ht : env.HasType univs Γ (VExpr.mkApps f (args ++ fields)) S)
    (hg : env.HasType univs Γ (VExpr.mkApps g args) (.sort v))
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RY : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages)
    (W : SelectedPiSupply (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ T) (images ++ fieldImages) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps g args)) out := by
  induction args generalizing g f T images with
  | nil =>
    cases RX
    exact H.finish_parameters.supply_history heq hs hΓ hf ht RY W
  | cons x args ih =>
    change env.HasType univs Γ (VExpr.mkApps (.app f x) (args ++ fields)) S at ht
    change env.HasType univs Γ (VExpr.mkApps (.app g x) args) (.sort v) at hg
    cases RX with
    | cons RImage RImages =>
      cases W with
      | @app _ rawA rawB image images _ RPi W =>
        obtain ⟨A, B, hA, hB, EA, EB, HBody⟩ :=
          (MixedFamilyPiObservation.compute (pending := []) heq hs hΓ hΓ H RPi).selected_pi
        simp only [List.reverse_nil, List.nil_append] at hA hB EA EB HBody
        obtain ⟨ds, C, _, HF⟩ := HBody.witness
        have hgPi : env.HasType univs Γ g (.forallE A (VExpr.wrapForalls ds (.sort u))) := HF.typed
        have hT := hf.isType henv hΓ
        obtain ⟨T', HT', ET'⟩ := proofErase_scoped_compute_realize
          (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hT.choose_spec rfl rfl RPi
        have hPi := HasType.forallE hA.choose_spec hB.choose_spec
        have EPi : proofErase Γ (.forallE A B) = .forallE rawA rawB := by
          rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
            if_neg (not_isProof_of_sort hΓ hPi), EA, EB]
        obtain ⟨_, HN⟩ := (proofErase_reflect hΓ HT'.hasType.2 hPi (ET'.trans EPi.symm)).2
          (not_isProof_of_sort hΓ HT'.hasType.2)
        have HE := HT'.toU.trans henv hΓ (HN.defeq hΓ)
        have hf' := hf.defeqU_r henv hΓ HE
        obtain ⟨V, hApp⟩ := spine_head_type (f := .app g x) hΓ hg
        obtain ⟨A₀, B₀, hg₀, hx₀⟩ := hApp.app_inv henv hΓ
        obtain ⟨⟨q, HA⟩, _⟩ := (hg₀.uniqU henv hΓ hgPi).forallE_inv henv hΓ
        have hx := HA.defeq hx₀
        obtain ⟨y, HXY, EY⟩ := proofErase_scoped_compute_realize
          (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hx rfl rfl RImage
        have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
        have HS := MixedFamilyPiObservation.supply (pending := []) hΓ hΓA HXY.hasType.2 HBody
        have EInst : proofErase Γ (B.inst y) = rawB.inst (proofErase Γ y) := by
          rw [proofErase_instN hΓA HXY.hasType.2 Ctx.InstN.zero hB.choose_spec, EB]
        have HEApp := IsDefEq.appDF hf' HXY
        have HEApps := spine_function_eq hΓ HEApp.toU ht
        have ht' := (HEApps.of_l henv hΓ ht).hasType.2
        have HEg := IsDefEq.appDF hgPi HXY
        have HEgs := spine_function_eq hΓ HEg.toU hg
        have hg' := (HEgs.of_l henv hΓ hg).hasType.2
        have RT := ih (T := B.inst y) (by rw [EInst]; exact HS)
          (hf'.app HXY.hasType.2) ht' hg' RImages (by rwa [EInst, EY])
        have HX := HF.apply hΓ hx
        have HY := HF.apply hΓ HXY.hasType.2
        have RH : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
            (proofErase Γ (.app g x)) (proofErase Γ (.app g y)) := by
          rw [show proofErase Γ (.app g x) = .app _ _ from
            if_neg (not_isProof_telescope_to_sort hΓ HX.typed),
            show proofErase Γ (.app g y) = .app _ _ from
            if_neg (not_isProof_telescope_to_sort hΓ HY.typed), EY]
          exact .app .refl RImage
        have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
            (proofErase Γ (VExpr.mkApps (.app g x) args))
            (proofErase Γ (VExpr.mkApps (.app g y) args)) := by
          rw [proofErase_mkApps hΓ hg (not_isProof_of_sort hΓ hg),
            proofErase_mkApps hΓ hg' (not_isProof_of_sort hΓ hg')]
          exact RH.mkApps (List.Forall₂.rfl (fun _ _ => .refl))
        exact RP.trans RT

/-- A fixed declaration-type origin and a retained native family suffice for
exact selected-output ancestry across arbitrary parameter and field histories.
The result body may depend on parameters but ignores the dependent field suffix. -/
theorem NativeFamilyPiHistory.mixed_native_spine_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HF : NativeFamilyPiHistory D Γ g u ps B)
    (hf : env.HasType univs Γ f
      (VExpr.wrapForalls ps (VExpr.wrapForalls fs (B.liftN fs.length))))
    (hp : ps.length = args.length) (hfields : fs.length = fields.length)
    (ht : env.HasType univs Γ (VExpr.mkApps f (args ++ fields)) S)
    (hg : env.HasType univs Γ (VExpr.mkApps g args) (.sort v))
    (HN : ∀ {T}, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) rawF T →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.wrapForalls ps (VExpr.wrapForalls fs (B.liftN fs.length)))) T)
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RY : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps rawF (images ++ fieldImages)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps g args)) out := by
  obtain ⟨hps, v, hfs⟩ := IsType.wrapForalls_inv henv hΓ (hf.isType henv hΓ)
  have hctx := (IsType.wrapForalls_inv henv hps ⟨v, hfs⟩).1
  have HO := MixedFamilyPiObservation.of_history (pending := []) heq hs hΓ HF hctx
  have HO' : MixedFamilyPiObservation D Γ g u fields.length args.length []
      (proofErase Γ (VExpr.wrapForalls ps (VExpr.wrapForalls fs (B.liftN fs.length)))) := by
    simpa only [hp, hfields, List.reverse_nil, List.nil_append] using HO
  obtain ⟨T, RF, W⟩ := RN.selected_supply
  exact HO'.supply_history heq hs hΓ hf ht hg RX RY (W.precompute (HN RF))

/-- Paired literal constant declarations discharge both native-origin premises
for an arbitrary parameter telescope followed by dependent fields. Field types
may depend on all preceding arguments; the family result depends only on the
parameters. Every selected conversion and computed argument image is retained. -/
theorem static_structure_declared_mixed_constructor_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants ctor = some ci) (hwc : ∀ l ∈ cls, l.WF univs)
    (hlc : cls.length = ci.uvars)
    (hf : env.constants family = some fi) (hwf : ∀ l ∈ fls, l.WF univs)
    (hlf : fls.length = fi.uvars)
    (HTf : fi.type.instL fls = VExpr.wrapForalls ps (.sort u))
    (HTc : ci.type.instL cls = VExpr.wrapForalls ps
      (VExpr.wrapForalls fs ((etaOpen ps.length (.const family fls)).liftN fs.length)))
    (HA : TelInst env univs Γ ps args)
    (HC : TelInst env univs Γ (ps ++ fs) (args ++ fields))
    (RX : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) images)
    (RY : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ))
      (fields.map (proofErase Γ)) fieldImages)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ctor cls) (images ++ fieldImages)) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const family fls) args)) out := by
  have hft : env.HasType univs Γ (.const family fls) (VExpr.wrapForalls ps (.sort u)) :=
    HTf ▸ HasType.const hf hwf hlf
  have EF : proofErase Γ (.const family fls) = .const family fls :=
    if_neg (not_isProof_telescope_to_sort hΓ hft)
  have hfc : env.HasType univs [] (.const family fls) (fi.type.instL fls) := .const hf hwf hlf
  obtain ⟨_, hfT⟩ := hfc.isType henv (by trivial)
  have Eft := proofErase_closed_context ((henv.ordered.closedC hf).instL) hfT hΓ
  have RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.const family fls)) (proofErase Γ (VExpr.wrapForalls ps (.sort u))) := by
    rw [EF, ← HTf, Eft]
    exact .const hf hwf hlf
  have H := NativeFamilyPiHistory.initial heq hs hΓ hft RF
  have hct : env.HasType univs [] (.const ctor cls) (ci.type.instL cls) := .const hc hwc hlc
  obtain ⟨_, hcT⟩ := hct.isType henv (by trivial)
  have Ect := proofErase_closed_context ((henv.ordered.closedC hc).instL) hcT hΓ
  have hctor : env.HasType univs Γ (.const ctor cls) (VExpr.wrapForalls ps
      (VExpr.wrapForalls fs ((etaOpen ps.length (.const family fls)).liftN fs.length))) :=
    HTc ▸ HasType.const hc hwc hlc
  have ht := HasType.mkApps_of_tel (show env.HasType univs Γ (.const ctor cls)
    (VExpr.wrapForalls (ps ++ fs) ((etaOpen ps.length (.const family fls)).liftN fs.length)) from
    by simpa only [wrap_append] using hctor) HC
  have hg : env.HasType univs Γ (VExpr.mkApps (.const family fls) args) (.sort u) := by
    simpa only [VExpr.instOuter_sort] using HasType.mkApps_of_tel hft HA
  have hp := HA.1
  have htotal := HC.1
  have hfields : fs.length = fields.length := by simp only [List.length_append] at htotal; omega
  apply H.mixed_native_spine_origin heq hs hΓ hctor hp.symm hfields ht hg ?_ RX RY RN
  intro T RT
  have RC := RT.const_compute hc
  rwa [← Ect, HTc] at RC

end Lean4Lean.VEnv.Strengthening
