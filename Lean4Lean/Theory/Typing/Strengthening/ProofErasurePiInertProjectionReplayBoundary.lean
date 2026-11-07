import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertReplayMinimum
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParameterBoxRegistration
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertReplayFailure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBoxFieldReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeStructureExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeaderBetaBoundary

/-! # Ordinary substitution can destroy projection-root replay

Let p and q inhabit a positive unit, and let Tag retain its unit parameter.
A fresh r : Box (Tag q) has a native projection of type Tag q, which expands
to the fieldless constructor at q. Substitute the box containing Tag p and
its constructor at p; unit equality makes this an ordinary typed substitution.
The substituted projection was typed before q was inserted. Descent therefore
forbids computation to the constructor retaining q, at any count or stage.

The box registration is constructed in an actual environment extension.
This obstructs blanket local replay, not strengthening or whole-tail readout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private BoxCarrierAlignment.projection_recipe BoxCarrierAlignment.family_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : Definitions}

/-- The fresh box's projection recovers its assigned type directly from the
context, even when the eventual box image has a different native parameter.
This supplies an actual Pi-inert structure root at stage one and its ordinary
one-binder substitution. No transport of that root is presumed. -/
theorem pi_inert_box_projection_structure_root
    (hi : env.projections box bi) (hp : bi.nparams = 1) (hf : bi.numFields = 1)
    (hz : bi.nindices = 0) (hadm : (bi.resultLevel.inst []).IsNeverZero)
    (hshape : bi.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const box []) (.bvar 1))))
    (hc : env.constants box = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hTag : env.projections tag (PositiveHeaderRegistration.info 0 [.const unit []] tag ctor))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort (.succ .zero)))
    (hx : env.HasType univs Γ x (.app (.const box []) A))
    (EA : proofErase Γ A = .app (.const tag []) q) :
    let B := proofErase Γ (.app (.const box []) A)
    let Δ := proofEraseCtx Γ
    let source := ProofShape.proj box 0 (.bvar 0)
    let target := ProofShape.app (.const ctor []) (q.liftN 1)
    TypedSource (B :: Δ) source ∧
      PiInertStage D 1 (B :: Δ) source target ∧
      ContextSubstitution (B :: Δ) Δ (ProofShape.Subst.one (proofErase Γ x)) := by
  let B := VExpr.app (.const box []) A
  have hB : env.HasType univs Γ B (.sort (.succ .zero)) := .app (BoxCarrierAlignment.family_typed hc) hA
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, _, hB⟩
  have hv : env.HasType univs (B :: Γ) (.bvar 0) B.lift := .bvar .zero
  have hn := not_proof_at_positive_type hΓB (hB.weak henv) hv
  have hproj : env.HasType univs (B :: Γ) (.proj box 0 (.bvar 0)) A.lift :=
    box_projection_typed hi hp hf hz hadm hshape hΓB hv
  have hnproj := not_proof_at_positive_type hΓB (hA.weak henv) hproj
  have EB : proofErase Γ B = .app (.const box []) (proofErase Γ A) := by
    rw [show proofErase Γ B = .app _ _ from if_neg (not_isProof_of_sort hΓ hB)]
    rw [show proofErase Γ (.const box []) = .const box [] from
      if_neg (not_isProof_function_to_sort hΓ (BoxCarrierAlignment.family_typed hc))]
  have RN := proofErase_scoped_lookup_recovery
    (Step := ErasedStaticStructureEtaExpansionStage D 0) hΓB
    (show Lookup (B :: Γ) 0 B.lift from .zero) hn .refl
  rw [show proofErase (B :: Γ) (.bvar 0) = .bvar 0 from if_neg hn,
    proofErase_liftN hΓ hΓB Ctx.LiftN.one hB, EB] at RN
  obtain ⟨doms, result, HT, hd⟩ := projection_expansion_telescope_exists (ls := []) hi (by simp)
  have hj : bi.nparams + 0 < doms.length := by omega
  have RP := ScopedTypeRecovery.proj hi HT hj (args := [(proofErase Γ A).liftN 1])
    (by simp [hp, hz]) RN
  rw [BoxCarrierAlignment.projection_recipe hp hf hshape HT hj] at RP
  have RP' : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx (B :: Γ)) (.proj box 0 (.bvar 0))
      (ProofShape.mkApps (.const tag []) [q.liftN 1]) := by
    simpa only [EA, ProofShape.liftN, ProofShape.mkApps, List.foldl_cons, List.foldl_nil] using RP
  have HR := NativeMaskedStructureExpansion.intro hTag rfl
    (Or.inl (show (PositiveHeaderRegistration.info 0 [.const unit []] tag ctor).resultLevel.inst [] |>.IsNeverZero from by
      intro v; simp [PositiveHeaderRegistration.info, VLevel.inst, VLevel.eval])) rfl RP'
  have ER : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx (B :: Γ)) (.proj box 0 (.bvar 0)) (.app (.const ctor []) (q.liftN 1)) := by
    simpa [nativeStructureOutput, PositiveHeaderRegistration.info, PositiveHeaderRegistration.constructor,
      VProjectionInfo.numFields, etaOpen, VExpr.forallArity, ProofShape.mkApps] using HR
  refine ⟨⟨B :: Γ, .proj box 0 (.bvar 0), _, hΓB, rfl, hproj, ?_⟩,
    ⟨.inr (.inr (.inr (.inr (.inr ER)))), .inl trivial⟩, ?_⟩
  · rw [show proofErase (B :: Γ) (.proj box 0 (.bvar 0)) = .proj box 0 _ from if_neg hnproj,
      show proofErase (B :: Γ) (.bvar 0) = .bvar 0 from if_neg hn]
  · exact ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓB hx)
      (erasedSubstAgreement_one hΓB hx)

/-- In an environment with the displayed registered unit, phantom family and
ordinary parameter box, one projection-headed structure root has no replay
after an actual typed binder consumption. The failure holds at every count
and for every descending computation language, including the full ambient
union under canonical Eq. This refutes blanket local transport under these
explicit registration hypotheses, not strengthening or whole-tail readout.
The actual typed consumption continuation and enclosing lambda application
both have global minimum count one across all finite stages. -/
theorem pi_inert_projection_structure_substitution_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections box bi) (hp : bi.nparams = 1) (hf : bi.numFields = 1)
    (hz : bi.nindices = 0) (hu : bi.uvars = 0) (hadm : (bi.resultLevel.inst []).IsNeverZero)
    (hshape : bi.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const box []) (.bvar 1))))
    (hc : env.constants box = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hiU : env.projections unit ui) (hpU : ui.nparams = 0)
    (hxU : ui.nindices = 0) (hfU : ui.numFields = 0)
    (hU : env.HasType univs [] (.const unit []) (.sort (.succ .zero)))
    (hTag : env.projections tag (PositiveHeaderRegistration.info 0 [.const unit []] tag ctor))
    (hF : env.HasType univs [] (.const tag [])
      (.forallE (.const unit []) (.sort (.succ .zero)))) :
    ∃ Δ A x source target, TypedSource (A :: Δ) source ∧
      ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) ∧
      ∃ HR : PiInertStage D 1 (A :: Δ) source target,
        PiInertCountedReplayFailure D 1 (.base HR) Δ (ProofShape.Subst.one x) ∧
        PiInertTypedContinuationMinimum D Δ (target.inst x) (A :: Δ) source 1 ∧
        TypedSource Δ (.app (.lam A source) x) ∧
        ScopedComputeCount (PiInertStage D 1) 1 Δ (.app (.lam A source) x) (target.inst x) ∧
        (∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
          (.app (.lam A source) x) (target.inst x) → 1 ≤ j) ∧
        ∀ Step, ErasedScopedPrimitiveDescent Step →
          ¬ ScopedCompute Step Δ (source.inst x) (target.inst x) := by
  let S := VExpr.const unit []
  let Γ₀ := [S]
  let Γ := [S, S]
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) := ⟨trivial, _, hU⟩
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΓ₀, _, hU.weak0 henv.ordered⟩
  have hP₀ : env.HasType univs Γ₀ (.bvar 0) S := .bvar .zero
  have hP : env.HasType univs Γ (.bvar 1) S := .bvar (.succ .zero)
  have hQ : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have hC : env.HasType univs [] (.const ctor [])
      (.forallE S (.app (.const tag []) (.bvar 0))) :=
    HasType.const (henv.ordered.projectionConstructor hTag) (ls := []) (by simp) rfl
  have hT₀ : env.HasType univs Γ₀ (.app (.const tag []) (.bvar 0)) (.sort (.succ .zero)) :=
    .app (hF.weak0 henv.ordered) hP₀
  have hTQ : env.HasType univs Γ (.app (.const tag []) (.bvar 0)) (.sort (.succ .zero)) :=
    .app (hF.weak0 henv.ordered) hQ
  have hE₀ : env.HasType univs Γ₀ (.app (.const ctor []) (.bvar 0))
      (.app (.const tag []) (.bvar 0)) := .app (hC.weak0 henv.ordered) hP₀
  let oldBox := VExpr.mkApps (.const bi.ctorName [])
    [.app (.const tag []) (.bvar 0), .app (.const ctor []) (.bvar 0)]
  have hBC := HasType.const (U := univs) (Γ := Γ₀)
    (henv.ordered.projectionConstructor hi) (ls := []) (by simp) (by simpa using hu.symm)
  rw [hshape] at hBC
  have hOld : env.HasType univs Γ₀ oldBox
      (.app (.const box []) (.app (.const tag []) (.bvar 0))) := by
    have HH := HasType.app (HasType.app hBC hT₀) hE₀
    simpa [oldBox, VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar, VExpr.mkApps] using HH
  have HPQ := IsDefEq.unitLike hiU (params := []) hpU.symm hxU hfU hP hQ
  have HT := IsDefEq.appDF (hF.weak0 henv.ordered) HPQ
  have HBox := IsDefEq.appDF (BoxCarrierAlignment.family_typed hc) HT
  have hx : env.HasType univs Γ oldBox.lift
      (.app (.const box []) (.app (.const tag []) (.bvar 0))) :=
    HBox.defeq (hOld.weak henv)
  have EQ : proofErase Γ (.bvar 0) = .bvar 0 :=
    if_neg (not_proof_at_positive_type hΓ (hU.weak0 henv.ordered) hQ)
  have EA : proofErase Γ (.app (.const tag []) (.bvar 0)) = .app (.const tag []) (.bvar 0) := by
    rw [show proofErase Γ (.app (.const tag []) (.bvar 0)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hTQ), EQ,
      show proofErase Γ (.const tag []) = .const tag [] from
        if_neg (not_isProof_function_to_sort hΓ (hF.weak0 henv.ordered))]
  obtain ⟨HS, HR, W⟩ := pi_inert_box_projection_structure_root
    (D := D) hi hp hf hz hadm hshape hc hTag hΓ hTQ hx EA
  have hProj := box_projection_typed hi hp hf hz hadm hshape hΓ₀ hOld
  have hProj' : env.HasType univs Γ ((VExpr.proj box 0 oldBox).lift)
      ((VExpr.app (.const tag []) (.bvar 0)).lift) := hProj.weak henv
  have EProj : proofErase Γ ((VExpr.proj box 0 oldBox).lift) =
      .proj box 0 (proofErase Γ oldBox.lift) :=
    if_neg (not_proof_at_positive_type hΓ (hT₀.weak henv) hProj')
  have Hno : ∀ Step, ErasedScopedPrimitiveDescent Step →
      ¬ ScopedCompute Step (proofEraseCtx Γ)
        ((ProofShape.proj box 0 (.bvar 0)).inst (proofErase Γ oldBox.lift))
        ((ProofShape.app (.const ctor []) ((ProofShape.bvar 0).liftN 1)).inst
          (proofErase Γ oldBox.lift)) := by
    intro Step hstep RC
    have R : ScopedCompute Step (proofEraseCtx Γ)
        (proofErase Γ ((VExpr.proj box 0 oldBox).lift)) (.app (.const ctor []) (.bvar 0)) := by
      rw [EProj]
      simpa [ProofShape.inst, ProofShape.liftN, liftVar, ProofShape.liftN_zero] using RC
    exact computed_source_no_inserted_argument hstep hΓ₀ hΓ Ctx.LiftN.one hProj
      (j := 0) (by omega) (by omega) R
  have HNP (later : Nat) := Hno (PiInertStage D later)
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs later))
  have Hminimum := (pi_inert_nonreplay_typed_continuation_minimum heq hs HS HR W HNP).2
  have hout : ∀ B b y,
      ((ProofShape.app (.const ctor []) ((ProofShape.bvar 0).liftN 1)).inst
        (proofErase Γ oldBox.lift)) ≠ .app (.lam B b) y := by
    intro B b y HE
    simp [ProofShape.inst, ProofShape.liftN, liftVar] at HE
  have Happlication := pi_inert_nonreplay_lambda_application_minimum HR HNP hout
  let B := VExpr.app (.const box []) (.app (.const tag []) (.bvar 0))
  have hB : env.HasType univs Γ B (.sort (.succ .zero)) :=
    .app (BoxCarrierAlignment.family_typed hc) hTQ
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, _, hB⟩
  have hv : env.HasType univs (B :: Γ) (.bvar 0) B.lift := .bvar .zero
  have hb : env.HasType univs (B :: Γ) (.proj box 0 (.bvar 0))
      ((VExpr.app (.const tag []) (.bvar 0)).lift) :=
    box_projection_typed hi hp hf hz hadm hshape hΓB hv
  have hL := HasType.lam hB hb
  have hApp : env.HasType univs Γ (.app (.lam B (.proj box 0 (.bvar 0))) oldBox.lift)
      (.app (.const tag []) (.bvar 0)) := by
    simpa only [VExpr.inst_lift] using HasType.app hL hx
  have hnApp := not_proof_at_positive_type hΓ hTQ hApp
  have hnL := not_isProof_fn hΓ hL hx hnApp
  have hnb := not_proof_at_positive_type hΓB (hTQ.weak henv) hb
  have hnv := not_proof_at_positive_type hΓB (hB.weak henv) hv
  have EApp : proofErase Γ (.app (.lam B (.proj box 0 (.bvar 0))) oldBox.lift) =
      .app (.lam (proofErase Γ B) (.proj box 0 (.bvar 0))) (proofErase Γ oldBox.lift) := by
    rw [show proofErase Γ (.app (.lam B (.proj box 0 (.bvar 0))) oldBox.lift) = .app _ _ from if_neg hnApp,
      show proofErase Γ (.lam B (.proj box 0 (.bvar 0))) = .lam _ _ from if_neg hnL,
      show proofErase (B :: Γ) (.proj box 0 (.bvar 0)) = .proj box 0 _ from if_neg hnb,
      show proofErase (B :: Γ) (.bvar 0) = .bvar 0 from if_neg hnv]
  refine ⟨_, _, _, _, _, HS, W, HR, .base HR HS W ?_, Hminimum,
    ⟨Γ, _, _, hΓ, rfl, hApp, EApp⟩, Happlication.1, Happlication.2, Hno⟩
  intro later j _ RJ
  apply Hno (PiInertStage D later)
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs later))
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RJ.forget

omit [Params] in
/-- Install the box in a real extension of an environment with canonical Eq,
a registered positive unit and the registered unit-parameter phantom family.
The resulting environment-core stage-one projection root has an interpreted
one-binder substitution and a certified local replay failure. In fact no
descending language can replay its substituted endpoints at any cost. Both
the typed consumption continuation and its typed enclosing lambda application
retain global minimum count one. Thus minimum count alone does not repair it. -/
theorem exists_registered_pi_inert_projection_replay_failure
    {base : VEnv} (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hiU : base.projections unit ui) (hpU : ui.nparams = 0)
    (hxU : ui.nindices = 0) (hfU : ui.numFields = 0)
    (hU : base.HasType 0 [] (.const unit []) (.sort (.succ .zero)))
    (hTag : base.projections tag (PositiveHeaderRegistration.info 0 [.const unit []] tag ctor))
    (hF : base.HasType 0 [] (.const tag [])
      (.forallE (.const unit []) (.sort (.succ .zero))))
    (hbox : base.constants box = none) (hbc : base.constants boxCtor = none)
    (hne : box ≠ boxCtor) :
    ∃ E : VEnv, ∃ hE : E.WF, base ≤ E ∧ E.HasCanonicalEq ∧
      (letI := hE.params 0
       ∃ Δ A x source target, TypedSource (A :: Δ) source ∧
         ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) ∧
         ∃ HR : PiInertStage EnvironmentCore.definitions 1 (A :: Δ) source target,
           PiInertCountedReplayFailure EnvironmentCore.definitions 1 (.base HR) Δ (ProofShape.Subst.one x) ∧
           PiInertTypedContinuationMinimum EnvironmentCore.definitions Δ (target.inst x) (A :: Δ) source 1 ∧
           TypedSource Δ (.app (.lam A source) x) ∧
           ScopedComputeCount (PiInertStage EnvironmentCore.definitions 1) 1 Δ
             (.app (.lam A source) x) (target.inst x) ∧
           (∀ later j, ScopedComputeCount (PiInertStage EnvironmentCore.definitions later) j Δ
             (.app (.lam A source) x) (target.inst x) → 1 ≤ j) ∧
           ∀ Step, ErasedScopedPrimitiveDescent Step →
             ¬ ScopedCompute Step Δ (source.inst x) (target.inst x)) := by
  obtain ⟨E, hE, hle, hi, hc⟩ := ParameterBoxRegistration.exists_extension hbase hbox hbc hne
  refine ⟨E, hE, hle, heq.mono hle, ?_⟩
  letI := hE.params 0
  exact pi_inert_projection_structure_substitution_failure (heq.mono hle) EnvironmentCore.sound
    hi rfl rfl rfl rfl (by intro v; simp [ParameterBoxRegistration.info, VLevel.inst, VLevel.eval])
    rfl hc (hle.projections hiU) hpU hxU hfU (hU.mono hle) (hle.projections hTag) (hF.mono hle)

end Lean4Lean.VEnv.Strengthening
