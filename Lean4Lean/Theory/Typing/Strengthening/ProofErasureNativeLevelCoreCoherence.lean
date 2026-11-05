import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpineEtaDiamond
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreNativeReduction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureUniverseJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSpineRoot

/-! # Coherence of native recovery over the universe-extended core

Native recovery can choose different intermediate types. Its outputs at the
same typed expression nevertheless join when its conversion paths join in the
ordinary universe-extended core. Dependent projection recipes must follow both
parameter computation and changes of universe instance.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private LevelCoreNative.projection_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreNativeReduction
variable [Params] {D : Definitions}

private theorem lam_origin (R : ScopedTypeRecovery Step Δ (.lam A b) out) :
    ∃ B, ScopedTypeRecovery Step (A :: Δ) b B ∧
      ScopedCompute Step Δ (.forallE A B) out := by
  generalize E : ProofShape.lam A b = e at R
  induction R with
  | lam R => cases E; exact ⟨_, R, .refl⟩
  | convert _ RC ih =>
    obtain ⟨B, R, RB⟩ := ih E
    exact ⟨B, R, RB.trans RC⟩
  | bvar | sort | const | app | forallE | proj => cases E

private theorem pi_origin (R : ScopedTypeRecovery Step Δ (.forallE A B) out) :
    ∃ u v, ScopedTypeRecovery Step Δ A (.sort u) ∧
      ScopedTypeRecovery Step (A :: Δ) B (.sort v) ∧
      ScopedCompute Step Δ (.sort (.imax u v)) out := by
  generalize E : ProofShape.forallE A B = e at R
  induction R with
  | forallE RA RB => cases E; exact ⟨_, _, RA, RB, .refl⟩
  | convert _ RC ih =>
    obtain ⟨u, v, RA, RB, R⟩ := ih E
    exact ⟨u, v, RA, RB, R.trans RC⟩
  | bvar | sort | const | app | lam | proj => cases E

private theorem proj_origin (R : ScopedTypeRecovery Step Δ (.proj s j m) out) :
    ∃ (info : VProjectionInfo), ∃ ls, ∃ (doms : List VExpr), ∃ result, ∃ (hj : info.nparams + j < doms.length), ∃ args,
      env.projections s info ∧ ProjTele env univs s info ls doms result ∧
      args.length = info.nparams + info.nindices ∧
      ScopedTypeRecovery Step Δ m (ProofShape.mkApps (.const s ls) args) ∧
      ScopedCompute Step Δ (projectionType s info doms j hj args m) out := by
  generalize E : ProofShape.proj s j m = e at R
  induction R with
  | proj hi HT hj hl RN => cases E; exact ⟨_, _, _, _, hj, _, hi, HT, hl, RN, .refl⟩
  | convert _ RC ih =>
    obtain ⟨i, ls, ds, r, hj, args, hi, HT, hl, RN, R⟩ := ih E
    exact ⟨i, ls, ds, r, hj, args, hi, HT, hl, RN, R.trans RC⟩
  | bvar | sort | const | app | lam | forallE => cases E

private theorem native_join_convert
    (hld : ErasedScopedPrimitiveDescent Left) (hrd : ErasedScopedPrimitiveDescent Right)
    (hc : TypedCoreConfluence Core)
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : ScopedTypeRecovery Left (proofEraseCtx Γ) (proofErase Γ e) A)
    (RR : ScopedTypeRecovery Right (proofEraseCtx Γ) (proofErase Γ e) B)
    (HJ : ComputeJoin Core A B)
    (RA : ScopedCompute Left (proofEraseCtx Γ) A A')
    (RB : ScopedCompute Right (proofEraseCtx Γ) B B') : ComputeJoin Core A' B' := by
  obtain ⟨CL, htL, EL⟩ := proofErase_scoped_typeRecovery_replay hld hΓ he RL
  obtain ⟨CR, htR, ER⟩ := proofErase_scoped_typeRecovery_replay hrd hΓ he RR
  obtain ⟨_, hCL⟩ := htL.isType henv hΓ
  obtain ⟨_, hCR⟩ := htR.isType henv hΓ
  rw [← EL, ← ER] at HJ
  exact ((hlj hΓ hCL (EL ▸ RA)).symm.trans_typed hc hΓ hCL HJ).trans_typed
    hc hΓ hCR (hrj hΓ hCR (ER ▸ RB))

private theorem family_path_origin
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs) (hi : env.projections s info)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (ET : proofErase Γ T = ProofShape.mkApps (.const s ls) args)
    (R : Compute (ErasedLevelCore D) (ProofShape.mkApps (.const s ls) args) out) :
    ∃ ls' args' mid, out = ProofShape.mkApps (.const s ls') args' ∧
      List.Forall₂ (Compute (ErasedIotaPrimitive D)) args mid ∧
      List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ StructuralVariant mid args' := by
  obtain ⟨mid, RC, VC⟩ := proofErase_level_core_factor hs hlevels hcon R hΓ hT ET
  obtain ⟨args₀, rfl, HA⟩ := (RC.scoped (Δ := []) (fun H => .base H)).const_spine
    (fun H => erased_iota_primitive_no_rigid (henv.projectionRigid hi) hD H
      (ProofShape.constHead_mkApps _ _))
  obtain ⟨ls', args', E, HL, HP⟩ := VC.constant_spine
  exact ⟨ls', args', args₀, E, HA.imp (fun _ _ H => H.core_forget), HL, HP⟩

/-- A native projection recipe follows a level-core computation of its family.
The chosen constructor telescope and universe instance may change; all dependent
parameter and preceding-field captures are retained. -/
theorem proofErase_native_projection_level_core_path
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ levels rhs, ¬ D.unfolds s levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ (.proj s j m) T)
    (hi : env.projections s info)
    (HT : ProjTele env univs s info ls doms result)
    (HT' : ProjTele env univs s info ls' doms' result')
    (hj : info.nparams + j < doms.length) (hj' : info.nparams + j < doms'.length)
    (hl : args.length = info.nparams + info.nindices)
    (RN : ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ)
      (proofErase Γ m) (ProofShape.mkApps (.const s ls) args))
    (R : Compute (ErasedLevelCore D) (ProofShape.mkApps (.const s ls) args)
      (ProofShape.mkApps (.const s ls') args'))
    (hn : ¬ IsProof Γ (.proj s j m)) :
    Compute (ErasedLevelCore D) (projectionType s info doms j hj args (proofErase Γ m))
      (projectionType s info doms' j hj' args' (proofErase Γ m)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
  have hd : ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore D) := erased_level_core_descent hs
  obtain ⟨F, hmF, EF⟩ := proofErase_scoped_typeRecovery_replay hd hΓ hm.hasType.2 RN
  obtain ⟨_, hF⟩ := hmF.isType henv hΓ
  obtain ⟨levels, args₁, mid, E, HA, HL, HP⟩ := family_path_origin hs hlevels hcon hD hi hΓ hF EF R
  obtain ⟨_, rfl, rfl⟩ := ProofShape.const_spine_inj E
  have RN' := RN.convert (R.scoped (fun H => .base H))
  obtain ⟨hw, hw', _, _⟩ := proofErase_native_structure_family_universes hd hd hΓ hm.hasType.2 hi RN RN'
  have hl' : args'.length = info.nparams + info.nindices :=
    HP.length_eq.symm.trans (HA.length_eq.symm.trans hl)
  have RP : ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ)
      (proofErase Γ (.proj s j m)) (projectionType s info doms' j hj' args' (proofErase Γ m)) := by
    rw [show proofErase Γ (.proj s j m) = .proj s j (proofErase Γ m) from if_neg hn]
    exact .proj hi HT' hj' hl' RN'
  obtain ⟨C, heC, EC⟩ := proofErase_scoped_typeRecovery_replay hd hΓ he RP
  obtain ⟨_, hC⟩ := heC.isType henv hΓ
  have V := proofErase_carrier_aligned_projection_type_full_variant HT HT' hw hw' HL hj hj' HP (.refl (a := proofErase Γ m))
  rw [← EC] at V
  exact (LevelCoreNative.projection_compute HA).mono (fun H => .inl H) |>.trans
    (by simpa only [EC] using (proofErase_carrier_aligned_variant_level_compute V hΓ hC).mono (fun H => .inr H))

private theorem recovery_not_proof (R : ScopedTypeRecovery Step Δ e A) : e ≠ .proof := by
  induction R with
  | convert _ _ ih => exact ih
  | bvar | sort | const | lam | app | forallE | proj => intro E; cases E

/-- All native outputs of the same typed expression join in the level core.
This covers every source form, including dependent projections and binders.
It assumes only confluence of the ordinary core, not guarded-stage confluence
or recovery of an independently assigned type. -/
theorem proofErase_native_level_core_coherent
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = source)
    (RL : ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) source A)
    (RR : ScopedTypeRecovery (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) source B) :
    ComputeJoin (ErasedLevelCore D) A B := by
  have hd : ErasedScopedPrimitiveDescent (fun _ => ErasedLevelCore D) := erased_level_core_descent hs
  have hcl : TypedCoreConfluence (ErasedLevelCore D) := proofErase_level_core_confluent hs hlevels hcon hc
  have hj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute (fun _ => ErasedLevelCore D) (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out :=
    fun _ _ R => .of_compute R.core_forget
  induction source generalizing Γ e T A B with
  | proof => exact (recovery_not_proof RL rfl).elim
  | bvar i =>
    obtain rfl := erase_bvar_inv Ee
    exact proofErase_variable_native_core_join hcl hj hj hΓ he RL RR
  | const c ls =>
    obtain rfl := erase_const_inv Ee
    have hn : ¬ IsProof Γ (.const c ls) := by
      intro hp; rw [proofErase_eq_proof.2 hp] at Ee; cases Ee
    exact proofErase_constant_native_core_join hd hcl hj hj hΓ he hn RL RR
  | sort u =>
    obtain rfl := erase_sort_inv Ee
    exact native_join_convert hd hd hcl hj hj hΓ he
      (Ee ▸ ScopedTypeRecovery.sort (he.sort_inv henv))
      (Ee ▸ ScopedTypeRecovery.sort (he.sort_inv henv)) .refl RL.sort_compute RR.sort_compute
  | app f a ihf _ =>
    obtain ⟨f₀, a₀, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := he.app_inv henv hΓ
    obtain ⟨XL, YL, RFL, RCL⟩ := RL.app_origin
    obtain ⟨XR, YR, RFR, RCR⟩ := RR.app_origin
    obtain ⟨shared, HL, HR⟩ := ihf hΓ hf Ef RFL RFR
    obtain ⟨X, Y, rfl, _, HYL⟩ := HL.pi_parts (fun H => erased_level_core_no_pi H)
    obtain ⟨X', Y', E, _, HYR⟩ := HR.pi_parts (fun H => erased_level_core_no_pi H)
    cases E
    have HB : ComputeJoin (ErasedLevelCore D) (YL.inst a) (YR.inst a) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        (ComputeJoin.subst (fun H => erased_level_core_subst H)
          (σ := ProofShape.Subst.one a) ⟨_, HYL, HYR⟩)
    exact native_join_convert hd hd hcl hj hj hΓ he
      (Ee ▸ ScopedTypeRecovery.app RFL) (Ee ▸ ScopedTypeRecovery.app RFR) HB RCL RCR
  | lam X b _ ihb =>
    obtain ⟨X₀, b₀, rfl, _, EX, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hX⟩, _, hb⟩ := he.lam_inv henv hΓ
    obtain ⟨BL, RBL, RCL⟩ := lam_origin RL
    obtain ⟨BR, RBR, RCR⟩ := lam_origin RR
    have HB := ihb (Γ := X₀ :: Γ) ⟨hΓ, u, hX⟩ hb Eb
      (by simpa only [proofEraseCtx, EX] using RBL)
      (by simpa only [proofEraseCtx, EX] using RBR)
    exact native_join_convert hd hd hcl hj hj hΓ he
      (Ee ▸ ScopedTypeRecovery.lam RBL) (Ee ▸ ScopedTypeRecovery.lam RBR)
      (ComputeJoin.forallE .refl HB) RCL RCR
  | forallE X Y _ _ =>
    obtain ⟨uL, vL, RXL, RYL, RCL⟩ := pi_origin RL
    obtain ⟨uR, vR, RXR, RYR, RCR⟩ := pi_origin RR
    have RNL := Ee ▸ ScopedTypeRecovery.forallE RXL RYL
    have RNR := Ee ▸ ScopedTypeRecovery.forallE RXR RYR
    obtain ⟨CL, htL, EL⟩ := proofErase_scoped_typeRecovery_replay hd hΓ he RNL
    obtain ⟨CR, htR, ER⟩ := proofErase_scoped_typeRecovery_replay hd hΓ he RNR
    obtain rfl := erase_sort_inv EL
    obtain rfl := erase_sort_inv ER
    have HE := (htL.uniqU henv hΓ htR).sort_inv henv hΓ
    have hw := (htR.isType henv hΓ).choose_spec.sort_inv henv
    exact native_join_convert hd hd hcl hj hj hΓ he RNL RNR
      (.of_compute (.base (.inr (.sort HE hw)))) RCL RCR
  | proj s j m ihm =>
    obtain ⟨m₀, rfl, hn, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    obtain ⟨info, ls, doms, result, hjL, args, hi, HT, hl, RML, RCL⟩ := proj_origin RL
    obtain ⟨info', ls', doms', result', hjR, args', hi', HT', hl', RMR, RCR⟩ := proj_origin RR
    cases henv.ordered.projections_unique hi hi'
    obtain ⟨shared, HL, HR⟩ := ihm hΓ hm.hasType.2 Em RML RMR
    have RML' := Em ▸ RML
    have RMR' := Em ▸ RMR
    obtain ⟨F, hmF, EF⟩ := proofErase_scoped_typeRecovery_replay hd hΓ hm.hasType.2 RML'
    obtain ⟨_, hF⟩ := hmF.isType henv hΓ
    obtain ⟨lsS, argsS, mid, rfl, _, _, _⟩ :=
      family_path_origin hs hlevels hcon (hD (henv.projectionRigid hi)) hi hΓ hF EF HL
    have RMS := RML'.convert (HL.scoped (fun H => .base H))
    obtain ⟨_, hwS, _, _⟩ := proofErase_native_structure_family_universes hd hd hΓ hm.hasType.2 hi RML' RMS
    obtain ⟨dsS, rS, HTS⟩ := projection_telescope_exists hi hwS
    have hjS : info.nparams + j < dsS.length := by have := HT.numFields; have := HTS.numFields; omega
    have PL := proofErase_native_projection_level_core_path hs hlevels hcon
      (hD (henv.projectionRigid hi)) hΓ he hi HT HTS hjL hjS hl RML' HL hn
    have PR := proofErase_native_projection_level_core_path hs hlevels hcon
      (hD (henv.projectionRigid hi)) hΓ he hi HT' HTS hjR hjS hl' RMR' HR hn
    rw [Em] at PL PR
    exact native_join_convert hd hd hcl hj hj hΓ he
      (Ee ▸ ScopedTypeRecovery.proj hi HT hjL hl RML)
      (Ee ▸ ScopedTypeRecovery.proj hi HT' hjR hl' RMR) ⟨_, PL, PR⟩ RCL RCR

/-- Native recoveries using different conversion relations still agree when
both relations have typed level-core joins. Their outputs may contain arbitrary
dependent binders and projection recipes. The expression itself is unrestricted. -/
theorem proofErase_native_mixed_level_core_coherent
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hld : ErasedScopedPrimitiveDescent Left) (hrd : ErasedScopedPrimitiveDescent Right)
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : ScopedTypeRecovery Left (proofEraseCtx Γ) (proofErase Γ e) A)
    (RR : ScopedTypeRecovery Right (proofEraseCtx Γ) (proofErase Γ e) B) :
    ComputeJoin (ErasedLevelCore D) A B := by
  obtain ⟨AL, RAL, HA⟩ := LevelCoreNative.recovery_of_compute_join hs hlevels hcon hD hc hld hlj RL hΓ he rfl rfl
  obtain ⟨BR, RBR, HB⟩ := LevelCoreNative.recovery_of_compute_join hs hlevels hcon hD hc hrd hrj RR hΓ he rfl rfl
  obtain ⟨shared, RA, RB⟩ := proofErase_native_level_core_coherent hs hlevels hcon hD hc hΓ he rfl RAL RBR
  exact ⟨shared, (HA.mono (fun H => .inl H)).trans RA, (HB.mono (fun H => .inl H)).trans RB⟩

/-- Two native function-eta expansions at any common typed source join in
the level core when their guard paths do. This removes the variable/constant
spine restriction from the eta/eta overlap. It does not join eta against an
arbitrary competing computation or establish confluence of guarded stages. -/
theorem proofErase_native_mixed_level_core_eta_diamond
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hld : ErasedScopedPrimitiveDescent Left) (hrd : ErasedScopedPrimitiveDescent Right)
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : NativeEtaExpansion Left (proofEraseCtx Γ) (proofErase Γ e) a)
    (RR : NativeEtaExpansion Right (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore D) a b := by
  cases RL with
  | intro RN SN =>
    cases RR with
    | intro RN' SN' =>
      exact proofErase_native_eta_type_diamond hld hrd
        (fun H => erased_level_core_no_pi H) hΓ he RN RN' SN SN'
        (proofErase_native_mixed_level_core_coherent hs hlevels hcon hD hc hld hrd hlj hrj hΓ he RN RN')

/-- Native structure expansions with arbitrary parameters have a common core
reduct when their recovery guards have typed core joins. Family injectivity
identifies the structure; core spine readout joins the selected parameters.
Mixed proof/data fields and differing universe instances are allowed. -/
theorem proofErase_native_mixed_level_core_structure_diamond
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hld : ErasedScopedPrimitiveDescent Left) (hrd : ErasedScopedPrimitiveDescent Right)
    (hlj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Left (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out)
    (hrj : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Right (proofEraseCtx Γ) (proofErase Γ e) out →
      ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : NativeMaskedStructureExpansion Left (proofEraseCtx Γ) (proofErase Γ e) a)
    (RR : NativeMaskedStructureExpansion Right (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore D) a b := by
  cases RL with
  | intro hi hx ha hp RN =>
    rename_i family info ls ps
    cases RR with
    | intro hi' hx' ha' hp' RN' =>
      obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hld hΓ he RN
      obtain ⟨B, heB, EB⟩ := proofErase_scoped_typeRecovery_replay hrd hΓ he RN'
      obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EA
      obtain ⟨args', rfl, _⟩ := proofErase_const_spine_inv EB
      obtain ⟨_, hA⟩ := heA.isType henv hΓ
      have HH := henv.headInversion.rigid_rigid hΓ
        (henv.projectionRigid hi) (henv.projectionRigid hi')
        ((heA.uniqU henv hΓ heB).typeChain henv hΓ hA)
      cases HH.1
      cases henv.ordered.projections_unique hi hi'
      obtain ⟨shared, HL, HR⟩ := proofErase_native_mixed_level_core_coherent
        hs hlevels hcon hD hc hld hrd hlj hrj hΓ he RN RN'
      have hroot : SpineRootLevels (fun _ => ErasedLevelCore D) family := by
        intro Δ ls args out H
        exact erased_level_recovered_stage_spine_levels heq
          (henv.projectionRigid hi) (hD (henv.projectionRigid hi)) 0 (Δ := Δ) H
      obtain ⟨lsS, psS, rfl, _, HP⟩ := (HL.scoped (Δ := proofEraseCtx Γ) (fun H => .base H)).const_spine_levels @hroot
      obtain ⟨lsS', psS', E, _, HQ⟩ := (HR.scoped (Δ := proofEraseCtx Γ) (fun H => .base H)).const_spine_levels @hroot
      obtain ⟨_, rfl, rfl⟩ := ProofShape.const_spine_inj E
      obtain ⟨hw, hw', hl, HE⟩ := proofErase_native_structure_family_universes hld hrd hΓ he hi RN RN'
      obtain ⟨PL, PR⟩ := nativeStructureOutput_levels_join
        (Step := fun _ => ErasedLevelCore D) (fun H => .base (.inr H))
        hi hw hw' hl HE HP HQ .refl .refl
      exact ⟨_, PL.core_forget, PR.core_forget⟩

private theorem stage_zero_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hlevels : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ComputeJoin (ErasedLevelCore D) (proofErase Γ e) out := by
  apply proofErase_scoped_compute_core_join
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (proofErase_level_core_confluent hs hlevels hcon hc) (R := R) (hΓ := hΓ) (ht := he) (EΓ := rfl) (Ee := rfl)
  intro Γ e T Δ a b H _ _ _ _
  rcases H with H | H
  · exact .of_compute (.base H)
  · exact (ComputeJoin.of_compute (.beta H.beta_back)).symm

/-- The eta/eta root overlap at the first guarded stage joins for every
typed source. Stage-zero guards may interleave ordinary computation, universe
conversion and constant beta expansion. No native-image or coverage premise
is imposed on subterms or arguments. -/
theorem proofErase_stage_one_native_eta_diamond
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hlevels : D.LevelCompatible univs) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hD : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (RR : NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (proofErase Γ e) b) : ComputeJoin (ErasedLevelCore D) a b :=
  proofErase_native_mixed_level_core_eta_diamond hs hlevels hcon hD hc
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (fun hΓ he R => stage_zero_join heq hs hlevels hcon hc hΓ he R)
    (fun hΓ he R => stage_zero_join heq hs hlevels hcon hc hΓ he R) hΓ he RL RR

/-- Actual stored environments discharge the confluence and compatibility
conditions of the first-stage eta/eta overlap. This is one critical-pair result,
not confluence of the entire first stage or the full finite-stage union. -/
theorem StoredCore.stage_one_native_eta_diamond
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage (Definitions.ofEnv env univs henv) 0)
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (RR : NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage (Definitions.ofEnv env univs henv) 0)
      (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore (Definitions.ofEnv env univs henv)) a b :=
  proofErase_stage_one_native_eta_diamond heq (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) hcon
    (fun hr _ _ => Definitions.ofEnv_no_rigid henv hr)
    (StoredCore.typed_core_confluence hcon) hΓ he RL RR

/-- The structure/structure root overlap at the first guarded stage is
joinable in every actual stored environment, with arbitrary parameter vectors.
This does not assert joining of higher-stage or mixed root overlaps. -/
theorem StoredCore.stage_one_native_structure_diamond
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (RL : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage (Definitions.ofEnv env univs henv) 0)
      (proofEraseCtx Γ) (proofErase Γ e) a)
    (RR : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage (Definitions.ofEnv env univs henv) 0)
      (proofEraseCtx Γ) (proofErase Γ e) b) :
    ComputeJoin (ErasedLevelCore (Definitions.ofEnv env univs henv)) a b := by
  have hs := Definitions.ofEnv_sound (U := univs) henv
  have hl : (Definitions.ofEnv env univs henv).LevelCompatible univs :=
    Definitions.ofEnv_levelCompatible henv
  have hc : TypedCoreConfluence (ErasedIotaPrimitive (Definitions.ofEnv env univs henv)) :=
    StoredCore.typed_core_confluence hcon
  exact proofErase_native_mixed_level_core_structure_diamond heq hs hl hcon
    (fun hr _ _ => Definitions.ofEnv_no_rigid henv hr) hc
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (erased_static_structure_eta_expansion_stage_descent heq hs 0)
    (fun hΓ he R => stage_zero_join heq hs hl hcon hc hΓ he R)
    (fun hΓ he R => stage_zero_join heq hs hl hcon hc hΓ he R) hΓ he RL RR

end Lean4Lean.VEnv.Strengthening
