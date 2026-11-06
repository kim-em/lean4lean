import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixComponentDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstantElimination
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Reading original Eq arguments at a spine cut

The constant-spine cut supplies its component origins from a whole computation.
A specialized Eq root therefore reads the original lower carrier and endpoints.
Ordinary core roots cannot be the selected cut of a proof-major Eq probe; after
universe changes are passed, the remaining cases are controlled expansions,
general singleton prefixes, and native eta expansions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront

open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private erase_app_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- A specialized root on a prefix of a computed Eq spine supplies the
original carrier guard. The five required component paths are extracted from
the retained whole argument vector; the suffix need not have length one. -/
theorem ProofShape.ComputedJointPrefixPrimitive.spine_component_guard
    (H : ComputedJointPrefixPrimitive Step Δ (ProofShape.mkApps (.const ``Eq.rec ls) pre) target)
    (HA : List.Forall₂ (ScopedCompute Step Δ) (α :: a :: M :: m :: b :: rest) (pre ++ pending)) :
    ComputedJointCarrierGuard Step Δ α a b := by
  generalize ES : ProofShape.mkApps (.const ``Eq.rec ls) pre = source at H
  cases H with
  | @intro α' a' b' v' w' M' m' HG =>
    obtain ⟨_, rfl, rfl⟩ := ProofShape.const_spine_inj
      (ps' := [α', a', M', m', b']) (ls' := [v', w']) ES
    cases HA with | cons Rα HA =>
      cases HA with | cons Ra HA =>
        cases HA with | cons _ HA =>
          cases HA with | cons _ HA =>
            cases HA with | cons Rb _ =>
              exact .carrierCompute Rα (.carrierReduce Ra Rb HG)

/-- Pi-inert computation leaves a literal proof marker unchanged. -/
theorem ProofShape.ScopedCompute.pi_inert_proof_fixed
    (R : ScopedCompute (PiInertStage D n) Δ .proof out) : out = .proof := by
  apply scoped_normal_fixed R
  intro Δ
  refine ⟨?_, trivial⟩
  intro out H
  rcases H.2 with H | ⟨u, H⟩
  · exact H
  · cases H

/-- Every computed prefix of a six-argument proof-major Eq spine is blocked
for ordinary core roots: it either lacks the major or still ends in proof.
No typings of the other five arguments are required for this exclusion. -/
theorem pi_inert_eq_prefix_no_core_root
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HA : List.Forall₂ (ScopedCompute (PiInertStage D n) Δ)
      [α, a, M, m, b, .proof] (pre ++ pending)) :
    ¬ ErasedIotaPrimitive D (ProofShape.mkApps (.const ``Eq.rec ls) pre) target := by
  apply erased_iota_eqRec_no_root hreg hoff hRec (constHead_mkApps _ _)
  by_cases hshort : pre.length ≤ 5
  · exact .inl ⟨pre, ls, rfl, hshort⟩
  · have HL := HA.length_eq
    simp only [List.length_cons, List.length_nil, List.length_append] at HL
    have hp : pending.length = 0 := by omega
    obtain rfl := List.eq_nil_of_length_eq_zero hp
    simp only [List.append_nil] at HA
    cases HA with | cons _ HA =>
      cases HA with | cons _ HA =>
        cases HA with | cons _ HA =>
          cases HA with | cons _ HA =>
            cases HA with | cons _ HA =>
              cases HA with | cons RP HA =>
                cases HA
                obtain rfl := RP.pi_inert_proof_fixed
                exact .inr ⟨_, rfl⟩

/-- No prefix of a sort-typed application spine can undergo structure eta.
An unapplied prefix is itself sort-typed; any proper prefix has an actual Pi
assignment because at least one argument is still pending. -/
theorem ControlTyping.no_masked_structure_spine
    (hstep : ErasedScopedPrimitiveDescent Step)
    (HT : ControlTyping Δ (ProofShape.mkApps source pending) (.sort u))
    (H : NativeMaskedStructureExpansion Step Δ source target) : False := by
  cases pending with
  | nil => exact HT.no_masked_structure hstep H
  | cons arg rest =>
    have HT' : TypedSource Δ (ProofShape.mkApps (.app source arg) rest) := by
      obtain ⟨Γ, e, hΓ, EΓ, ht, Ee⟩ := HT
      exact ⟨Γ, e, _, hΓ, EΓ, ht, Ee⟩
    obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := typed_spine_head HT'
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨A, B, hf, _⟩ := ht.app_inv henv hΓ
    rw [← Ef] at H
    cases H with
    | intro hi _ _ _ RN =>
      obtain ⟨F, hfF, EF⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
      obtain ⟨ps, rfl, _⟩ := proofErase_const_spine_inv EF
      obtain ⟨_, hF⟩ := hfF.isType henv hΓ
      exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi) hF
        (hfF.uniqU henv hΓ hf)

/-- The root families left after ordinary core, specialized Eq readout and
structure eta. This is a classification of concrete roots, not a coverage or termination claim. -/
def StaticOtherSpineRoot (D : Definitions) (n : Nat) (Δ : List ProofShape)
    (source target : ProofShape) : Prop :=
  ConstantExpansion source target ∨ ∃ k, k < n ∧
    (CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Δ source target ∨
     NativeIdentityExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ source target ∨
     NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D k) Δ source target)

/-- With level core, specialized Eq and structure eta excluded, an actual
root belongs to the remaining constant/identity/function-eta/singleton cases. -/
theorem static_other_spine_root
    (H : ErasedStaticStructureEtaExpansionStage D n Δ source target)
    (HC : ¬ ErasedLevelCore D source target)
    (HE : ¬ ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ source target)
    (HS : ¬ NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Δ source target) :
    StaticOtherSpineRoot D n Δ source target := by
  induction n with
  | zero =>
    rcases H with H | H
    · exact (HC H).elim
    · exact .inl H
  | succ n ih =>
    rcases H with H | H | H | H | H | H
    · rcases ih H (fun H => HE (H.mono (fun H => .inl H)))
        (fun H => HS (H.mono (fun H => .inl H))) with H | ⟨k, hk, H⟩
      · exact .inl H
      · exact .inr ⟨k, by omega, H⟩
    · exact .inr ⟨n, by omega, .inl H⟩
    · exact (HE (H.mono (fun H => .inl H))).elim
    · exact .inr ⟨n, by omega, .inr (.inl H)⟩
    · exact .inr ⟨n, by omega, .inr (.inr H)⟩
    · exact (HS (H.mono (fun H => .inl H))).elim

/-- From a whole exposure computation, either a specialized Eq prefix reads
back the original lower equation, or a root of another family acts on the
original spine. Universe-only and ordinary core roots have been excluded, as
has structure eta at every prefix of the sort-typed source. The remaining cut retains all original argument origins, its actual source typing,
and both complete path segments. It need not yet be a general singleton guard. -/
theorem pi_inert_eq_exposure_readout_or_spine_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (Eargs : args = [(proofErase Γ A).liftN count offset,
      (proofErase Γ a).liftN count offset, M, m, (proofErase Γ b).liftN count offset, .proof])
    (HT : ControlTyping (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out) (HE : CarrierExposure out) :
    (ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) ∧ env.IsDefEq univs Γ a b A) ∨
    (∃ ls pre pending target,
      List.Forall₂ (· ≈ ·) [v,w] ls ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')) args (pre ++ pending) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
        (ProofShape.mkApps (.const ``Eq.rec [v,w]) args)
        (ProofShape.mkApps (.const ``Eq.rec ls) (pre ++ pending)) ∧
      TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) ∧
      PiInertStage D n (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
      StaticOtherSpineRoot D n (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ') (ProofShape.mkApps target pending) out) := by
  classical
  rcases R.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
      (@level_primitive_spine_roots univs ``Eq.rec) with
    ⟨ls, args', EO, _, _⟩ | ⟨ls, pre, pending, target, HL, HA, RP, H, HN, RT⟩
  · exact ((carrier_exposure_ne_eqRec heq HE) (by rw [EO, constHead_mkApps]; rfl)).elim
  · have HA₆ := Eargs ▸ HA
    have hd : ErasedScopedPrimitiveCertificateDescent
        (ErasedStaticStructureEtaExpansionStage D n) (ErasedStaticStructureEtaExpansionStage D n) :=
      erased_static_structure_eta_expansion_stage_certificate_descent heq hs n
    by_cases HQ : ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n)
        (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec ls) pre) target
    · have HG := HQ.spine_component_guard (HA₆.imp (fun _ _ R => R.mono pi_inert_stage_embed))
      have HGl := proofErase_computed_joint_carrier_certificate_descend hd hΓ hΓ' W ha hb HG
      exact .inl ⟨HGl, proofErase_computed_joint_carrier_reflect hd.descent hΓ ha hb HGl⟩
    · have HC : ¬ ErasedLevelCore D (ProofShape.mkApps (.const ``Eq.rec ls) pre) target := by
        rintro (HC | HC)
        · exact pi_inert_eq_prefix_no_core_root hreg hoff hRec HA₆ HC
        · exact HN HC
      have hp : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
        ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)
      have HTsrc : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) := by
        obtain ⟨Γ₀, e₀, hΓ₀, EΓ₀, ht₀, Ee₀⟩ := HT
        exact ⟨Γ₀, e₀, _, hΓ₀, EΓ₀, ht₀, Ee₀⟩
      have HS := HT.compute hp RP
      rw [ProofShape.mkApps_append] at HS
      exact .inr ⟨ls, pre, pending, target, HL, HA, RP,
        RP.spine_cut_source_typed hp HTsrc,
        H, static_other_spine_root H.1 HC HQ (fun H => HS.no_masked_structure_spine hd.descent H), RT⟩

/-- The two administrative expansion alternatives at a typed spine cut can
be bypassed without losing its pending arguments, exact exposed output, or
restricted stage. This supplies a continuation from the cut's source; it does
not assert that recursively choosing and bypassing cuts terminates. -/
theorem pi_inert_expansion_prefix_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ source)
    (H : ConstantExpansion source target ∨ NativeIdentityExpansion Recovery Δ source target)
    (RT : ScopedCompute (PiInertStage D n) Δ (ProofShape.mkApps target pending) out)
    (HE : CarrierExposure out) :
    ScopedCompute (PiInertStage D n) Δ (ProofShape.mkApps source pending) out := by
  rcases H with H | H
  · obtain ⟨Γ, e, T, hΓ, rfl, ht, rfl⟩ := HT
    cases H with
    | intro _ =>
      have hA : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
        .sort (by trivial)
      have EA : proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) :=
        if_neg (not_isProof_of_sort hΓ hA)
      exact pi_inert_constant_spine_eliminate heq hs hΓ hA ht HE.not_lambda_spine
        (by simpa only [EA, ProofShape.constantExpansion] using RT)
  · cases H with
    | intro _ => exact RT.pi_inert_identity_spine_eliminate HE.not_lambda_spine

end Lean4Lean.VEnv.Strengthening
