import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertPairedCompositionFront
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProbeCarrier

/-! # Retained conversion of carrier histories

A type comparison retains transport of finite carrier histories under every
typed substitution. These transport certificates compose, while bare term
histories do not acquire a transitivity rule. Ground paired interpretation
consumes the certificate at each of its two environments. Core joins and
certified aliases of a unit type construct certificates; arbitrary strong
type-comparison coverage remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Retained type-conversion evidence. At every actual typed substitution,
finite carrier histories transport in both directions, for arbitrary raw
endpoints in the target context. The output stage may depend on the input.
Missing for full coverage is construction from each original strong type
comparison; ordinary definitional equality alone is not a constructor. -/
def PiInertCarrierTransport (D : Definitions) (Δ : List ProofShape)
    (T U : ProofShape) : Prop :=
  ∀ {Λ σ}, ContextSubstitution Δ Λ σ → ∀ a b,
    (∃ n, PiInertWorldHistory D n Λ (T.subst σ) a b) ↔
    (∃ n, PiInertWorldHistory D n Λ (U.subst σ) a b)

/-- Reflexive type comparison retains precisely the same histories. -/
theorem PiInertCarrierTransport.refl : PiInertCarrierTransport D Δ T T :=
  fun _ _ _ => Iff.rfl

/-- Type symmetry reverses the two already proved transport functions. -/
theorem PiInertCarrierTransport.symm (H : PiInertCarrierTransport D Δ T U) :
    PiInertCarrierTransport D Δ U T := fun W a b => (H W a b).symm

/-- Type transitivity composes transport at the same substituted intermediate
carrier. This is not transitivity of term histories at a fixed carrier. -/
theorem PiInertCarrierTransport.trans (H : PiInertCarrierTransport D Δ T U)
    (K : PiInertCarrierTransport D Δ U V) : PiInertCarrierTransport D Δ T V :=
  fun W a b => (H W a b).trans (K W a b)

/-- The certificate itself survives arbitrary typed substitution; its future
endpoints are still arbitrary shapes, not required to be substitution images. -/
theorem PiInertCarrierTransport.substitute (H : PiInertCarrierTransport D Δ T U)
    (W : ContextSubstitution Δ Λ σ) :
    PiInertCarrierTransport D Λ (T.subst σ) (U.subst σ) := by
  intro Ξ τ V a b
  rw [ProofShape.subst_subst, ProofShape.subst_subst]
  exact H (W.comp V) a b

/-- Typed ordinary-core joins construct the whole transport certificate.
Both joins and carrier-source typings substitute directly. -/
theorem PiInertCarrierTransport.of_core_join
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HT : TypedSource Δ T) (HU : TypedSource Δ U)
    (J : ComputeJoin (ErasedLevelCore D) T U) : PiInertCarrierTransport D Δ T U := by
  intro Λ σ W a b
  have K := J.subst (fun R => erased_level_core_subst R) (σ := σ)
  exact ⟨fun ⟨n, H⟩ => ⟨n, H.core_join hs hc (HU.subst W) K⟩,
    fun ⟨n, H⟩ => ⟨n, H.core_join hs hc (HT.subst W) K.symm⟩⟩

/-- Two retained computations to the same nullary empty family construct
transport in both directions. Each target history is built from its own
carrier exposure; no composition of endpoint comparisons is assumed. -/
theorem PiInertCarrierTransport.unit_aliases
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (RT : PiInertEvidence D n .compute Δ T (.const family ls))
    (RU : PiInertEvidence D m .compute Δ U (.const family ls)) :
    PiInertCarrierTransport D Δ T U := by
  intro Λ σ W a b
  have HT : PiInertWorldHistory D n Λ (T.subst σ) a b :=
    ((pi_inert_unit_carrier_history hi hp hx hf hD).carrier_prefix
      (RT.substitute W)).world_history
  have HU : PiInertWorldHistory D m Λ (U.subst σ) a b :=
    ((pi_inert_unit_carrier_history hi hp hx hf hD).carrier_prefix
      (RU.substitute W)).world_history
  exact ⟨fun _ => ⟨m, HU⟩, fun _ => ⟨n, HT⟩⟩

/-- An assigned ground comparison preserves proof-marker status. Soundness
is used only in the original context at realized common typings. -/
theorem PiInertAssignedBase.proof_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertAssignedBase D Δ a b T) : a = .proof ↔ b = .proof := by
  obtain ⟨Γ, a₀, A, hΓ, rfl, ha, Ea, EA⟩ := H.left
  obtain ⟨_, hA⟩ := ha.isType henv hΓ
  obtain ⟨b₀, hb, Eb⟩ := H.right.realize_carrier hΓ hA EA
  have HE := PiInertDemandBase.actual_defeq heq hs hΓ ha hb
    (by simpa only [Ea, Eb, EA] using H.ground)
  rw [← Ea, ← Eb, proofErase_eq_proof, proofErase_eq_proof]
  exact isProof_congr hΓ HE

/-- A new assignment for one side of an assigned ground comparison gives
the other side the same new assignment. The proof-marker case is derived
from the comparison; non-proof cases use type uniqueness on a fixed endpoint.
This transports typing only, not the retained carrier history. -/
theorem PiInertAssignedBase.transfer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertAssignedBase D Δ a b T) (HA : TypedAt Δ a U) : TypedAt Δ b U := by
  by_cases hn : a = .proof
  · have hb := (H.proof_iff heq hs).1 hn
    simpa only [hn, hb] using HA
  · exact H.left.transfer HA H.right hn

/-- Ground paired interpretation changes both selected carriers using the
retained type certificates. Each certificate is applied at its own typed
environment. Cross-endpoint assignments are proved, including proof markers;
no semantic assignment is inferred from the transport certificate itself. -/
theorem PiInertGuardedPairInterpretation.convert_ground
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertGuardedPairInterpretation D Δ uses a b T U (.plain .ground) (.plain .ground))
    (LT : PiInertCarrierTransport D Δ T V) (RT : PiInertCarrierTransport D Δ U E)
    (HA : TypedAt Δ a V) (HB : TypedAt Δ b E) :
    PiInertGuardedPairInterpretation D Δ uses a b V E (.plain .ground) (.plain .ground) := by
  refine ⟨HA, HB, ?_⟩
  intro Λ σ τ WL WR images
  have old := H.run WL WR images
  have AL := HA.subst WL
  have BR := HB.subst WR
  have BL := old.forward.base.transfer heq hs AL
  have AR := old.backward.base.transfer heq hs BR
  have HL := (LT WL _ _).1 old.forward.base.ground.history
  have HR := (RT WR _ _).1 old.backward.base.ground.history
  exact ⟨⟨AL, BL, AL.sources.1, BL.sources.1, AL.sources.2, HL⟩,
    ⟨BR, AR, BR.sources.1, AR.sources.1, BR.sources.2, HR⟩⟩

/-- The original strong conversion rule consumes its type child's retained
transport and its term child's ground interpreter. The ordinary children
construct the new actual assignments. Construction of the transport from an
arbitrary type child remains an explicit coverage gap. -/
theorem StrongBounded.paired_ground_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ A B (.sort u))
    (termChild : StrongBounded env univs k Γ f g A)
    (HT : PiInertCarrierTransport D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B))
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ A) (proofErase Γ A)
      (.plain .ground) (.plain .ground)) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ B) (proofErase Γ B)
      (.plain .ground) (.plain .ground) := by
  have HE := typeChild.strong.defeq
  have HF := termChild.strong.defeq
  exact H.convert_ground heq hs HT HT
    (TypedAt.of_typed hΓ (HE.defeq HF.hasType.1))
    (TypedAt.of_typed hΓ (HE.defeq HF.hasType.2))

/-- Literal nullary empty carriers construct ground paired interpreters for
arbitrary actually assigned operands, with no image requirements. All target
endpoints are supplied by the paired typed substitutions. -/
theorem PiInertGuardedPairInterpretation.unit_ground
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (HA : TypedAt Δ a (.const family ls)) (HB : TypedAt Δ b (.const family ls)) :
    PiInertGuardedPairInterpretation D Δ [] a b (.const family ls) (.const family ls)
      (.plain .ground) (.plain .ground) := by
  refine ⟨HA, HB, ?_⟩
  intro Λ σ τ WL WR _
  have AL := HA.subst WL
  have BR := HB.subst WR
  simp only [ProofShape.subst] at AL BR
  have HL : PiInertWorldHistory D 0 Λ (.const family ls) (a.subst σ) (b.subst τ) :=
    (pi_inert_unit_carrier_history hi hp hx hf hD).world_history
  exact ⟨⟨AL, BR, AL.sources.1, BR.sources.1, AL.sources.2, 0, HL⟩,
    ⟨BR, AL, BR.sources.1, AL.sources.1, BR.sources.2, 0, HL.symm⟩⟩

/-- A retained proposition-index child constructs carrier transport from a
unit type to its Eq-rec-hidden alias. The target exposure is constructed at
the next stage, not assumed from ordinary equality of the probe and minor. -/
theorem PiInertEvidence.unit_probe_transport
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (H : PiInertEvidence D n (.compare true) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q)) :
    PiInertCarrierTransport D (proofEraseCtx Γ) (proofErase Γ (.const family ls))
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q)) := by
  have RS := PiInertEvidence.core (stage := 0) hs hc hΓ hS
    (.refl (e := proofErase Γ (.const family ls)))
  have RT := H.type_probe heq hs hl hcon hreg hoff hRec hΓ hS hP hQ hq
  have ES : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hS)
  rw [ES] at RS RT ⊢
  intro Λ σ W a b
  exact PiInertCarrierTransport.unit_aliases hi hp hx hf hD RS RT W a b

/-- The hidden-unit comparison is constructed from its original unit rule
and its explicit proposition-index child. The result interprets arbitrary
paired substitutions and requires no image evidence, output history, or
composition of the constructor-bridge comparisons. -/
theorem PiInertEvidence.unit_probe_ground_interpretation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (ha : env.HasType univs Γ a (.const family ls))
    (hb : env.HasType univs Γ b (.const family ls))
    (H : PiInertEvidence D n (.compare true) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ Q)) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ a) (proofErase Γ b)
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q))
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q)) (.plain .ground) (.plain .ground) := by
  have ES : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hS)
  have original := PiInertGuardedPairInterpretation.unit_ground hi hp hx hf hD
    (ES ▸ TypedAt.of_typed hΓ ha) (ES ▸ TypedAt.of_typed hΓ hb)
  have CT : PiInertCarrierTransport D (proofEraseCtx Γ) (proofErase Γ (.const family ls))
      (proofErase Γ (eqTypeProbe u (.const family ls) P Q q)) :=
    H.unit_probe_transport heq hs hl hcon hc hreg hoff hRec hi hp hx hf hD hΓ hS hP hQ hq
  rw [ES] at CT
  have HPQ := proofErase_computed_joint_compare_reflect
    (fun hΓ hΓ' W ht R => erased_static_structure_eta_expansion_stage_descent heq hs n
      hΓ hΓ' W ht (pi_inert_stage_embed R)) hΓ hP hQ (H.base .refl .refl)
  have HE := eqTypeProbe_defeq heq hΓ hS hP hQ hq
    (HPQ.1 ⟨_, HasType.sort (by trivial)⟩)
  exact original.convert_ground heq hs CT CT
    (TypedAt.of_typed hΓ (HE.symm.defeq ha)) (TypedAt.of_typed hΓ (HE.symm.defeq hb))

omit [Params] in
/-- In the full environment core, a reflexive proposition index constructs
the hidden-unit interpreter outright. The equality major may be any actual
proof, including a free variable. All carrier transport, index comparison
and paired histories are constructed; only actual declarations and typings
remain as premises. This example does not provide arbitrary-index coverage. -/
theorem EnvironmentCore.reflexive_unit_probe_ground_interpretation
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {family info ls Γ u P q a b}, env.HasCanonicalEq →
      env.projections family info → info.nparams = 0 → info.nindices = 0 → info.numFields = 0 →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.const family ls) (.sort u) →
      env.HasType U Γ P (.sort .zero) →
      env.HasType U Γ q (eqApp (.succ .zero) (.sort .zero) P P) →
      env.HasType U Γ a (.const family ls) → env.HasType U Γ b (.const family ls) →
      PiInertGuardedPairInterpretation definitions (proofEraseCtx Γ) []
        (proofErase Γ a) (proofErase Γ b)
        (proofErase Γ (eqTypeProbe u (.const family ls) P P q))
        (proofErase Γ (eqTypeProbe u (.const family ls) P P q))
        (.plain .ground) (.plain .ground) := by
  letI := henv.params U
  intro family info ls Γ u P q a b heq hi hp hx hf hΓ hS hP hq ha hb
  have hc : TypedCoreConfluence (ErasedLevelCore definitions) :=
    typed_level_core_confluence (fun H => H)
  obtain ⟨data, hreg, hr, hn, _⟩ := heq.recursorRegistration henv
  have HR : PiInertEvidence definitions 0 .compute (proofEraseCtx Γ)
      (proofErase Γ P) (proofErase Γ P) := .core sound hc hΓ hP .refl
  have HC : PiInertEvidence definitions 0 (.compare true) (proofEraseCtx Γ)
      (proofErase Γ P) (proofErase Γ P) := HR.join hc HR
  exact HC.unit_probe_ground_interpretation heq sound (levelCompatible (fun H => H))
    (fun H => H) hc hreg (hr.eqRec_target heq hn).2.1 (no_eqRec heq)
    hi hp hx hf (no_rigid (henv.projectionRigid hi)) hΓ hS hP hP hq ha hb

end Lean4Lean.VEnv.Strengthening
