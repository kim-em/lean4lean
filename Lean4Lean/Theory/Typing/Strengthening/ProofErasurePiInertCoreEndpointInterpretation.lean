import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEliminationOrigins

/-! # Preserve recursive interpretations across core endpoint prefixes

The original reduct-typing child of beta supplies the interpretation. Actual
source typing and ordinary core computation transport that interpretation to
the redex under arbitrary paired substitutions, preserving all recursive
profiles and finite image requirements.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Ordinary core reduction preserves the exact raw assigned carrier. This
realizes the reduct at the source's actual type rather than using an unrelated
target source witness. -/
theorem ProofShape.TypedAt.core_reduct
    (hs : D.Sound env univs) (H : TypedAt Δ a T)
    (R : Compute (ErasedLevelCore D) a b) : TypedAt Δ b T := by
  obtain ⟨Γ, a₀, A, hΓ, EΓ, ha, Ea, EA⟩ := H
  obtain ⟨b₀, HE, Eb⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ha EΓ Ea (R.scoped (fun R => .base R))
  exact ⟨Γ, b₀, A, hΓ, EΓ, HE.hasType.2, Eb, EA⟩

/-- An actually sourced ordinary-core predecessor receives the reduct's
assigned carrier. If the reduct erases to proof, actual equality forces the
source to be the same raw marker; otherwise erasure reflection realizes the
reduct's assignment on the exact actual reduct. -/
theorem ProofShape.TypedAt.core_predecessor
    (hs : D.Sound env univs) (H : TypedAt Δ b T) (HA : TypedSource Δ a)
    (R : Compute (ErasedLevelCore D) a b) : TypedAt Δ a T := by
  obtain ⟨Γ, a₀, A, hΓ, EΓ, ha, Ea⟩ := HA
  obtain ⟨b₀, HE, Eb⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ha EΓ Ea (R.scoped (fun R => .base R))
  by_cases hp : b = .proof
  · have hpa := (isProof_congr hΓ HE).2 (proofErase_eq_proof.1 (Eb.trans hp))
    have E : a = .proof := Ea.symm.trans (proofErase_eq_proof.2 hpa)
    simpa only [E, hp] using H
  have H' : TypedAt (proofEraseCtx Γ) b T := EΓ ▸ H
  obtain ⟨B, hb, EB⟩ := H'.realize_term hΓ HE.hasType.2 Eb hp
  exact ⟨Γ, a₀, B, hΓ, EΓ, (HE.toU.of_r henv hΓ hb).hasType.1, Ea, EB⟩

/-- Directed interpretation survives independent ordinary-core prefixes.
The right predecessor's cross assignment is derived from its interpreted
reduct after substitution. Original carriers, profiles and uses stay fixed. -/
theorem PiInertDirectedPairInterpretation.prefixes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertDirectedPairInterpretation D Δ uses a' b' T U p)
    (HA : TypedAt Δ a T) (HB : TypedAt Δ b U)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertDirectedPairInterpretation D Δ uses a b T U p := by
  refine ⟨HA, HB, ?_⟩
  intro Λ σ τ WL WR images
  have old := H.run WL WR images
  have RL := RA.subst (fun R => erased_level_core_subst R) (σ := σ)
  have RR := RB.subst (fun R => erased_level_core_subst R) (σ := τ)
  have right := old.base.right.core_predecessor hs (HB.sources.1.subst WR) RR
  exact old.prefixes heq hs hc (HA.subst WL) right RL RR

/-- Paired prefix closure preserves both independently chosen recursive
interfaces and the same requirement list. Each direction retains its own
carrier and annotation substitution; no history composition is used. -/
theorem PiInertGuardedPairInterpretation.prefixes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertGuardedPairInterpretation D Δ uses a' b' T U p q)
    (HA : TypedAt Δ a T) (HB : TypedAt Δ b U)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertGuardedPairInterpretation D Δ uses a b T U p q := by
  refine ⟨HA, HB, ?_⟩
  intro Λ σ τ WL WR images
  have old := H.run WL WR images
  have RL := RA.subst (fun R => erased_level_core_subst R) (σ := σ)
  have RR := RB.subst (fun R => erased_level_core_subst R) (σ := τ)
  exact ⟨old.forward.prefixes heq hs hc (HA.subst WL)
      (old.forward.base.right.core_predecessor hs (HB.sources.1.subst WR) RR) RL RR,
    old.backward.prefixes heq hs hc (HB.subst WR)
      (old.backward.base.right.core_predecessor hs (HA.sources.1.subst WL) RL) RR RL⟩

/-- A self interpreter of the reduct supplies a self interpreter of its
ordinary-core predecessor, with no larger image requirements or new profile. -/
theorem PiInertGuardedInterpretation.prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertGuardedInterpretation D Δ uses b T p)
    (HA : TypedAt Δ a T) (R : Compute (ErasedLevelCore D) a b) :
    PiInertGuardedInterpretation D Δ uses a T p :=
  ⟨HA, (H.directed.prefixes heq hs hc HA HA R R).run⟩

/-- The original beta constructor consumes a paired self interpretation of
its rank-k reduct-typing child. This preserves arbitrary recursive profiles
and nonempty image requirements, including erased proofs. It does not build
or recursively interpret a new lambda derivation. General construction of the
reduct interpretation remains part of the simultaneous induction. -/
theorem StrongBounded.paired_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hu : u.WF univs) (hv : v.WF univs)
    (domainChild : StrongBounded env univs k Γ A A (.sort u))
    (bodyType : StrongBounded env univs k (A::Γ) B B (.sort v))
    (bodyChild : StrongBounded env univs k (A::Γ) body body B)
    (argumentChild : StrongBounded env univs k Γ x x A)
    (resultType : StrongBounded env univs k Γ (B.inst x) (B.inst x) (.sort v))
    (reductChild : StrongBounded env univs k Γ (body.inst x) (body.inst x) (B.inst x))
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ (body.inst x)) (proofErase Γ (body.inst x))
      (proofErase Γ (B.inst x)) (proofErase Γ (B.inst x)) p q) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ (.app (.lam A body) x)) (proofErase Γ (body.inst x))
      (proofErase Γ (B.inst x)) (proofErase Γ (B.inst x)) p q := by
  have HE := (StrongBounded.beta hu hv domainChild bodyType bodyChild argumentChild
    resultType reductChild).strong.defeq
  exact H.prefixes heq hs hc (.of_typed hΓ HE.hasType.1) (.of_typed hΓ HE.hasType.2)
    (.beta (proofErase_beta_forward hΓ HE.hasType.1 .beta)) .refl

/-- Projection-iota similarly consumes its original rank-k field-typing
child. Actual projection inversion supplies constructor saturation, so no
extra arity premise or reconstructed strong field derivation is required. -/
theorem StrongBounded.paired_projIota
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (sourceChild : StrongBounded env univs k Γ
      (.proj family index (VExpr.mkApps (.const info.ctorName ls) args))
      (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)) T)
    (hfield : args[info.nparams + index]? = some field)
    (fieldChild : StrongBounded env univs k Γ field field T)
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ field) (proofErase Γ field) (proofErase Γ T) (proofErase Γ T) p q) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ (.proj family index (VExpr.mkApps (.const info.ctorName ls) args)))
      (proofErase Γ field) (proofErase Γ T) (proofErase Γ T) p q := by
  have hsource := sourceChild.strong.defeq.hasType.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hsource.proj_inv henv hΓ
  have hlen := (projection_major_family henv hΓ hi (henv.projectionRigid hi) hm.hasType.2).2
  exact H.prefixes heq hs hc (.of_typed hΓ hsource) (.of_typed hΓ fieldChild.strong.defeq.hasType.1)
    ((proofErase_pattern_step_forward hs hΓ hsource (.projIota hi hlen hfield)).mono
      (fun R => .inl R)) .refl

/-- The stored-definition branch of extra consumes its original rank-k
right-hand-side typing child. The registered definition is included in the
ordinary core, and its exact universe instance supplies the prefix. The
separate built-in quotient equation is not asserted to be a delta step. -/
theorem StrongBounded.paired_extra_stored
    {value : VDefVal} {ls : List VLevel}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hdefs : ∀ {c ls rhs}, (Definitions.ofEnv env univs henv).unfolds c ls rhs →
      D.unfolds c ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hdf : env.defeqs value.toDefEq)
    (hw : ∀ l ∈ ls, l.WF univs) (hl : ls.length = value.toDefEq.uvars)
    (hu : u.WF univs)
    (typeChild : StrongBounded env univs k []
      (value.toDefEq.type.instL ls) (value.toDefEq.type.instL ls) (.sort u))
    (leftClosed : StrongBounded env univs k []
      (value.toDefEq.lhs.instL ls) (value.toDefEq.lhs.instL ls) (value.toDefEq.type.instL ls))
    (rightClosed : StrongBounded env univs k []
      (value.toDefEq.rhs.instL ls) (value.toDefEq.rhs.instL ls) (value.toDefEq.type.instL ls))
    (leftChild : StrongBounded env univs k Γ
      (value.toDefEq.lhs.instL ls) (value.toDefEq.lhs.instL ls) (value.toDefEq.type.instL ls))
    (rightChild : StrongBounded env univs k Γ
      (value.toDefEq.rhs.instL ls) (value.toDefEq.rhs.instL ls) (value.toDefEq.type.instL ls))
    (H : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ (value.toDefEq.rhs.instL ls)) (proofErase Γ (value.toDefEq.rhs.instL ls))
      (proofErase Γ (value.toDefEq.type.instL ls)) (proofErase Γ (value.toDefEq.type.instL ls)) p q) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) uses
      (proofErase Γ (value.toDefEq.lhs.instL ls)) (proofErase Γ (value.toDefEq.rhs.instL ls))
      (proofErase Γ (value.toDefEq.type.instL ls)) (proofErase Γ (value.toDefEq.type.instL ls)) p q := by
  have HE := (StrongBounded.extra hdf hw hl hu typeChild leftClosed rightClosed leftChild rightChild).strong.defeq
  have hl' : ls.length = value.uvars := hl
  have E : value.toDefEq.lhs.instL ls = VExpr.const value.name ls := by
    simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hl']
  have hd := hdefs ⟨value.toDefEq, _, hdf, hw, hl, E, rfl⟩
  apply H.prefixes heq hs hc (.of_typed hΓ HE.hasType.1) (.of_typed hΓ HE.hasType.2) _ .refl
  have hleft := HE.hasType.1
  rw [E] at hleft ⊢
  exact (proofErase_pattern_step_forward hs hΓ hleft (.delta hd)).mono (fun R => .inl R)

end Lean4Lean.VEnv.Strengthening
