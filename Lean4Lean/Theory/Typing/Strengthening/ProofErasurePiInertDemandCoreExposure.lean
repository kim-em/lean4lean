import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandTreeConversion

/-! # Demand conversion through certified core exposure of selected types

Selected carriers may have arbitrary outer syntax when a typed ordinary-core
join exposes the required finite Pi tree. Assigned typings and demand action
both transport through that join. Semantic equality alone is not promoted to
a core certificate; general exposure and strong demand coverage remain open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A raw source retains at least one assigned raw carrier. -/
theorem ProofShape.TypedSource.assigned (H : TypedSource Δ e) : ∃ T, TypedAt Δ e T := by
  obtain ⟨Γ, a, A, hΓ, EΓ, ha, Ea⟩ := H
  exact ⟨proofErase Γ A, Γ, a, A, hΓ, EΓ, ha, Ea, rfl⟩

/-- A typed ordinary-core join transports an assigned carrier, including
backwards expansions. The common actual reducts are aligned by typed erasure
reflection. Neither guarded-stage confluence nor strengthening is used. -/
theorem ProofShape.TypedAt.core_join
    (hs : D.Sound env univs) (H : TypedAt Δ e T) (HU : TypedSource Δ U)
    (J : ComputeJoin (ErasedLevelCore D) T U) : TypedAt Δ e U := by
  obtain ⟨Γ, a, A, hΓ, rfl, ha, Ea, EA⟩ := H
  obtain ⟨V, HV⟩ := HU.assigned
  obtain ⟨B, C, hB, EB, _⟩ := HV.realize hΓ
  obtain ⟨_, hA⟩ := ha.isType henv hΓ
  obtain ⟨out, RA, RB⟩ := J
  obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hA rfl EA (RA.scoped (fun R => .base R))
  obtain ⟨B', HB, EB'⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hB rfl EB (RB.scoped (fun R => .base R))
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ HA.hasType.2 HB.hasType.2 (EA'.trans EB'.symm)).2
    (not_isProof_of_sort hΓ HA.hasType.2)
  have HAB := (HA.toU.trans henv hΓ (HE.defeq hΓ)).trans henv hΓ HB.toU.symm
  exact ⟨Γ, a, B, hΓ, rfl, ha.defeqU_r henv hΓ HAB, Ea, EB⟩

/-- A typed selected carrier with a certified core join to the finite Pi
exposure required by a demand. The selected syntax itself need not be a Pi.
This is a certificate to construct, not semantic equality completeness. -/
structure PiInertCoreTypeCarrier (D : Definitions) (Δ : List ProofShape)
    (p : PiInertDemand) (T : ProofShape) : Prop where
  source : TypedSource Δ T
  exposed : ∃ U, TypedSource Δ U ∧ ComputeJoin (ErasedLevelCore D) T U ∧ PiInertTypeCarrier p U

/-- Literal selected Pi trees supply exposure with a reflexive join. -/
theorem PiInertCoreTypeCarrier.literal (HT : TypedSource Δ T) (H : PiInertTypeCarrier p T) :
    PiInertCoreTypeCarrier D Δ p T := ⟨HT, T, HT, ⟨T, .refl, .refl⟩, H⟩

/-- Every typed core alias of a selected Pi tree carries its exposure. -/
theorem PiInertCoreTypeCarrier.of_join (HT : TypedSource Δ T) (HU : TypedSource Δ U)
    (J : ComputeJoin (ErasedLevelCore D) T U) (H : PiInertTypeCarrier p U) :
    PiInertCoreTypeCarrier D Δ p T := ⟨HT, U, HU, J, H⟩

/-- Exposure remains available after any interpreted typed substitution.
Unlike value histories, this certificate needs no variable-world restriction. -/
theorem PiInertCoreTypeCarrier.subst (H : PiInertCoreTypeCarrier D Δ p T)
    (W : ContextSubstitution Δ Λ σ) : PiInertCoreTypeCarrier D Λ p (T.subst σ) := by
  obtain ⟨HT, U, HU, J, HE⟩ := H
  exact ⟨HT.subst W, U.subst σ, HU.subst W,
    J.subst (fun R => erased_level_core_subst R), HE.subst σ⟩

/-- Certified exposure transports in either direction through a further
ordinary-core join. Typed confluence is only used at the middle carrier. -/
theorem PiInertCoreTypeCarrier.core_join
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertCoreTypeCarrier D Δ p T) (HV : TypedSource Δ V)
    (J : ComputeJoin (ErasedLevelCore D) T V) : PiInertCoreTypeCarrier D Δ p V := by
  obtain ⟨HT, U, HU, K, HE⟩ := H
  exact ⟨HV, U, HU, J.symm.trans_source hc HT K, HE⟩

/-- Finite-tree conversion accepts selected outer aliases with certified
core exposures. Both assigned endpoints and the full source demand move to
the exposed types; the converted demand then returns to the selected target.
No core join between the source and target carriers is required. -/
theorem PiInertTypeInterface.convert_core_exposed
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HR : PiInertTypeInterface p R)
    (HA : PiInertCoreTypeCarrier D Δ p A) (HB : PiInertCoreTypeCarrier D Δ p B)
    (hfOld : TypedAt Δ f A) (hfNew : TypedAt Δ f B) (hgNew : TypedAt Δ g B)
    (hfRef : TypedAt Δ f R) (hgRef : TypedAt Δ g R)
    (H : PiInertDemandValue p D Δ f g A) : PiInertDemandValue p D Δ f g B := by
  obtain ⟨_, A', HA', JA, EA⟩ := HA
  obtain ⟨HB, B', HB', JB, EB⟩ := HB
  have converted := HR.convert heq hs hc hRigid EA EB
    (hfOld.core_join hs HA' JA) (hfNew.core_join hs HB' JB) (hgNew.core_join hs HB' JB)
    hfRef hgRef (H.core_join hs hc HA' JA)
  exact converted.core_join hs hc HB JB.symm

/-- Original strong conversion children use exposed outer aliases with the
same finite interface. Exposure certificates are explicit; neither the type
child nor ordinary reference typing is assumed to manufacture them. -/
theorem StrongBounded.demand_convert_core_exposed_tree
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ A B (.sort v))
    (termChild : StrongBounded env univs k Γ f g A)
    (hfRef : env.HasType univs Γ f R)
    (HR : PiInertTypeInterface p (proofErase Γ R))
    (HA : PiInertCoreTypeCarrier D (proofEraseCtx Γ) p (proofErase Γ A))
    (HB : PiInertCoreTypeCarrier D (proofEraseCtx Γ) p (proofErase Γ B))
    (H : PiInertDemandValue p D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ A)) :
    PiInertDemandValue p D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ B) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  have hgRef := HT.hasType.2.defeqU_r henv hΓ (HT.hasType.1.uniqU henv hΓ hfRef)
  exact HR.convert_core_exposed heq hs hc hRigid HA HB (TypedAt.of_typed hΓ HT.hasType.1)
    (TypedAt.of_typed hΓ (HE.defeq HT.hasType.1))
    (TypedAt.of_typed hΓ (HE.defeq HT.hasType.2))
    (TypedAt.of_typed hΓ hfRef) (TypedAt.of_typed hΓ hgRef) H

/-- A typed identity-beta alias constructs its exposure certificate. Its
erasure has application syntax, so it is outside the previous literal-Pi
selected-carrier rule even when its contractum is a function type. -/
theorem PiInertCoreTypeCarrier.identity_alias
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (H : PiInertCoreTypeCarrier D (proofEraseCtx Γ) p (proofErase Γ T)) :
    let U := VExpr.app (.lam (.sort u) (.bvar 0)) T
    PiInertCoreTypeCarrier D (proofEraseCtx Γ) p (proofErase Γ U) ∧
      ∀ A B, proofErase Γ U ≠ .forallE A B := by
  obtain ⟨hU, _, RB, _⟩ := proofErase_identity_recovery_cover (Step := PiInertStage D 0) hΓ hT
  have HU : TypedSource (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam (.sort u) (.bvar 0)) T)) :=
    ⟨Γ, _, _, hΓ, rfl, hU, rfl⟩
  refine ⟨H.core_join hc HU ⟨_, .refl, .beta RB⟩, ?_⟩
  intro A B E
  have EU : proofErase Γ (.app (.lam (.sort u) (.bvar 0)) T) =
      .app (proofErase Γ (.lam (.sort u) (.bvar 0))) (proofErase Γ T) :=
    if_neg (not_isProof_of_sort hΓ hU)
  rw [EU] at E
  cases E

/-- Conversion between two actual non-Pi identity aliases constructs both
exposure certificates. The source demand is retained at the source alias;
the selected function annotations need no core join with each other. -/
theorem PiInertTypeInterface.convert_identity_aliases
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (hfOld : env.HasType univs Γ f A) (hfNew : env.HasType univs Γ f B)
    (hgNew : env.HasType univs Γ g B) (hfRef : env.HasType univs Γ f R)
    (HR : PiInertTypeInterface p (proofErase Γ R))
    (HA : PiInertTypeCarrier p (proofErase Γ A)) (HB : PiInertTypeCarrier p (proofErase Γ B))
    (H : PiInertDemandValue p D (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.app (.lam (.sort u) (.bvar 0)) A))) :
    PiInertDemandValue p D (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.app (.lam (.sort v) (.bvar 0)) B)) := by
  obtain ⟨_, EA, _, _⟩ := proofErase_identity_recovery_cover (Step := PiInertStage D 0) hΓ hA
  obtain ⟨_, EB, _, _⟩ := proofErase_identity_recovery_cover (Step := PiInertStage D 0) hΓ hB
  have HCA : PiInertCoreTypeCarrier D (proofEraseCtx Γ) p (proofErase Γ A) :=
    .literal ⟨Γ, A, _, hΓ, rfl, hA, rfl⟩ HA
  have HCB : PiInertCoreTypeCarrier D (proofEraseCtx Γ) p (proofErase Γ B) :=
    .literal ⟨Γ, B, _, hΓ, rfl, hB, rfl⟩ HB
  have hgRef := hgNew.defeqU_r henv hΓ (hfNew.uniqU henv hΓ hfRef)
  exact HR.convert_core_exposed heq hs hc hRigid
    (HCA.identity_alias hc hΓ hA).1 (HCB.identity_alias hc hΓ hB).1
    (TypedAt.of_typed hΓ (EA.symm.defeq hfOld))
    (TypedAt.of_typed hΓ (EB.symm.defeq hfNew))
    (TypedAt.of_typed hΓ (EB.symm.defeq hgNew))
    (TypedAt.of_typed hΓ hfRef) (TypedAt.of_typed hΓ hgRef) H

end Lean4Lean.VEnv.Strengthening
