import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCoreEndpointInterpretation

/-! # The original application rule, including erased whole proofs

Nonproof applications consume recursive function and argument interpretations.
Proof-marker applications instead need exactly the visible call exposures of
the output tree; they have no typed application tests. Native dependent result
instances are retained separately before selected-carrier conversion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Only the visible call exposures of a recursive tree. At a call this does
not demand any supply for inputs or later outputs; a proof marker cannot be
applied by a typed raw test. Intersections retain both visible requirements. -/
def PiInertGuardedRootSupply : PiInertGuardedTree → ProofShape.Subst →
    Definitions → List ProofShape → ProofShape → Prop
  | .plain _, _, _, _, _ => True
  | .both p q, ρ, D, Δ, T =>
      PiInertGuardedRootSupply p ρ D Δ T ∧ PiInertGuardedRootSupply q ρ D Δ T
  | .call A B _ _, ρ, D, Δ, T =>
      ∃ n, PiInertWorldComputation D n Δ T (.forallE (A.subst ρ) (B.subst ρ.lift))

/-- A full type-only supply includes the visible exposures. -/
theorem PiInertGuardedTreeSupply.root
    (H : PiInertGuardedTreeSupply p ρ D Δ T) : PiInertGuardedRootSupply p ρ D Δ T := by
  induction p with
  | plain => trivial
  | both p q ihp ihq => exact ⟨ihp H.1, ihq H.2⟩
  | call => exact H.1

/-- At a typed proof marker, visible exposures are both necessary and
sufficient for the entire recursive value. No later output supply or function
action is hidden in the reverse implication. -/
theorem pi_inert_proof_guarded_tree_iff_root
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (HA : TypedAt Δ .proof T) :
    PiInertGuardedTreeValue p ρ D Δ .proof .proof T ↔ PiInertGuardedRootSupply p ρ D Δ T := by
  induction p with
  | plain => exact ⟨fun _ => trivial, fun _ =>
      ⟨HA, HA, pi_inert_proof_demand_value hc HA.sources.1 HA.sources.2⟩⟩
  | both p q ihp ihq => exact and_congr ihp ihq
  | call A B p q =>
    refine ⟨fun H => H.2.1, fun R => ?_⟩
    refine ⟨⟨HA, HA, PiInertDemandBase.refl hc HA.sources.1 HA.sources.2⟩, R, ?_⟩
    intro Λ σ x y W HX HL HR
    exact HL.not_proof_app.elim

/-- Visible exposures reinterpreted under the same paired environments and
one-sided image requirements as directed term interpretation. -/
structure PiInertRootSupplyInterpretation (D : Definitions) (Δ : List ProofShape)
    (uses : List (Nat × PiInertGuardedTree)) (T : ProofShape) (p : PiInertGuardedTree) : Prop where
  run : ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
    PiInertGuardedImages D Δ Λ σ τ uses → PiInertGuardedRootSupply p σ D Λ (T.subst σ)

/-- Ordinary demand outputs have no visible guarded exposure obligation. -/
theorem PiInertRootSupplyInterpretation.plain :
    PiInertRootSupplyInterpretation D Δ uses T (.plain p) := ⟨fun _ _ _ => trivial⟩

/-- Existing full supply can discharge the weaker proof-marker requirement. -/
theorem PiInertGuardedSupplyInterpretation.root
    (H : PiInertGuardedSupplyInterpretation D Δ uses T p) :
    PiInertRootSupplyInterpretation D Δ uses T p :=
  ⟨fun WL WR images => (H.run WL WR images).root⟩

/-- Visible exposure interpretation constructs a directed proof comparison
under arbitrary paired substitutions. The two proof markers need no relation
between their substitution maps. -/
theorem PiInertRootSupplyInterpretation.proof_directed
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertRootSupplyInterpretation D Δ uses T p) (HA : TypedAt Δ .proof T) :
    PiInertDirectedPairInterpretation D Δ uses .proof .proof T T p := by
  refine ⟨HA, HA, ?_⟩
  intro Λ σ τ WL WR images
  have HL := HA.subst WL
  simp only [ProofShape.subst] at HL ⊢
  exact (pi_inert_proof_guarded_tree_iff_root hc HL).2 (H.run WL WR images)

/-- Additional image requirements may be ignored. The original run and both
recursive interfaces are unchanged. -/
theorem PiInertGuardedPairInterpretation.weaken_uses
    (H : PiInertGuardedPairInterpretation D Δ uses a b T U p q)
    (incl : ∀ i r, (i, r) ∈ uses → (i, r) ∈ more) :
    PiInertGuardedPairInterpretation D Δ more a b T U p q :=
  ⟨H.left, H.right, fun WL WR images => H.run WL WR (fun i r hi => images i r (incl i r hi))⟩

/-- The original appDF case retains the native dependent result on each side.
Nonproof applications consume the full recursive inputs. Whole applications
that erase to proofs use only visible output exposures. All original strong
children remain at rank k; general construction of their interpretations and
of visible exposures is not assumed. -/
theorem StrongBounded.paired_app_native
    (heq : env.HasCanonicalEq)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs) (hv : v.WF univs)
    (domainChild : StrongBounded env univs k Γ A A (.sort u))
    (bodyType : StrongBounded env univs k (A::Γ) B B (.sort v))
    (functionChild : StrongBounded env univs k Γ f g (.forallE A B))
    (argumentChild : StrongBounded env univs k Γ x y A)
    (resultChild : StrongBounded env univs k Γ (B.inst x) (B.inst y) (.sort v))
    (HF : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) fs
      (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A B))
      (.call (proofErase Γ A) (proofErase (A::Γ) B) p q)
      (.call (proofErase Γ A) (proofErase (A::Γ) B) r s))
    (HX : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) xs
      (proofErase Γ x) (proofErase Γ y) (proofErase Γ A) (proofErase Γ A) p r)
    (SL : PiInertRootSupplyInterpretation D (proofEraseCtx Γ) ls
      (proofErase Γ (B.inst x)) (q.subst (.one (proofErase Γ x))))
    (SR : PiInertRootSupplyInterpretation D (proofEraseCtx Γ) rs
      (proofErase Γ (B.inst y)) (s.subst (.one (proofErase Γ y)))) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) ((fs ++ xs) ++ (ls ++ rs))
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y))
      (proofErase Γ (B.inst x)) (proofErase Γ (B.inst y))
      (q.subst (.one (proofErase Γ x))) (s.subst (.one (proofErase Γ y))) := by
  have hA := domainChild.strong.defeq.hasType.1
  have hB := bodyType.strong.defeq.hasType.1
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HE := (StrongBounded.appDF hu hv domainChild bodyType functionChild argumentChild resultChild).strong.defeq
  have hx := argumentChild.strong.defeq.hasType.1
  have hy := argumentChild.strong.defeq.hasType.2
  have hright := HasType.app functionChild.strong.defeq.hasType.2 hy
  have FL := TypedAt.of_typed hΓ HE.hasType.1
  have FR := TypedAt.of_typed hΓ hright
  by_cases hp : IsProof Γ (.app f x)
  · have hp' := (isProof_congr hΓ HE).1 hp
    rw [proofErase_eq_proof.2 hp] at FL
    rw [proofErase_eq_proof.2 hp'] at FR
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    exact (((SL.proof_directed hc FL).right_assignment FR).paired
      ((SR.proof_directed hc FR).right_assignment FL)).weaken_uses
      (fun i p hi => List.mem_append_right _ hi)
  have hp' := mt (isProof_congr hΓ HE).2 hp
  have EL : proofErase Γ (.app f x) = .app (proofErase Γ f) (proofErase Γ x) := if_neg hp
  have ER : proofErase Γ (.app g y) = .app (proofErase Γ g) (proofErase Γ y) := if_neg hp'
  have ETL := proofErase_instN hΓA hx Ctx.InstN.zero hB
  have ETR := proofErase_instN hΓA hy Ctx.InstN.zero hB
  rw [EL, ETL] at FL
  rw [ER, ETR] at FR
  rw [EL, ER, ETL, ETR]
  exact (HF.app heq hc HX FL FR).weaken_uses (fun i p hi => List.mem_append_left _ hi)

/-- The ground appDF result has the rule's common selected carrier on both
sides. Its original result-type child supplies reverse transport from B[y]
to B[x] at rank k below k+1. Ordinary ground outputs need no added exposure
supply or image requirements, even when the whole application is a proof.
Function and argument interpretations remain the simultaneous IH inputs. -/
theorem StrongBounded.paired_app_ground_of_lower
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs) (hv : v.WF univs)
    (domainChild : StrongBounded env univs k Γ A A (.sort u))
    (bodyType : StrongBounded env univs k (A::Γ) B B (.sort v))
    (functionChild : StrongBounded env univs k Γ f g (.forallE A B))
    (argumentChild : StrongBounded env univs k Γ x y A)
    (resultChild : StrongBounded env univs k Γ (B.inst x) (B.inst y) (.sort v))
    (HF : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) fs
      (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A B))
      (.call (proofErase Γ A) (proofErase (A::Γ) B) p (.plain .ground))
      (.call (proofErase Γ A) (proofErase (A::Γ) B) r (.plain .ground)))
    (HX : PiInertGuardedPairInterpretation D (proofEraseCtx Γ) xs
      (proofErase Γ x) (proofErase Γ y) (proofErase Γ A) (proofErase Γ A) p r)
    (lower : ∀ {j X Y w}, j < k+1 → StrongBounded env univs j Γ X Y (.sort w) →
      PiInertGroundTypeEquiv D Γ X Y) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) (fs ++ xs)
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y))
      (proofErase Γ (B.inst x)) (proofErase Γ (B.inst x)) (.plain .ground) (.plain .ground) := by
  have native := StrongBounded.paired_app_native heq hc hΓ hu hv
    domainChild bodyType functionChild argumentChild resultChild HF HX
    (ls := []) (rs := []) .plain .plain
  simp only [PiInertGuardedTree.subst, List.append_nil] at native
  have HE := (StrongBounded.appDF hu hv domainChild bodyType functionChild argumentChild resultChild).strong.defeq
  exact native.convert_trees heq hs PiInertTreeTransport.refl
    (lower (Nat.lt_succ_self _) resultChild).backward
    (.of_typed hΓ HE.hasType.1) (.of_typed hΓ HE.hasType.2)

end Lean4Lean.VEnv.Strengthening
