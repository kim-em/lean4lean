import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertBinderTransportBoundary

/-! # Interpret the two body directions independently

A directed comparison consumes only the forward variable-image requirements.
Two independently proved directions construct the existing paired interpreter.
This lets lambda abstraction consume one-sided recursive input evidence in
each action, without trying to reverse that input evidence inside the action.
General strong coverage and comparison transitivity remain open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private tree_cons_comp tree_id_comp tree_inst
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedTrees
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- One direction of a comparison, reinterpreted under arbitrary paired
typed substitutions using only forward image evidence. The right term has
its own original assignment; each run assigns both images the left carrier.
General construction from strong comparisons is not assumed. -/
structure PiInertDirectedPairInterpretation (D : Definitions) (Δ : List ProofShape)
    (uses : List (Nat × PiInertGuardedTree)) (a b T U : ProofShape)
    (p : PiInertGuardedTree) : Prop where
  left : TypedAt Δ a T
  right : TypedAt Δ b U
  run : ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
    PiInertGuardedImages D Δ Λ σ τ uses →
    PiInertGuardedTreeValue p σ D Λ (a.subst σ) (b.subst τ) (T.subst σ)

/-- Existing self interpretation supplies the directed comparison of a term
with itself, retaining its complete recursive profile. -/
theorem PiInertGuardedInterpretation.directed
    (H : PiInertGuardedInterpretation D Δ uses a T p) :
    PiInertDirectedPairInterpretation D Δ uses a a T T p :=
  ⟨H.assigned, H.assigned, H.run⟩

/-- With no image requirements, the old paired interpreter already supplies
each separate direction. Additional requested images may simply be unused. -/
theorem PiInertGuardedPairInterpretation.directed_of_empty
    (H : PiInertGuardedPairInterpretation D Δ [] a b T U p q) :
    PiInertDirectedPairInterpretation D Δ uses a b T U p :=
  ⟨H.left, H.right, fun WL WR _ => (H.run WL WR (fun _ _ h => nomatch h)).forward⟩

/-- Two separate body directions construct the existing paired interface.
Each run consumes only its own image orientation and requirement list. -/
theorem PiInertDirectedPairInterpretation.paired
    (H : PiInertDirectedPairInterpretation D Δ ls a b T U p)
    (K : PiInertDirectedPairInterpretation D Δ rs b a U T q) :
    PiInertGuardedPairInterpretation D Δ (ls ++ rs) a b T U p q := by
  refine ⟨H.left, H.right, ?_⟩
  intro Λ σ τ WL WR images
  exact ⟨H.run WL WR (fun i p hi => (images i p (List.mem_append_left _ hi)).forward),
    K.run WR WL (fun i p hi => (images i p (List.mem_append_right _ hi)).backward)⟩

/-- Directed application consumes the full one-sided recursive input tree.
Its output annotations and carrier use the left original argument, while the
right term's own actual assignment is retained separately. -/
theorem PiInertDirectedPairInterpretation.app
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HF : PiInertDirectedPairInterpretation D Δ fs f g T U (.call A B p q))
    (HX : PiInertDirectedPairInterpretation D Δ xs x y A C p)
    (HL : TypedAt Δ (.app f x) (B.inst x)) (HR : TypedAt Δ (.app g y) V) :
    PiInertDirectedPairInterpretation D Δ (fs ++ xs) (.app f x) (.app g y)
      (B.inst x) V (q.subst (.one x)) := by
  refine ⟨HL, HR, ?_⟩
  intro Λ σ τ WL WR images
  have F := HF.run WL WR (fun i p hi => images i p (List.mem_append_left _ hi))
  have X := HX.run WL WR (fun i p hi => images i p (List.mem_append_right _ hi))
  have result := F.app heq hc X (HL.sources.1.subst WL) (HR.sources.1.subst WR)
  simpa only [PiInertGuardedTreeValue.subst_iff, ProofShape.Subst.one,
    tree_cons_comp, tree_id_comp, ProofShape.subst, ProofShape.subst_inst, tree_inst] using result

/-- Directed comparison changes its complete left interface using a retained
type certificate. The new left assignment and the comparison supply the
cross assignment for the right image; no reverse semantic image is needed. -/
theorem PiInertDirectedPairInterpretation.convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertDirectedPairInterpretation D Δ uses a b T U p)
    (HT : PiInertTreeTransport D Δ p T q V)
    (HA : TypedAt Δ a V) (HB : TypedAt Δ b E) :
    PiInertDirectedPairInterpretation D Δ uses a b V E q := by
  refine ⟨HA, HB, ?_⟩
  intro Λ σ τ WL WR images
  have old := H.run WL WR images
  have AL := HA.subst WL
  exact HT WL old AL (old.base.transfer heq hs AL)

/-- A proof marker at a literal Pi supplies its call profile outright.
Application tests have an impossible typed proof-marker head, so no input
or output exposure supply is needed for this erased proof branch. -/
theorem PiInertDirectedPairInterpretation.proof_call
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HA : TypedAt Δ .proof (.forallE A B)) :
    PiInertDirectedPairInterpretation D Δ uses .proof .proof
      (.forallE A B) (.forallE A B) (.call A B p q) := by
  refine ⟨HA, HA, ?_⟩
  intro Λ σ τ WL WR images
  have HL := HA.subst WL
  simp only [ProofShape.subst] at HL ⊢
  refine ⟨⟨HL, HL, PiInertDemandBase.refl hc HL.sources.1 HL.sources.2⟩,
    ⟨0, (PiInertEvidence.of_core_join hc HL.sources.2 HL.sources.2 .refl).world_computation⟩, ?_⟩
  intro Ξ κ x y W HX HF HG
  exact HF.not_proof_app.elim

/-- Lambda congruence for two different bodies at the same written domain.
The body is reinterpreted at each paired argument substitution. Arbitrary
recursive input and output profiles are supported, with no symmetry premise
on one-sided input values and no conversion of a local history's core world.
Domain interpretation and type-only input supply remain explicit. -/
theorem PiInertDirectedPairInterpretation.lam
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u)
    (HD : PiInertGuardedInterpretation D Δ ds A (.sort u) (.plain .ground))
    (HS : PiInertGuardedSupplyInterpretation D Δ ss A p)
    (HB : PiInertDirectedPairInterpretation D (A::Δ) (p.bindUses uses) b c B B q)
    (HF : TypedAt Δ (.lam A b) (.forallE A B))
    (HG : TypedAt Δ (.lam A c) (.forallE A B)) :
    PiInertDirectedPairInterpretation D Δ (ds ++ (ss ++ uses))
      (.lam A b) (.lam A c) (.forallE A B) (.forallE A B) (.call A B p q) := by
  refine ⟨HF, HG, ?_⟩
  intro Λ σ τ WL WR images
  have domain := HD.run WL WR (fun i p hi => images i p (List.mem_append_left _ hi))
  have supply := HS.run WL WR (fun i p hi =>
    images i p (List.mem_append_right _ (List.mem_append_left _ hi)))
  have old : PiInertGuardedImages D Δ Λ σ τ uses := fun i p hi =>
    images i p (List.mem_append_right _ (List.mem_append_right _ hi))
  have SL := ContextSubstitution.sort WL S
  have SR := ContextSubstitution.sort WR S
  obtain ⟨m, HA⟩ := domain.base.ground.history
  have VL : ContextSubstitution (A::Δ) (A.subst σ :: Λ) σ.lift := WL.cons
  have VR : ContextSubstitution (A::Δ) (A.subst σ :: Λ) τ.lift :=
    ContextSubstitution.paired_lift heq hs WL WR S HA
  have body := HB.run (ContextSubstitution.eta_lift VL S) (ContextSubstitution.eta_lift VR S)
    (old.binder heq hs hc hRigid SL supply)
  have bodyBase := body.base
  rw [HB.left.sources.1.subst_etaLift S VL, HB.right.sources.1.subst_etaLift S VR,
    HB.left.sources.2.subst_etaLift S VL] at bodyBase
  have WB : ContextSubstitution (A.subst σ :: Λ) (A.subst τ :: Λ) ProofShape.Subst.id :=
    HA.binder_context heq hs SL SR
  have rightBody : TypedAt (A.subst τ :: Λ) (c.subst τ.lift) (B.subst σ.lift) := by
    simpa only [ProofShape.subst_id] using bodyBase.right.subst WB
  have rightOwn := TypedAt.lam_body
    (by simpa only [ProofShape.subst] using HG.sources.1.subst WR) rightBody
  have right := rightOwn.pi_domain heq hs SL SR domain.base.ground
  have left := HF.subst WL
  obtain ⟨n, history⟩ := bodyBase.ground.history
  have testL := PiInertEvidence.raw_lambda_test (n := n) hs hc S HF.sources.1
  have testR := PiInertEvidence.raw_lambda_test (n := n) hs hc S HG.sources.1
  have HL := testL.substitute VL
  have HR := testR.substitute VR
  simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst] at HL HR
  have ground := (history.prefixes HL.world_computation HR.world_computation).function heq hs hc SL
  refine ⟨⟨left, ?_, ?_⟩, ⟨0, ?_⟩, ?_⟩
  · simpa only [ProofShape.subst] using right
  · exact ⟨HF.sources.1.subst WL, HG.sources.1.subst WR, HF.sources.2.subst WL, n, ground⟩
  · exact (PiInertEvidence.of_core_join hc left.sources.2 left.sources.2 .refl).world_computation
  · intro Ξ κ x y W HX HLeft HRight
    have PL : ContextSubstitution Δ Ξ (σ.comp κ) := ContextSubstitution.comp WL W.typed
    have PR : ContextSubstitution Δ Ξ (τ.comp κ) := ContextSubstitution.comp WR W.typed
    simp only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] at HLeft HRight ⊢
    have BL : ContextSubstitution (A::Δ) Ξ ((σ.comp κ).cons x) :=
      ContextSubstitution.lambda_argument PL HLeft
    have BR : ContextSubstitution (A::Δ) Ξ ((τ.comp κ).cons y) :=
      ContextSubstitution.lambda_argument PR HRight
    have result := HB.run BL BR ((old.move W).cons_pair HX)
    have FL := left.subst W.typed
    have FR := right.subst W.typed
    simp only [ProofShape.subst_subst, ProofShape.subst, ← ProofShape.Subst.comp_lift] at FL FR
    obtain ⟨TX, TL⟩ := FL.app_parts HLeft
    have TR := FR.app_result_left heq hs TX (p := .ground) HX.base.ground HRight
    rw [tree_inst] at TL TR
    have beta (body : ProofShape) (υ : ProofShape.Subst) (z : ProofShape) :
        Compute (ErasedLevelCore D)
          (.app (.lam (A.subst υ) (body.subst υ.lift)) z) (body.subst (υ.cons z)) :=
      tree_inst body υ z ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := A.subst υ))
    exact result.prefixes heq hs hc TL TR (beta b (σ.comp κ) x) (beta c (τ.comp κ) y)

/-- Independent body directions construct both complete lambda interfaces.
Each orientation may use a different recursive input/output profile and
different finite image requirements. No input value is symmetrized here. -/
theorem pi_inert_paired_lambdas_of_directed_bodies
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u)
    (HD : PiInertGuardedInterpretation D Δ ds A (.sort u) (.plain .ground))
    (HL : PiInertGuardedSupplyInterpretation D Δ ls A p)
    (HR : PiInertGuardedSupplyInterpretation D Δ rs A r)
    (HB : PiInertDirectedPairInterpretation D (A::Δ) (p.bindUses bs) b c B B q)
    (HC : PiInertDirectedPairInterpretation D (A::Δ) (r.bindUses cs) c b B B s)
    (HF : TypedAt Δ (.lam A b) (.forallE A B))
    (HG : TypedAt Δ (.lam A c) (.forallE A B)) :
    PiInertGuardedPairInterpretation D Δ ((ds ++ (ls ++ bs)) ++ (ds ++ (rs ++ cs)))
      (.lam A b) (.lam A c) (.forallE A B) (.forallE A B)
      (.call A B p q) (.call A B r s) :=
  (HB.lam heq hs hc hRigid S HD HL HF HG).paired
    (HC.lam heq hs hc hRigid S HD HR HG HF)

/-- The same-domain lamDF branch consumes the two directional
interpretations of its original body child, with unrestricted recursive
profiles. Both directions concern that rank-k child; no rank-(k+1) strong
symmetry reconstruction is submitted to an induction hypothesis. Domain
interpretation and both input supplies are still required. Different written
domains and general construction of these hypotheses remain open. The erased
proof branch constructs both calls directly and needs no body action. -/
theorem StrongBounded.paired_lam_same_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (domainChild : StrongBounded env univs k Γ A A (.sort u))
    (bodyType : StrongBounded env univs k (A::Γ) B B (.sort v))
    (bodyChild : StrongBounded env univs k (A::Γ) b c B)
    (HD : PiInertGuardedInterpretation D (proofEraseCtx Γ) ds (proofErase Γ A)
      (.sort u) (.plain .ground))
    (HL : PiInertGuardedSupplyInterpretation D (proofEraseCtx Γ) ls (proofErase Γ A) p)
    (HR : PiInertGuardedSupplyInterpretation D (proofEraseCtx Γ) rs (proofErase Γ A) r)
    (HB : PiInertDirectedPairInterpretation D (proofEraseCtx (A::Γ)) (p.bindUses bs)
      (proofErase (A::Γ) b) (proofErase (A::Γ) c)
      (proofErase (A::Γ) B) (proofErase (A::Γ) B) q)
    (HC : PiInertDirectedPairInterpretation D (proofEraseCtx (A::Γ)) (r.bindUses cs)
      (proofErase (A::Γ) c) (proofErase (A::Γ) b)
      (proofErase (A::Γ) B) (proofErase (A::Γ) B) s) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ)
      ((ds ++ (ls ++ bs)) ++ (ds ++ (rs ++ cs)))
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam A c))
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A B))
      (.call (proofErase Γ A) (proofErase (A::Γ) B) p q)
      (.call (proofErase Γ A) (proofErase (A::Γ) B) r s) := by
  have hA := domainChild.strong.defeq.hasType.1
  have hB := bodyType.strong.defeq.hasType.1
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HE := (StrongBounded.lamDF (hA.sort_r henv hΓ) (hB.sort_r henv hΓA)
    domainChild bodyType bodyType bodyChild bodyChild).strong.defeq
  have ET : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))
  by_cases hn : IsProof Γ (.lam A b)
  · have hn' := (isProof_congr hΓ HE).1 hn
    have HA := TypedAt.of_typed hΓ HE.hasType.1
    rw [proofErase_eq_proof.2 hn, ET] at HA
    rw [proofErase_eq_proof.2 hn, proofErase_eq_proof.2 hn', ET]
    exact (PiInertDirectedPairInterpretation.proof_call hc HA).paired
      (PiInertDirectedPairInterpretation.proof_call hc HA)
  have hn' := mt (isProof_congr hΓ HE).2 hn
  have EL : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A::Γ) b) := if_neg hn
  have ER : proofErase Γ (.lam A c) = .lam (proofErase Γ A) (proofErase (A::Γ) c) := if_neg hn'
  have FL := TypedAt.of_typed hΓ HE.hasType.1
  have FR := TypedAt.of_typed hΓ HE.hasType.2
  rw [EL, ET] at FL
  rw [ER, ET] at FR
  rw [EL, ER, ET]
  exact pi_inert_paired_lambdas_of_directed_bodies heq hs hc hRigid (.of_typed hΓ hA)
    HD HL HR HB HC FL FR

end Lean4Lean.VEnv.Strengthening
