import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaPiComparisonEvidence

/-! # Substitution-stable interpreted evidence for recursive synthesis

The induction hypothesis need not reconstruct an older syntactic certificate
after each derived rule. It retains the proved interpretation at one fixed stage,
including every future interpreted substitution. No completeness assumption is
made for arbitrary equality derivations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A particular computation or comparison and its interpretation after every
typed substitution. Each component is evidence to construct, not an oracle for
all semantic equalities or all substitutions of arbitrary checker certificates. -/
structure PiInertEvidence (D : Definitions) (stage : Nat) (kind : CoreFamilyKind)
    (Δ : List ProofShape) (a b : ProofShape) : Prop where
  base : PiInertInterpret D stage kind Δ a b
  future : ∀ {Δ' τ}, ContextSubstitution Δ Δ' τ →
    PiInertInterpret D stage kind Δ' (a.subst τ) (b.subst τ)

/-- The existing hereditary syntactic certificates construct the interpreted
induction evidence at their exact stage. No additional future-closure premise
is inferred for non-hereditary certificates. -/
theorem CoreFamilyCast.Hereditary.pi_inert_evidence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast.Hereditary D stage kind Δ a b) : PiInertEvidence D stage kind Δ a b :=
  ⟨H.base.pi_inert_interpret heq hs hl hcon hc hreg hoff hD,
    fun W => (H.future W).pi_inert_interpret heq hs hl hcon hc hreg hoff hD⟩

/-- Future substitutions compose while preserving the same stage. -/
theorem PiInertEvidence.substitute (H : PiInertEvidence D stage kind Δ a b)
    (W : ContextSubstitution Δ Δ' τ) : PiInertEvidence D stage kind Δ' (a.subst τ) (b.subst τ) := by
  refine ⟨H.future W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.future (W.comp V)

/-- Actual typed substitution supplies evidence for the actual substituted
terms, with erasure reconstruction rather than a native image assumption. -/
theorem PiInertEvidence.typed_substitute
    (H : PiInertEvidence D stage kind (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B) :
    PiInertEvidence D stage kind (proofEraseCtx Γ₀)
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have ES : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES]
  exact H.substitute (ContextSubstitution.of_typed hΓ₀ W ES)

/-- Comparison symmetry needs no new computation or stage bound. -/
theorem PiInertEvidence.symm (H : PiInertEvidence D stage (.compare mode) Δ a b) :
    PiInertEvidence D stage (.compare mode) Δ b a :=
    by
  refine ⟨fun RA RB => (H.base RB RA).symm, ?_⟩
  intro Δ' τ W a' b' RA RB
  exact (H.future W RB RA).symm

/-- Sequential computation uses the retained ordinary-core output tail to
invoke the next interpretation. -/
theorem PiInertInterpret.trans (H : PiInertInterpret D stage .compute Δ a b)
    (K : PiInertInterpret D stage .compute Δ b c) : PiInertInterpret D stage .compute Δ a c := by
  refine ⟨K.1, ?_⟩
  intro a' RA
  obtain ⟨middle, RL, RM⟩ := H.2 RA
  obtain ⟨shared, RT, RR⟩ := K.2 RM
  exact ⟨shared, RL.trans RT, RR⟩

/-- Computation composition also retains every future substitution. -/
theorem PiInertEvidence.trans (H : PiInertEvidence D stage .compute Δ a b)
    (K : PiInertEvidence D stage .compute Δ b c) : PiInertEvidence D stage .compute Δ a c :=
  ⟨H.base.trans K.base, fun W => (H.future W).trans (K.future W)⟩

/-- Joining two computation outputs uses ordinary core confluence at their
retained typed common output, not confluence of the guarded stage. -/
theorem PiInertInterpret.join (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertInterpret D stage .compute Δ a shared)
    (K : PiInertInterpret D stage .compute Δ b shared) : PiInertInterpret D stage (.compare mode) Δ a b := by
  intro a' b' RA RB
  obtain ⟨left, RL, CL⟩ := H.2 RA
  obtain ⟨right, RR, CR⟩ := K.2 RB
  obtain ⟨Γ, e, T, hΓ, _, ht, EE⟩ := H.1
  obtain ⟨joined, JL, JR⟩ := hc hΓ ht (EE ▸ CL) (EE ▸ CR)
  exact .compute (RL.trans JL.in_pi_inert_stage) (RR.trans JR.in_pi_inert_stage) (.leaf .refl)

/-- Common-output joins retain future evidence in either checking mode. -/
theorem PiInertEvidence.join (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertEvidence D stage .compute Δ a shared)
    (K : PiInertEvidence D stage .compute Δ b shared) : PiInertEvidence D stage (.compare mode) Δ a b :=
  ⟨H.base.join hc K.base, fun W => (H.future W).join hc (K.future W)⟩

/-- Retaining full-core residuals also retains their future substituted paths.
This applies to derived evidence as well as the original grammar. -/
theorem PiInertEvidence.reducts
    (H : PiInertEvidence D stage (.compare mode) Δ a b)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertEvidence D stage (.compare mode) Δ a' b' := by
  refine ⟨fun SA SB => H.base (RA.trans SA) (RB.trans SB), ?_⟩
  intro Δ' τ W a'' b'' SA SB
  exact H.future W ((RA.subst (fun R => erased_level_core_subst R)).trans SA)
    ((RB.subst (fun R => erased_level_core_subst R)).trans SB)

/-- Whole-Pi evidence yields substitution-stable common domain evidence at
the same stage. No native representation or domain history is assumed. -/
theorem PiInertEvidence.pi_domains
    (H : PiInertEvidence D stage (.compare mode) Δ (.forallE A B) (.forallE C E)) :
    PiInertEvidence D stage (.compare true) Δ A C := by
  refine ⟨?_, ?_⟩
  · intro X Y RA RC
    exact (H.base (.forallE RA .refl) (.forallE RC .refl)).pi_domains_of_no_pi
      (fun R => pi_inert_stage_no_pi R)
  · intro Δ' τ W X Y RA RC
    exact (H.future W (.forallE RA .refl) (.forallE RC .refl)).pi_domains_of_no_pi
      (fun R => pi_inert_stage_no_pi R)

end Lean4Lean.VEnv.Strengthening
