import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRankedUnitOrigin

/-! # Type transport at original ranks and arbitrary selected carriers

A type equality's conversion child need not be assigned a literal universe.
Keep ordinary sort typing separately from its original strong derivation.
Bidirectional typed transport then handles symmetry and transitivity without
new strong proofs, and conversion reuses its original term child unchanged.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Both directions of ground transport, with actual new endpoint assignments
as in TreeTransport. This does not require histories for untyped operands. -/
structure PiInertGroundTypeEquiv (D : Definitions) (Γ : List VExpr) (A B : VExpr) : Prop where
  forward : PiInertTreeTransport D (proofEraseCtx Γ)
    (.plain .ground) (proofErase Γ A) (.plain .ground) (proofErase Γ B)
  backward : PiInertTreeTransport D (proofEraseCtx Γ)
    (.plain .ground) (proofErase Γ B) (.plain .ground) (proofErase Γ A)

/-- Identity needs no semantic type comparison. -/
theorem PiInertGroundTypeEquiv.refl : PiInertGroundTypeEquiv D Γ A A :=
  ⟨PiInertTreeTransport.refl, PiInertTreeTransport.refl⟩

/-- Reverse the retained directions, without reconstructing a strong proof. -/
theorem PiInertGroundTypeEquiv.symm (H : PiInertGroundTypeEquiv D Γ A B) :
    PiInertGroundTypeEquiv D Γ B A := ⟨H.backward, H.forward⟩

/-- Actual equalities supply intermediate assignments in each orientation.
Only the semantic certificates are composed, not term comparisons. -/
theorem PiInertGroundTypeEquiv.trans
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HBC : env.IsDefEq univs Γ B C (.sort u))
    (H : PiInertGroundTypeEquiv D Γ A B) (K : PiInertGroundTypeEquiv D Γ B C) :
    PiInertGroundTypeEquiv D Γ A C :=
  ⟨PiInertTreeTransport.trans_typed hΓ HAB H.forward K.forward,
    PiInertTreeTransport.trans_typed hΓ HBC.symm K.backward H.backward⟩

/-- Existing carrier transport supplies the two typed directions. -/
theorem PiInertGroundTypeEquiv.of_carrier
    (H : PiInertCarrierTransport D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B)) :
    PiInertGroundTypeEquiv D Γ A B :=
  ⟨PiInertTreeTransport.ground H, PiInertTreeTransport.ground H.symm⟩

/-- An ordinary core join constructs both directions independently of the
selected type of the original strong equality. -/
theorem PiInertGroundTypeEquiv.of_core_join
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort u))
    (J : ComputeJoin (ErasedLevelCore D) (proofErase Γ A) (proofErase Γ B)) :
    PiInertGroundTypeEquiv D Γ A B :=
  .of_carrier (PiInertCarrierTransport.of_core_join hs hc ⟨Γ, A, _, hΓ, rfl, hA, rfl⟩
    ⟨Γ, B, _, hΓ, rfl, hB, rfl⟩ J)

/-- The remaining original constructors in the sorted transport induction.
Each constructor supplies the original rule premises at their original rank.
These cases are obligations, not a claimed smaller strengthening frontier. -/
inductive StrongBounded.TypeTransportPrincipal :
    {k : Nat} → {Γ : List VExpr} → {a b T : VExpr} →
      StrongBounded env univs k Γ a b T → Prop where
  | appDF : TypeTransportPrincipal (.appDF h1 h2 h3 h4 h5 h6 h7)
  | projDF : TypeTransportPrincipal (.projDF h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)
  | forallEDF : TypeTransportPrincipal (.forallEDF h1 h2 h3 h4 h5)
  | pat : TypeTransportPrincipal (.pat h1 h2 h3 h4 h5 h6)

/-- Missing principal cases for a well-founded induction, with sort typing
separate from the selected carrier. The lower handler covers original ranks
strictly below the current node, in any well-formed context. It never asks for
a bound on reconstructed universe conversion or context substitution. It does
not itself supply term interpreters for nonsorted arguments, paired lambda
action, or index histories for erased proof majors. Those remain substantive
requirements when attempting the four cases. -/
def PiInertSortedTransportCases (D : Definitions) : Prop :=
  ∀ {k Γ a b T u} (H : StrongBounded env univs k Γ a b T),
    H.TypeTransportPrincipal → OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a (.sort u) →
    (∀ {j Ξ x y C v}, j < k → OnCtx Ξ (env.IsType univs) →
      StrongBounded env univs j Ξ x y C → env.HasType univs Ξ x (.sort v) →
      PiInertGroundTypeEquiv D Ξ x y) → PiInertGroundTypeEquiv D Γ a b

/-- All original constructors except the four explicitly named principal
cases are discharged. In particular defeqDF uses the original term child at
its possibly nonliteral universe alias. Sorts, constants, beta, stored delta
and constructor projections use ordinary core joins; proof, lambda and
structure inhabitant cases contradict sorting. The closed quotient equation
also has a lambda left endpoint and is excluded only at this sorted root.
This is a sufficient induction interface, not proof of its remaining cases. -/
theorem StrongBounded.sorted_ground_transport
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hdefs : ∀ {c ls rhs}, (Definitions.ofEnv env univs henv).unfolds c ls rhs →
      D.unfolds c ls rhs)
    (cases : PiInertSortedTransportCases D)
    (H : StrongBounded env univs bound Γ a b T)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ a (.sort u)) :
    PiInertGroundTypeEquiv D Γ a b := by
  induction bound using Nat.strongRecOn generalizing Γ a b T u with
  | ind bound ih =>
    have lower {j Ξ x y C v} (hj : j < bound) (hΞ : OnCtx Ξ (env.IsType univs))
        (K : StrongBounded env univs j Ξ x y C) (hx : env.HasType univs Ξ x (.sort v)) :=
      ih j hj K hΞ hx
    have hB := (H.strong.defeq.toU.of_l henv hΓ hA).hasType.2
    cases H with
    | bvar => exact .refl
    | symm K => exact (lower (Nat.lt_succ_self _) hΓ K hB).symm
    | trans L R =>
      have HL := L.strong.defeq.toU.of_l henv hΓ hA
      have HR := R.strong.defeq.toU.of_l henv hΓ HL.hasType.2
      exact .trans hΓ HL HR
        (lower (Nat.lt_succ_self _) hΓ L hA)
        (lower (Nat.lt_succ_self _) hΓ R HL.hasType.2)
    | raise hj K => exact lower hj hΓ K hA
    | defeqDF hu HT K => exact lower (Nat.lt_succ_self _) hΓ K hA
    | sortDF hu hv he =>
      apply PiInertGroundTypeEquiv.of_core_join hs hc hΓ hA hB
      simp only [proofErase, if_neg (not_isProof_of_sort hΓ hA),
        if_neg (not_isProof_of_sort hΓ hB)]
      exact .of_compute (.base (.inr (.sort he hv)))
    | constDF h1 h2 h3 h4 h5 h6 h7 h8 =>
      apply PiInertGroundTypeEquiv.of_core_join hs hc hΓ hA hB
      simp only [proofErase, if_neg (not_isProof_of_sort hΓ hA),
        if_neg (not_isProof_of_sort hΓ hB)]
      exact .of_compute (.base (.inr (.const h5 h3)))
    | beta =>
      exact .of_core_join hs hc hΓ hA hB
        (.of_compute (.beta (proofErase_beta_forward hΓ hA .beta)))
    | proofIrrel hp hx hy =>
      exact (not_isProof_of_sort hΓ hA ⟨_, hx.strong.defeq, hp.strong.defeq⟩).elim
    | lamDF | eta =>
      obtain ⟨_, HE, _⟩ := hA.lam_inv_forallE henv hΓ
      exact (HE.symm.sort_forallE_inv henv hΓ).elim
    | structEta hi hp hx hm hn =>
      have HE := hA.uniqU henv hΓ hn.strong.defeq.hasType.1
      exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
        (HE.typeChain henv hΓ (HasType.sort (hA.sort_r henv hΓ)))).elim
    | unitLike hi hp hx hf hm hn =>
      have HE := hA.uniqU henv hΓ hm.strong.defeq.hasType.1
      exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi)
        (HE.typeChain henv hΓ (HasType.sort (hA.sort_r henv hΓ)))).elim
    | appDF h1 h2 h3 h4 h5 h6 h7 =>
      exact cases (.appDF h1 h2 h3 h4 h5 h6 h7)
        (.appDF (h1 := h1) (h2 := h2) (h3 := h3) (h4 := h4) (h5 := h5)
          (h6 := h6) (h7 := h7)) hΓ hA lower
    | projDF h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      exact cases (.projDF h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12)
        (.projDF (h1 := h1) (h2 := h2) (h3 := h3) (h4 := h4) (h5 := h5)
          (h6 := h6) (h7 := h7) (h8 := h8) (h9 := h9) (h10 := h10)
          (h11 := h11) (h12 := h12)) hΓ hA lower
    | forallEDF h1 h2 h3 h4 h5 =>
      exact cases (.forallEDF h1 h2 h3 h4 h5)
        (.forallEDF (h1 := h1) (h2 := h2) (h3 := h3) (h4 := h4) (h5 := h5)) hΓ hA lower
    | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      obtain ⟨ds, hwf⟩ := henv
      rcases hwf.defeqs_origin h1 with rfl | ⟨value, hv, rfl⟩
      · obtain ⟨_, HE, _⟩ := hA.lam_inv_forallE henv hΓ
        exact (HE.symm.sort_forallE_inv henv hΓ).elim
      · have he {ls : List VLevel} (hl : ls.length = value.uvars) :
            value.toDefEq.lhs.instL ls = .const value.name ls := by
          simp only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id hl]
        have he := he h3
        have hd := hdefs ⟨value.toDefEq, _, h1, h2, h3, he, rfl⟩
        apply PiInertGroundTypeEquiv.of_core_join hs hc hΓ hA hB
        apply ComputeJoin.of_compute
        rw [he] at hA ⊢
        exact (proofErase_pattern_step_forward hs hΓ hA (.delta hd)).mono (fun H => .inl H)
    | pat h1 h2 h3 h4 h5 h6 =>
      exact cases (.pat h1 h2 h3 h4 h5 h6)
        (.pat (h1 := h1) (h2 := h2) (h3 := h3) (h4 := h4) (h5 := h5) (h6 := h6)) hΓ hA lower
    | projIota h1 h2 h3 h4 =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hA.proj_inv henv hΓ
      have hlen := (projection_major_family henv hΓ h1 (henv.projectionRigid h1)
        hm.hasType.2).2
      exact .of_core_join hs hc hΓ hA hB (.of_compute
        ((proofErase_pattern_step_forward hs hΓ hA (.projIota h1 hlen h3)).mono
          (fun H => .inl H)))

/-- The completed induction would supply the current conversion consumer's
exact contract. No universe reassignment is inserted into the strong proof. -/
theorem PiInertSortedTransportCases.ground_coverage
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hdefs : ∀ {c ls rhs}, (Definitions.ofEnv env univs henv).unfolds c ls rhs →
      D.unfolds c ls rhs)
    (H : PiInertSortedTransportCases D) : PiInertStrongGroundTreeCoverage D := by
  intro Γ k A B u hΓ HE
  exact (HE.sorted_ground_transport hs hc hdefs H hΓ HE.strong.defeq.hasType.1).forward

/-- Unrestricted coverage also covers an independently sorted equality at an
arbitrary selected carrier. Reassignment and symmetry may increase rank here:
this lemma calibrates the global obligation and is not a recursive IH call. -/
theorem PiInertStrongGroundTreeCoverage.sorted_equiv
    (coverage : PiInertStrongGroundTreeCoverage D)
    (H : StrongBounded env univs k Γ a b T)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ a (.sort u)) :
    PiInertGroundTypeEquiv D Γ a b := by
  have HE := H.strong.defeq.toU.of_l henv hΓ hA
  obtain ⟨n, K⟩ := strong_has_bound (HE.strong henv.orderedStrong hΓ)
  exact ⟨coverage hΓ K, coverage hΓ (.symm K)⟩

/-- The four-case induction interface is equivalent to the current global
ground-coverage contract, given sound confluent core computation containing
stored definitions. Fewer listed constructors is not strict logical smallness. -/
theorem pi_inert_sorted_transport_cases_iff
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hdefs : ∀ {c ls rhs}, (Definitions.ofEnv env univs henv).unfolds c ls rhs →
      D.unfolds c ls rhs) :
    PiInertSortedTransportCases D ↔ PiInertStrongGroundTreeCoverage D := by
  constructor
  · exact fun H => H.ground_coverage hs hc hdefs
  · intro H k Γ a b T u K _ hΓ hA _
    exact H.sorted_equiv K hΓ hA

omit [Params] in
/-- The four remaining constructor cases still imply the full proposition
front in the actual core when a closed positive unit exists. This is a checked
lower bound on the new induction interface, not a strictly smaller frontier. -/
theorem EnvironmentCore.sorted_transport_cases_propositionFront
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {family info ls u}, env.HasCanonicalEq →
      env.projections family info → info.nparams = 0 → info.nindices = 0 → info.numFields = 0 →
      env.HasType U [] (.const family ls) (.sort (.succ u)) →
      PiInertSortedTransportCases definitions → PropositionFront := by
  letI := henv.params U
  intro family info ls u heq hi hp hx hf hS H
  exact ground_tree_coverage_propositionFront henv U heq hi hp hx hf hS
    (H.ground_coverage sound (typed_level_core_confluence (fun H => H))
      (fun H => includes_core (.inl H)))

end Lean4Lean.VEnv.Strengthening
