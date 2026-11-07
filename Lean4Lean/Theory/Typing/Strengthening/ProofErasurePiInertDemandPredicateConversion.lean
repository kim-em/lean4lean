import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandTypedConversion

/-! # Type-valued function conversion with higher-order inputs

A type-valued interface constructs dependent-result transport independently
of the input type. Structural subsingleton domains then construct the input
component, including iterated function domains returning empty structures.
General argument transport and outer type exposure remain separate gaps.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A type-valued function interface constructs the result-transport component
for arbitrary input types. Only argument transport remains supplied, and only
for arguments with their actual target-domain assignments. Both selected Pi
annotations may otherwise be arbitrary aliases, including dependent results. -/
theorem PiInertDemandValue.predicate_interface_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hfOld : env.HasType univs Γ f (.forallE A B))
    (hfNew : env.HasType univs Γ f (.forallE C E))
    (hgNew : env.HasType univs Γ g (.forallE C E))
    (hfTypes : env.HasType univs Γ f (.forallE K (.sort u)))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE A B)))
    (input : ∀ {Λ σ x y}, PiInertCoreWorld D (proofEraseCtx Γ) Λ σ →
      TypedAt Λ x ((proofErase Γ C).subst σ) → TypedAt Λ y ((proofErase Γ C).subst σ) →
      PiInertDemandValue r D Λ x y ((proofErase Γ C).subst σ) →
      PiInertDemandValue p D Λ x y ((proofErase Γ A).subst σ)) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  apply PiInertDemandValue.function_of_typed_calls heq hs hc hRigid hΓ hfNew hgNew
  intro Λ σ x y W HX HL HR
  have hgTypes := hgNew.defeqU_r henv hΓ (hfTypes.uniqU henv hΓ hfNew).symm
  obtain ⟨_, hPiOld⟩ := hfOld.isType henv hΓ
  obtain ⟨_, hPiNew⟩ := hfNew.isType henv hΓ
  obtain ⟨_, hPiTypes⟩ := hfTypes.isType henv hΓ
  obtain ⟨⟨z, hK⟩, ⟨_, hU⟩⟩ := hPiTypes.forallE_inv henv.ordered
  have EPold : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPiOld)
  have EPnew : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) := if_neg (not_isProof_of_sort hΓ hPiNew)
  have EPtypes : proofErase Γ (.forallE K (.sort u)) = .forallE (proofErase Γ K) (.sort u) := by
    have EP : proofErase Γ (.forallE K (.sort u)) =
        .forallE (proofErase Γ K) (proofErase (K :: Γ) (.sort u)) :=
      if_neg (not_isProof_of_sort hΓ hPiTypes)
    rw [EP, show proofErase (K :: Γ) (.sort u) = .sort u from
      if_neg (not_isProof_of_sort (show OnCtx (K :: Γ) (env.IsType univs) from ⟨hΓ, z, hK⟩) hU)]
  have oldTyped := (TypedAt.of_typed hΓ hfOld).subst W.typed
  have newTyped := (TypedAt.of_typed hΓ hfNew).subst W.typed
  have newRight := (TypedAt.of_typed hΓ hgNew).subst W.typed
  have typeLeft := (TypedAt.of_typed hΓ hfTypes).subst W.typed
  have typeRight := (TypedAt.of_typed hΓ hgTypes).subst W.typed
  have value := H.move W
  simp only [EPold, EPnew, EPtypes, ProofShape.subst] at oldTyped newTyped newRight typeLeft typeRight value
  obtain ⟨TX, TL⟩ := newTyped.app_parts HL
  obtain ⟨TY, _⟩ := newRight.app_parts HR
  obtain ⟨_, CL⟩ := typeLeft.app_parts HL
  obtain ⟨_, CR⟩ := typeRight.app_parts HR
  have OL := (oldTyped.app_parts HL).2
  have arg := input W TX TY HX
  have result := value.app heq hc arg HL HR OL.sources.2
  exact result.sorted_reindex heq hs CL.sort_domain CR.sort_domain OL TL.sources.2

/-- Structural subsingleton source domains discharge argument transport for
a type-valued function. They include arbitrary iterated function domains into
empty structures, so arguments need not themselves be types or variables.
No core join or component-transport premise is required; source arrow evidence
and the ordinary type-valued interface remain explicit. -/
theorem PiInertDemandValue.subsingleton_predicate_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hfOld : env.HasType univs Γ f (.forallE A B))
    (hfNew : env.HasType univs Γ f (.forallE C E))
    (hgNew : env.HasType univs Γ g (.forallE C E))
    (hfTypes : env.HasType univs Γ f (.forallE K (.sort u)))
    (HA : SubsingletonCarrier (proofErase Γ A))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE A B))) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  obtain ⟨_, hPi⟩ := hfOld.isType henv hΓ
  obtain ⟨⟨v, hA⟩, _⟩ := hPi.forallE_inv henv.ordered
  have HT : TypedSource (proofEraseCtx Γ) (proofErase Γ A) := ⟨Γ, A, .sort v, hΓ, rfl, hA, rfl⟩
  apply H.predicate_interface_convert heq hs hc hRigid hΓ hfOld hfNew hgNew hfTypes
  intro Λ σ x y W _ _ HX
  have HV : PiInertCarrierValue D 0 Λ x y ((proofErase Γ A).subst σ) :=
    .subsingleton HX.base.leftSource HX.base.rightSource (HA.subst σ)
  exact HV.demand heq hs hc hRigid (HT.subst W.typed)

/-- The original strong conversion parent is constructed for structural
subsingleton source domains and type-valued functions. It consumes the two
original rank-k children and a retained source arrow demand, with neither
argument nor result transport left as an oracle. General domains are not
covered by the structural-subsingleton hypothesis. -/
theorem StrongBounded.demand_convert_subsingleton_predicate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ (.forallE A B) (.forallE C E) (.sort v))
    (termChild : StrongBounded env univs k Γ f g (.forallE A B))
    (hfTypes : env.HasType univs Γ f (.forallE K (.sort u)))
    (HA : SubsingletonCarrier (proofErase Γ A))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE A B))) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  exact H.subsingleton_predicate_convert heq hs hc hRigid hΓ HT.hasType.1
    (HE.defeq HT.hasType.1) (HE.defeq HT.hasType.2) hfTypes HA

/-- A fresh predicate over functions S -> S, for a closed positive empty
structure S, constructs every target arrow demand after arbitrary actual Pi
conversion. Its input is genuinely a function type: the predicate has no
universe-to-universe typing, so the preceding interface theorem cannot apply.
The native source demand is constructed, not assumed. -/
theorem pi_inert_function_input_predicate_conversion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u)))
    (r s : PiInertDemand) :
    let S := VExpr.const family ls
    let F := VExpr.forallE S S
    let T := VExpr.forallE F (.sort .zero)
    ∀ {C E}, env.IsDefEqU univs [T] T (.forallE C E) →
      (∀ v w, ¬ env.HasType univs [T] (.bvar 0) (.forallE (.sort v) (.sort w))) ∧
      PiInertDemandValue (.arrow r s) D (proofEraseCtx [T])
        (proofErase [T] (.bvar 0)) (proofErase [T] (.bvar 0)) (proofErase [T] (.forallE C E)) := by
  dsimp only
  let S := VExpr.const family ls
  let F := VExpr.forallE S S
  let T := VExpr.forallE F (.sort .zero)
  have hSΓ {Γ} : env.HasType univs Γ S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hF {Γ} : env.HasType univs Γ F (.sort (.imax (.succ u) (.succ u))) :=
    .forallE hSΓ hSΓ
  have hT {Γ} : env.HasType univs Γ T
      (.sort (.imax (.imax (.succ u) (.succ u)) (.succ .zero))) :=
    .forallE hF (.sort (by trivial))
  have hΓ : OnCtx [T] (env.IsType univs) := ⟨trivial, _, hT⟩
  have lookup : Lookup [T] 0 T := .zero
  have hf : env.HasType univs [T] (.bvar 0) T := .bvar lookup
  have hn : ¬ IsProof [T] (.bvar 0) := not_isProof_function_to_sort hΓ hf
  have EV : proofErase [T] (.bvar 0) = .bvar 0 := if_neg hn
  have EO : contextOracle (proofEraseCtx [T]) 0 = proofErase [T] T := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ lookup]
  have HV : TypedSource (proofEraseCtx [T]) (.bvar 0) :=
    ⟨[T], .bvar 0, T, hΓ, rfl, hf, EV⟩
  have HN : PiInertWorldValue D 0 (proofEraseCtx [T]) (.bvar 0) (.bvar 0) (proofErase [T] T) := by
    rw [← EO]
    exact pi_inert_native_variable_world_neutral.value HV HV
  have source : PiInertDemandValue (.arrow .ground .ground) D (proofEraseCtx [T])
      (proofErase [T] (.bvar 0)) (proofErase [T] (.bvar 0)) (proofErase [T] T) := by
    rw [EV]
    exact (PiInertCarrierValue.neutral HN).demand heq hs hc hRigid
      ⟨[T], T, _, hΓ, rfl, hT, rfl⟩
  have ES {Γ} (hΓ : OnCtx Γ (env.IsType univs)) : proofErase Γ S = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hSΓ)
  have EF : proofErase [T] F = .forallE (.const family ls) (.const family ls) := by
    have E : proofErase [T] F = .forallE (proofErase [T] S) (proofErase (S::[T]) S) :=
      if_neg (not_isProof_of_sort hΓ hF)
    rw [E, ES hΓ, ES (show OnCtx (S::[T]) (env.IsType univs) from ⟨hΓ, _, hSΓ⟩)]
  have HF : SubsingletonCarrier (proofErase [T] F) := by
    rw [EF]
    exact .forallE (.unit hi hx hz (ps := []) hp.symm)
  intro C E HE
  constructor
  · intro v w hh
    obtain ⟨⟨_, HD⟩, _, _⟩ := (hh.uniqU henv hΓ hf).forallE_inv henv hΓ
    exact HD.toU.sort_forallE_inv henv hΓ
  · have hf' := hf.defeqU_r henv hΓ HE
    exact source.subsingleton_predicate_convert heq hs hc hRigid hΓ hf hf' hf' hf HF

end Lean4Lean.VEnv.Strengthening
