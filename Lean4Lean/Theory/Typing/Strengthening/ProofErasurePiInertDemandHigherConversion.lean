import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandPredicateConversion

/-! # Higher-order predicate conversion at assigned argument types

Actual raw assignments can share fixed non-proof representatives. This makes
universe-interface conversion usable inside a higher-order call. The selected
argument carriers must still expose literal Pis; arbitrary outer aliases and
full strong demand coverage are not proved here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
variable [Params] {D : Definitions}

/-- A non-proof raw assignment can use any fixed actual representative of its
endpoint in a context with the same erasure. Reflection aligns the terms,
while the assigned type is retained exactly at the raw level. -/
theorem ProofShape.TypedAt.realize_term
    (H : TypedAt (proofEraseCtx Γ) e T) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (Ea : proofErase Γ a = e) (hn : e ≠ .proof) :
    ∃ B, env.HasType univs Γ a B ∧ proofErase Γ B = T := by
  obtain ⟨b, B, hb, Eb, EB⟩ := H.realize hΓ
  have hna : ¬ IsProof Γ a := fun hp => hn (Ea.symm.trans (proofErase_eq_proof.2 hp))
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ ha hb (Ea.trans Eb.symm)).2 hna
  exact ⟨B, ((HE.defeq hΓ).of_r henv hΓ hb).hasType.1, EB⟩

/-- An assigned function interface returning a literal universe cannot erase
to the proof marker. No non-proof hypothesis is needed from the caller. -/
theorem ProofShape.TypedAt.function_to_sort_ne_proof
    (H : TypedAt Δ e (.forallE K (.sort u))) : e ≠ .proof := by
  obtain ⟨Γ, a, A, hΓ, _, ha, Ea, EA⟩ := H
  obtain ⟨C, E, rfl, _, _, EE⟩ := erase_forallE_inv EA
  obtain rfl := erase_sort_inv EE
  intro h
  exact not_isProof_function_to_sort hΓ ha (proofErase_eq_proof.1 (Ea.trans h))

/-- Universe-interface conversion works directly on assigned raw arguments
in arbitrary worlds. The function interface supplies a non-proof witness;
all selected type annotations remain those of the original assignments. -/
theorem PiInertDemandValue.assigned_universe_interface_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hfOld : TypedAt Δ f (.forallE A B))
    (hfNew : TypedAt Δ f (.forallE C E))
    (hgNew : TypedAt Δ g (.forallE C E))
    (hfTypes : TypedAt Δ f (.forallE (.sort v) (.sort u)))
    (H : PiInertDemandValue (.arrow p q) D Δ f g (.forallE A B)) :
    PiInertDemandValue (.arrow r s) D Δ f g (.forallE C E) := by
  have hnf := hfTypes.function_to_sort_ne_proof
  obtain ⟨Γ, f₀, F, hΓ, rfl, hf₀, Ef, EF⟩ := hfOld
  obtain ⟨A₀, B₀, rfl, _, _, _⟩ := erase_forallE_inv EF
  obtain ⟨T, hfT, ET⟩ := hfNew.realize_term hΓ hf₀ Ef hnf
  obtain ⟨C₀, E₀, rfl, _, _, _⟩ := erase_forallE_inv ET
  obtain ⟨g₀, G, hg₀, Eg, EG⟩ := hgNew.realize hΓ
  obtain ⟨_, hG⟩ := hg₀.isType henv hΓ
  obtain ⟨_, hT⟩ := hfT.isType henv hΓ
  obtain ⟨_, eqGT⟩ := (proofErase_reflect hΓ hG hT (EG.trans ET.symm)).2
    (not_isProof_of_sort hΓ hG)
  have hgT := hg₀.defeqU_r henv hΓ (eqGT.defeq hΓ)
  obtain ⟨K, hfK, EK⟩ := hfTypes.realize_term hΓ hf₀ Ef hnf
  obtain ⟨V, U, rfl, _, EV, EU⟩ := erase_forallE_inv EK
  obtain rfl := erase_sort_inv EV
  obtain rfl := erase_sort_inv EU
  rw [← Ef, ← Eg, ← EF] at H
  rw [← Ef, ← Eg, ← ET]
  exact H.universe_interface_convert heq hs hc hRigid hΓ hf₀ hfT hgT hfK

/-- Predicate result transport exposes the argument assignments at the old,
new and reference interfaces. This supports recursive input conversion on
higher-order operands without asking a callback to recover those typings. -/
theorem PiInertDemandValue.predicate_interface_convert_assigned
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
      TypedAt Λ x ((proofErase Γ A).subst σ) → TypedAt Λ y ((proofErase Γ A).subst σ) →
      TypedAt Λ x ((proofErase Γ K).subst σ) → TypedAt Λ y ((proofErase Γ K).subst σ) →
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
  have hgOld := hgNew.defeqU_r henv hΓ (hfOld.uniqU henv hΓ hfNew).symm
  have oldRight := (TypedAt.of_typed hΓ hgOld).subst W.typed
  have oldTyped := (TypedAt.of_typed hΓ hfOld).subst W.typed
  have newTyped := (TypedAt.of_typed hΓ hfNew).subst W.typed
  have newRight := (TypedAt.of_typed hΓ hgNew).subst W.typed
  have typeLeft := (TypedAt.of_typed hΓ hfTypes).subst W.typed
  have typeRight := (TypedAt.of_typed hΓ hgTypes).subst W.typed
  have value := H.move W
  simp only [EPold, EPnew, EPtypes, ProofShape.subst] at oldRight oldTyped newTyped newRight typeLeft typeRight value
  obtain ⟨TX, TL⟩ := newTyped.app_parts HL
  obtain ⟨TY, _⟩ := newRight.app_parts HR
  obtain ⟨KX, CL⟩ := typeLeft.app_parts HL
  obtain ⟨KY, CR⟩ := typeRight.app_parts HR
  obtain ⟨OX, OL⟩ := oldTyped.app_parts HL
  have OY := (oldRight.app_parts HR).1
  have arg := input W OX OY KX KY TX TY HX
  have result := value.app heq hc arg HL HR OL.sources.2
  exact result.sorted_reindex heq hs CL.sort_domain CR.sort_domain OL TL.sources.2

/-- Predicates over type-valued functions construct both conversion components.
The source and target argument carriers expose literal Pis, whose annotations
may differ arbitrarily. The reference input is universe-to-universe. Input
conversion reverses direction and recursively invokes its checked interface;
no subsingleton or supplied component-transport hypothesis is used. -/
theorem PiInertDemandValue.higher_predicate_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hfOld : env.HasType univs Γ f (.forallE (.forallE A B) F))
    (hfNew : env.HasType univs Γ f (.forallE (.forallE C E) G))
    (hgNew : env.HasType univs Γ g (.forallE (.forallE C E) G))
    (hfTypes : env.HasType univs Γ f
      (.forallE (.forallE (.sort v) (.sort u)) (.sort w)))
    (H : PiInertDemandValue (.arrow (.arrow p q) t) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE (.forallE A B) F))) :
    PiInertDemandValue (.arrow (.arrow r s) z) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE (.forallE C E) G)) := by
  obtain ⟨_, hOld⟩ := hfOld.isType henv hΓ
  obtain ⟨⟨_, hAB⟩, _⟩ := hOld.forallE_inv henv.ordered
  obtain ⟨_, hNew⟩ := hfNew.isType henv hΓ
  obtain ⟨⟨_, hCE⟩, _⟩ := hNew.forallE_inv henv.ordered
  obtain ⟨_, hRef⟩ := hfTypes.isType henv hΓ
  obtain ⟨⟨_, hVU⟩, _⟩ := hRef.forallE_inv henv.ordered
  obtain ⟨⟨v', hV⟩, ⟨_, hU⟩⟩ := hVU.forallE_inv henv.ordered
  have EAB : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hAB)
  have ECE : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) := if_neg (not_isProof_of_sort hΓ hCE)
  have EVU : proofErase Γ (.forallE (.sort v) (.sort u)) =
      .forallE (.sort v) (.sort u) := by
    have EP : proofErase Γ (.forallE (.sort v) (.sort u)) =
        .forallE (proofErase Γ (.sort v)) (proofErase (.sort v :: Γ) (.sort u)) :=
      if_neg (not_isProof_of_sort hΓ hVU)
    rw [EP, show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ hV),
      show proofErase (.sort v :: Γ) (.sort u) = .sort u from
        if_neg (not_isProof_of_sort (show OnCtx (.sort v :: Γ) (env.IsType univs) from ⟨hΓ, v', hV⟩) hU)]
  apply H.predicate_interface_convert_assigned heq hs hc hRigid hΓ hfOld hfNew hgNew hfTypes
  intro Λ σ x y _ OX OY KX _ TX _ HX
  simp only [EAB, ECE, EVU, ProofShape.subst] at OX OY KX TX HX ⊢
  exact HX.assigned_universe_interface_convert heq hs hc hRigid TX OX OY KX

/-- The higher-order predicate case consumes the original conversion-rule
children. The retained term payload has an arrow demand for its function
argument, allowing the contravariant inner conversion to run. -/
theorem StrongBounded.demand_convert_higher_predicate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ
      (.forallE (.forallE A B) F) (.forallE (.forallE C E) G) (.sort v'))
    (termChild : StrongBounded env univs k Γ f g (.forallE (.forallE A B) F))
    (hfTypes : env.HasType univs Γ f
      (.forallE (.forallE (.sort v) (.sort u)) (.sort w)))
    (H : PiInertDemandValue (.arrow (.arrow p q) t) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE (.forallE A B) F))) :
    PiInertDemandValue (.arrow (.arrow r s) z) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE (.forallE C E) G)) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  exact H.higher_predicate_convert heq hs hc hRigid hΓ HT.hasType.1
    (HE.defeq HT.hasType.1) (HE.defeq HT.hasType.2) hfTypes

/-- The assigned predicate rule exposes all three input assignments in an
arbitrary erased context. This is the interface used by recursive conversion;
it does not assume that semantic carrier equality is an ordinary-core join. -/
theorem PiInertDemandValue.assigned_predicate_interface_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hfOld : TypedAt Δ f (.forallE A B))
    (hfNew : TypedAt Δ f (.forallE C E))
    (hgNew : TypedAt Δ g (.forallE C E))
    (hfTypes : TypedAt Δ f (.forallE K (.sort u)))
    (H : PiInertDemandValue (.arrow p q) D Δ f g (.forallE A B))
    (input : ∀ {Λ σ x y}, PiInertCoreWorld D Δ Λ σ →
      TypedAt Λ x (A.subst σ) → TypedAt Λ y (A.subst σ) →
      TypedAt Λ x (K.subst σ) → TypedAt Λ y (K.subst σ) →
      TypedAt Λ x (C.subst σ) → TypedAt Λ y (C.subst σ) →
      PiInertDemandValue r D Λ x y (C.subst σ) →
      PiInertDemandValue p D Λ x y (A.subst σ)) :
    PiInertDemandValue (.arrow r s) D Δ f g (.forallE C E) := by
  have hnf := hfTypes.function_to_sort_ne_proof
  obtain ⟨Γ, f₀, F, hΓ, rfl, hf₀, Ef, EF⟩ := hfOld
  obtain ⟨A₀, B₀, rfl, _, EA, _⟩ := erase_forallE_inv EF
  obtain ⟨T, hfT, ET⟩ := hfNew.realize_term hΓ hf₀ Ef hnf
  obtain ⟨C₀, E₀, rfl, _, EC, _⟩ := erase_forallE_inv ET
  obtain ⟨g₀, G, hg₀, Eg, EG⟩ := hgNew.realize hΓ
  obtain ⟨_, hG⟩ := hg₀.isType henv hΓ
  obtain ⟨_, hT⟩ := hfT.isType henv hΓ
  obtain ⟨_, eqGT⟩ := (proofErase_reflect hΓ hG hT (EG.trans ET.symm)).2
    (not_isProof_of_sort hΓ hG)
  have hgT := hg₀.defeqU_r henv hΓ (eqGT.defeq hΓ)
  obtain ⟨K, hfK, EK⟩ := hfTypes.realize_term hΓ hf₀ Ef hnf
  obtain ⟨V, U, rfl, _, EV, EU⟩ := erase_forallE_inv EK
  obtain rfl := erase_sort_inv EU
  rw [← Ef, ← Eg, ← EF] at H
  rw [← Ef, ← Eg, ← ET]
  apply H.predicate_interface_convert_assigned heq hs hc hRigid hΓ hf₀ hfT hgT hfK
  intro Λ σ x y W OX OY KX KY TX TY HX
  simp only [EA, EC, EV] at OX OY KX KY TX TY HX ⊢
  exact input W OX OY KX KY TX TY HX

/-- A finite hierarchy of type-valued interfaces. A level-zero operand is a
type; a successor operand consumes the preceding level and returns a type.
There is no fixed bound on higher-order nesting. -/
inductive PiInertPredicateTower : Nat → ProofShape → Prop where
  | sort : PiInertPredicateTower 0 (.sort u)
  | function : PiInertPredicateTower n A → PiInertPredicateTower (n+1) (.forallE A (.sort u))

/-- Selected carriers expose the Pi structure required by a tower. At level
zero any carrier annotation is permitted; each successor codomain is also
arbitrary. The selected carrier need not equal the reference interface. -/
inductive PiInertPredicateCarrier : Nat → ProofShape → Prop where
  | base : PiInertPredicateCarrier 0 T
  | function : PiInertPredicateCarrier n A → PiInertPredicateCarrier (n+1) (.forallE A B)

/-- The finite demand sufficient for conversion at each interface level. -/
def PiInertDemand.predicateTower : Nat → PiInertDemand
  | 0 => .ground
  | n+1 => .arrow (predicateTower n) .ground

omit [Params] in
/-- Reference tower shape persists in every substitution, including beneath
binders; no semantic type equality or normalization is used. -/
theorem PiInertPredicateTower.subst (H : PiInertPredicateTower n T) (σ : ProofShape.Subst) :
    PiInertPredicateTower n (T.subst σ) := by
  induction H generalizing σ with
  | sort => exact .sort
  | function H ih => exact .function (ih σ)

omit [Params] in
/-- The selected Pi exposure condition persists through future worlds. -/
theorem PiInertPredicateCarrier.subst (H : PiInertPredicateCarrier n T) (σ : ProofShape.Subst) :
    PiInertPredicateCarrier n (T.subst σ) := by
  induction H generalizing σ with
  | base => exact .base
  | function H ih => exact .function (ih σ)

/-- Recursive demand conversion at every finite predicate-tower level.
The induction is on the reference interface, never on a transformed strong
derivation. Both selected carriers expose the necessary Pi domains, while
all leaf annotations and selected codomains may be arbitrary actual aliases.
General outer exposure and completeness of source demands remain open. -/
theorem PiInertPredicateTower.convert_subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HR : PiInertPredicateTower n R) (σ : ProofShape.Subst)
    (HA : PiInertPredicateCarrier n A) (HB : PiInertPredicateCarrier n B)
    (hfOld : TypedAt Δ f A) (hfNew : TypedAt Δ f B) (hgNew : TypedAt Δ g B)
    (hfRef : TypedAt Δ f (R.subst σ)) (hgRef : TypedAt Δ g (R.subst σ))
    (H : PiInertDemandValue (.predicateTower n) D Δ f g A) :
    PiInertDemandValue (.predicateTower n) D Δ f g B := by
  induction HR generalizing σ Δ f g A B with
  | sort =>
    exact H.sorted_reindex heq hs hfRef.sort_domain hgRef.sort_domain hfOld hfNew.sources.2
  | function HR ih =>
    cases HA with
    | function HA =>
      cases HB with
      | function HB =>
        apply H.assigned_predicate_interface_convert heq hs hc hRigid hfOld hfNew hgNew hfRef
        intro Λ τ x y _ OX OY KX KY TX _ HX
        simp only [ProofShape.subst_subst] at KX KY
        exact ih (σ.comp τ) (HB.subst τ) (HA.subst τ) TX OX OY KX KY HX

/-- The substitution-stable tower conversion theorem at the original
interface. Its selected-carrier shape and source-demand assumptions remain
explicit; it is not a completeness theorem for arbitrary typed functions. -/
theorem PiInertPredicateTower.convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HR : PiInertPredicateTower n R)
    (HA : PiInertPredicateCarrier n A) (HB : PiInertPredicateCarrier n B)
    (hfOld : TypedAt Δ f A) (hfNew : TypedAt Δ f B) (hgNew : TypedAt Δ g B)
    (hfRef : TypedAt Δ f R) (hgRef : TypedAt Δ g R)
    (H : PiInertDemandValue (.predicateTower n) D Δ f g A) :
    PiInertDemandValue (.predicateTower n) D Δ f g B := by
  have Hf : TypedAt Δ f (R.subst ProofShape.Subst.id) := by simpa only [ProofShape.subst_id] using hfRef
  have Hg : TypedAt Δ g (R.subst ProofShape.Subst.id) := by simpa only [ProofShape.subst_id] using hgRef
  exact HR.convert_subst heq hs hc hRigid .id HA HB hfOld hfNew hgNew Hf Hg H

/-- Tower interfaces are outside the structural-subsingleton carrier class
at every level. This separates their input-conversion mechanism from the
previous empty-structure case without claiming semantic non-subsingletonness. -/
theorem PiInertPredicateTower.not_subsingleton (H : PiInertPredicateTower n R) :
    ¬ SubsingletonCarrier R := by
  intro HS
  cases H with
  | sort => exact HS.not_sort rfl
  | function => exact HS.pi_body.not_sort rfl

/-- Original strong conversion children support the entire finite tower
hierarchy. The actual reference typing supplies both endpoint interfaces by
ordinary uniqueness. No strong derivation is transformed for recursion. -/
theorem StrongBounded.demand_convert_predicate_tower
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ A B (.sort v))
    (termChild : StrongBounded env univs k Γ f g A)
    (hfRef : env.HasType univs Γ f R)
    (HR : PiInertPredicateTower n (proofErase Γ R))
    (HA : PiInertPredicateCarrier n (proofErase Γ A))
    (HB : PiInertPredicateCarrier n (proofErase Γ B))
    (H : PiInertDemandValue (.predicateTower n) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ A)) :
    PiInertDemandValue (.predicateTower n) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ B) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  have hgRef := HT.hasType.2.defeqU_r henv hΓ (HT.hasType.1.uniqU henv hΓ hfRef)
  exact HR.convert heq hs hc hRigid HA HB (TypedAt.of_typed hΓ HT.hasType.1)
    (TypedAt.of_typed hΓ (HE.defeq HT.hasType.1))
    (TypedAt.of_typed hΓ (HE.defeq HT.hasType.2))
    (TypedAt.of_typed hΓ hfRef) (TypedAt.of_typed hΓ hgRef) H

end Lean4Lean.VEnv.Strengthening
