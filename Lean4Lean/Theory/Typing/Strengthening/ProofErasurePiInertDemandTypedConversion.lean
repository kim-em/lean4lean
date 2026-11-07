import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandConversion

/-! # Demand conversion at actual function calls

Argument/result transports need only cover operands and results with their
actual selected typings. This weaker interface admits a proved case for
functions consuming and returning types even when the alternate domains and
codomains are not related by ordinary-core joins.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private weak_subst from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandBinders
variable [Params] {D : Definitions}

/-- An actual raw application assigns its argument the function's selected
domain and assigns the whole application the selected dependent result.
Reflection and ordinary Pi injectivity align the actual representatives. -/
theorem ProofShape.TypedAt.app_parts (H : TypedAt Δ f (.forallE A B))
    (HX : TypedSource Δ (.app f x)) : TypedAt Δ x A ∧ TypedAt Δ (.app f x) (B.inst x) := by
  obtain ⟨Γ, t, T, hΓ, EΓ, ht, Et⟩ := HX
  obtain ⟨g, y, rfl, hn, Eg, Ey⟩ := erase_app_inv Et
  obtain ⟨C, E, hg, hy⟩ := ht.app_inv henv hΓ
  obtain ⟨f₀, F, hf₀, Ef₀, EF⟩ := (EΓ ▸ H).realize hΓ
  obtain ⟨A₀, B₀, rfl, _, EA, EB⟩ := erase_forallE_inv EF
  have hng : ¬ IsProof Γ g := fun hp => hn (IsProof.app_fn hΓ hg hy hp)
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hg hf₀ (Eg.trans Ef₀.symm)).2 hng
  have hg' := ((HE.defeq hΓ).of_r henv hΓ hf₀).hasType.1
  obtain ⟨⟨_, HD⟩, _, _⟩ := (hg.uniqU henv hΓ hg').forallE_inv henv hΓ
  have hy' := hy.defeqU_r henv hΓ HD.toU
  obtain ⟨_, hPi⟩ := hf₀.isType henv hΓ
  obtain ⟨⟨u, hA⟩, ⟨_, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A₀::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  refine ⟨⟨Γ, y, A₀, hΓ, EΓ, hy', Ey, EA⟩,
    ⟨Γ, .app g y, B₀.inst y, hΓ, EΓ, hg'.app hy', Et, ?_⟩⟩
  simpa only [EA, EB, Ey] using proofErase_instN hΓA hy' Ctx.InstN.zero hB

/-- Assigned typing at a literal raw universe gives a domain-sort witness
for the endpoint itself. This follows from erasure shape inversion. -/
theorem ProofShape.TypedAt.sort_domain (H : TypedAt Δ a (.sort u)) : DomainSort Δ a u := by
  obtain ⟨Γ, e, T, hΓ, EΓ, he, Ee, ET⟩ := H
  obtain rfl := erase_sort_inv ET
  exact ⟨Γ, e, hΓ, EΓ, he, Ee⟩

/-- Universe-assigned operands admit any target carrier and finite profile
once a ground payload is present. Actual assignments supply the sortedness
which independent raw source witnesses alone would not establish. -/
theorem PiInertDemandValue.assigned_sort_transfer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HA : TypedAt Δ a (.sort u)) (HB : TypedAt Δ b (.sort u))
    (HT : TypedSource Δ T) (H : PiInertDemandValue p D Δ a b (.sort u)) :
    PiInertDemandValue q D Δ a b T :=
  H.sorted_reindex heq hs HA.sort_domain HB.sort_domain HA HT

/-- Typed application action at a literal Pi constructs its own ground
history by testing the fresh argument. The resulting finite arrow demand
retains every core-world future and every core alias of the selected Pi.
There is no supplied ground equality between the functions. -/
theorem PiInertDemandValue.function_of_typed_calls
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hfNew : env.HasType univs Γ f (.forallE C E))
    (hgNew : env.HasType univs Γ g (.forallE C E))
    (run : ∀ {Λ σ x y}, PiInertCoreWorld D (proofEraseCtx Γ) Λ σ →
      PiInertDemandValue r D Λ x y ((proofErase Γ C).subst σ) →
      TypedSource Λ (.app ((proofErase Γ f).subst σ) x) →
      TypedSource Λ (.app ((proofErase Γ g).subst σ) y) →
      PiInertDemandValue s D Λ (.app ((proofErase Γ f).subst σ) x)
        (.app ((proofErase Γ g).subst σ) y) (((proofErase (C::Γ) E).subst σ.lift).inst x)) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  have TF := TypedAt.of_typed hΓ hfNew
  have TG := TypedAt.of_typed hΓ hgNew
  by_cases hp : IsProof Γ f
  · have hgp := isProof_of_common_type hΓ hfNew hgNew hp
    have HT := TF.sources.2
    have HF := TF.sources.1
    rw [proofErase_eq_proof.2 hp] at HF
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hgp]
    exact pi_inert_proof_demand_value hc HF HT
  have hng : ¬ IsProof Γ g := fun hgp => hp (isProof_of_common_type hΓ hgNew hfNew hgp)
  obtain ⟨_, hPiNew⟩ := hfNew.isType henv hΓ
  obtain ⟨⟨u, hC⟩, ⟨v, hE⟩⟩ := hPiNew.forallE_inv henv.ordered
  have EPnew : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) := if_neg (not_isProof_of_sort hΓ hPiNew)
  have SC := DomainSort.of_typed hΓ hC
  have W := PiInertCoreWorld.weakening (D := D) heq hc SC
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have hFresh (a : VExpr) (ha : env.HasType univs Γ a (.forallE C E)) :
      env.HasType univs (C::Γ) (.app a.lift (.bvar 0)) E := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar, VExpr.inst] using
      HasType.app (ha.weak henv) (.bvar .zero)
  have freshSource (a : VExpr) (ha : env.HasType univs Γ a (.forallE C E))
      (hn : ¬ IsProof Γ a) :
      TypedSource (proofErase Γ C :: proofEraseCtx Γ)
        (.app ((proofErase Γ a).liftN 1) (etaArgument u)) :=
    ⟨C::Γ, .app a.lift (.bvar 0), E, hΓC, rfl, hFresh a ha, proofErase_eta_body hΓ hC ha hn⟩
  have HC : PiInertDemandValue r D (proofErase Γ C :: proofEraseCtx Γ)
      (etaArgument u) (etaArgument u) ((proofErase Γ C).subst (fun i => .bvar (i+1))) := by
    simpa only [weak_subst] using pi_inert_fresh_demand_value heq hs hc hRigid SC
  have body := run W HC
    (by simpa only [weak_subst] using freshSource f hfNew hp)
    (by simpa only [weak_subst] using freshSource g hgNew hng)
  have HE : TypedSource (proofErase Γ C :: proofEraseCtx Γ) (proofErase (C::Γ) E) :=
    ⟨C::Γ, E, .sort v, hΓC, rfl, hE, rfl⟩
  rw [HE.fresh_inst heq hc SC] at body
  simp only [weak_subst] at body
  obtain ⟨n, history⟩ := body.base.history
  have ground := history.function heq hs hc SC
  rw [EPnew]
  refine ⟨⟨TF.sources.1, TG.sources.1, EPnew ▸ TF.sources.2, n, ground⟩, ?_⟩
  intro Λ σ C' E' x y V HP J HX HL HR HResult
  simp only [ProofShape.subst] at J
  obtain ⟨JD, JB⟩ := J.level_core_pi_parts
  have HCS : TypedSource (proofEraseCtx Γ) (proofErase Γ C) := ⟨Γ, C, _, hΓ, rfl, hC, rfl⟩
  have result := run V (HX.core_join hs hc (HCS.subst V.typed) JD.symm) HL HR
  have JE : ComputeJoin (ErasedLevelCore D)
      (((proofErase (C::Γ) E).subst σ.lift).inst x) (E'.inst x) := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      JB.subst (fun R => erased_level_core_subst R) (σ := ProofShape.Subst.one x)
  exact result.core_join hs hc HResult JE


/-- Function conversion only needs transports for actually assigned operands
and application results. Whole application typing supplies those assignments.
The two dependent result carriers use the corresponding arguments separately;
no equality of the raw result types is assumed. General construction of these
typed components remains open outside the proved cases below. -/
theorem PiInertDemandValue.function_convert_typed
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hfOld : env.HasType univs Γ f (.forallE A B))
    (hfNew : env.HasType univs Γ f (.forallE C E))
    (hgNew : env.HasType univs Γ g (.forallE C E))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE A B)))
    (input : ∀ {Λ σ x y}, PiInertCoreWorld D (proofEraseCtx Γ) Λ σ →
      TypedAt Λ x ((proofErase Γ C).subst σ) → TypedAt Λ y ((proofErase Γ C).subst σ) →
      PiInertDemandValue r D Λ x y ((proofErase Γ C).subst σ) →
      PiInertDemandValue p D Λ x y ((proofErase Γ A).subst σ))
    (output : ∀ {Λ σ x y a b}, PiInertCoreWorld D (proofEraseCtx Γ) Λ σ →
      TypedAt Λ a (((proofErase (A::Γ) B).subst σ.lift).inst x) →
      TypedAt Λ b (((proofErase (A::Γ) B).subst σ.lift).inst y) →
      TypedAt Λ a (((proofErase (C::Γ) E).subst σ.lift).inst x) →
      TypedAt Λ b (((proofErase (C::Γ) E).subst σ.lift).inst y) →
      PiInertDemandValue q D Λ a b (((proofErase (A::Γ) B).subst σ.lift).inst x) →
      PiInertDemandValue s D Λ a b (((proofErase (C::Γ) E).subst σ.lift).inst x)) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  apply PiInertDemandValue.function_of_typed_calls heq hs hc hRigid hΓ hfNew hgNew
  intro Λ σ x y W HX HL HR
  have TF := TypedAt.of_typed hΓ hfNew
  have TG := TypedAt.of_typed hΓ hgNew
  obtain ⟨_, hPiOld⟩ := hfOld.isType henv hΓ
  obtain ⟨_, hPiNew⟩ := hfNew.isType henv hΓ
  have EPold : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPiOld)
  have EPnew : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) := if_neg (not_isProof_of_sort hΓ hPiNew)
  have hgOld := hgNew.defeqU_r henv hΓ (hfOld.uniqU henv hΓ hfNew).symm
  have oldTyped := (TypedAt.of_typed hΓ hfOld).subst W.typed
  have oldRight := (TypedAt.of_typed hΓ hgOld).subst W.typed
  have newTyped := TF.subst W.typed
  have newRight := TG.subst W.typed
  have value := H.move W
  simp only [EPold, EPnew, ProofShape.subst] at oldTyped oldRight newTyped newRight value
  obtain ⟨TX, TL⟩ := newTyped.app_parts HL
  obtain ⟨TY, TR⟩ := newRight.app_parts HR
  have OL := (oldTyped.app_parts HL).2
  have OR := (oldRight.app_parts HR).2
  exact output W OL OR TL TR
    (value.app heq hc (input W TX TY HX) HL HR OL.sources.2)

/-- A function which returns types at the source Pi and takes types at the
target Pi admits every target finite arrow profile. The alternate source
domain and target codomain may be arbitrary actually assigned expressions;
there is no core-join premise and no residual argument/result transport oracle.
This theorem assumes the source arrow demand, not general demand completeness. -/
theorem PiInertDemandValue.type_function_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hfOld : env.HasType univs Γ f (.forallE A (.sort u)))
    (hfNew : env.HasType univs Γ f (.forallE (.sort v) E))
    (hgNew : env.HasType univs Γ g (.forallE (.sort v) E))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE A (.sort u)))) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE (.sort v) E)) := by
  obtain ⟨_, hPiOld⟩ := hfOld.isType henv hΓ
  obtain ⟨⟨w, hA⟩, ⟨_, hB⟩⟩ := hPiOld.forallE_inv henv.ordered
  obtain ⟨_, hPiNew⟩ := hfNew.isType henv hΓ
  obtain ⟨⟨_, hC⟩, _⟩ := hPiNew.forallE_inv henv.ordered
  have ES : proofErase Γ (.sort v) = .sort v := if_neg (not_isProof_of_sort hΓ hC)
  have EB : proofErase (A::Γ) (.sort u) = .sort u :=
    if_neg (not_isProof_of_sort (show OnCtx (A::Γ) (env.IsType univs) from ⟨hΓ, w, hA⟩) hB)
  apply H.function_convert_typed heq hs hc hRigid hΓ hfOld hfNew hgNew
  · intro Λ σ x y W TX TY HX
    simp only [ES, ProofShape.subst] at TX TY HX
    have HA : TypedSource (proofEraseCtx Γ) (proofErase Γ A) := ⟨Γ, A, _, hΓ, rfl, hA, rfl⟩
    exact HX.assigned_sort_transfer heq hs TX TY (HA.subst W.typed)
  · intro Λ σ x y a b _ OL OR TL _ HV
    simp only [EB, ProofShape.subst, ProofShape.inst] at OL OR HV
    exact HV.assigned_sort_transfer heq hs OL OR TL.sources.2

/-- The original rank-k strong children construct type-function conversion
without any supplied component transport. Only the source term child's arrow
demand remains an induction payload. This covers a source Pi returning a
universe and a target Pi accepting one, with arbitrary alternate annotations. -/
theorem StrongBounded.demand_convert_type_function
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ
      (.forallE A (.sort u)) (.forallE (.sort v) E) (.sort w))
    (termChild : StrongBounded env univs k Γ f g (.forallE A (.sort u)))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE A (.sort u)))) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE (.sort v) E)) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  exact H.type_function_convert heq hs hc hRigid hΓ HT.hasType.1
    (HE.defeq HT.hasType.1) (HE.defeq HT.hasType.2)

/-- A common universe-to-universe typing constructs conversion between any
two actually assigned literal Pis. Their domain/codomain annotations can be
arbitrary aliases, including dependent codomains. Actual application typing
at the common interface proves that arguments and results are types, so both
component transports are constructed without a core-join premise. -/
theorem PiInertDemandValue.universe_interface_convert
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hfOld : env.HasType univs Γ f (.forallE A B))
    (hfNew : env.HasType univs Γ f (.forallE C E))
    (hgNew : env.HasType univs Γ g (.forallE C E))
    (hfTypes : env.HasType univs Γ f (.forallE (.sort v) (.sort u)))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE A B))) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  apply PiInertDemandValue.function_of_typed_calls heq hs hc hRigid hΓ hfNew hgNew
  intro Λ σ x y W HX HL HR
  have hgTypes := hgNew.defeqU_r henv hΓ (hfTypes.uniqU henv hΓ hfNew).symm
  obtain ⟨_, hPiOld⟩ := hfOld.isType henv hΓ
  obtain ⟨⟨w, hA⟩, _⟩ := hPiOld.forallE_inv henv.ordered
  obtain ⟨_, hPiNew⟩ := hfNew.isType henv hΓ
  obtain ⟨_, hPiTypes⟩ := hfTypes.isType henv hΓ
  obtain ⟨⟨z, hV⟩, ⟨_, hU⟩⟩ := hPiTypes.forallE_inv henv.ordered
  have EPold : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPiOld)
  have EPnew : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) := if_neg (not_isProof_of_sort hΓ hPiNew)
  have EPtypes : proofErase Γ (.forallE (.sort v) (.sort u)) = .forallE (.sort v) (.sort u) := by
    have EP : proofErase Γ (.forallE (.sort v) (.sort u)) =
        .forallE (proofErase Γ (.sort v)) (proofErase (.sort v :: Γ) (.sort u)) :=
      if_neg (not_isProof_of_sort hΓ hPiTypes)
    rw [EP, show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ hV),
      show proofErase (.sort v :: Γ) (.sort u) = .sort u from
        if_neg (not_isProof_of_sort (show OnCtx (.sort v :: Γ) (env.IsType univs) from ⟨hΓ, z, hV⟩) hU)]
  have oldTyped := (TypedAt.of_typed hΓ hfOld).subst W.typed
  have newTyped := (TypedAt.of_typed hΓ hfNew).subst W.typed
  have typeLeft := (TypedAt.of_typed hΓ hfTypes).subst W.typed
  have typeRight := (TypedAt.of_typed hΓ hgTypes).subst W.typed
  have value := H.move W
  simp only [EPold, EPnew, EPtypes, ProofShape.subst] at oldTyped newTyped typeLeft typeRight value
  obtain ⟨TX, TL⟩ := newTyped.app_parts HL
  obtain ⟨CX, CL⟩ := typeLeft.app_parts HL
  obtain ⟨CY, CR⟩ := typeRight.app_parts HR
  have OL := (oldTyped.app_parts HL).2
  have HA : TypedSource (proofEraseCtx Γ) (proofErase Γ A) := ⟨Γ, A, _, hΓ, rfl, hA, rfl⟩
  have arg := HX.sorted_reindex (q := p) heq hs CX.sort_domain CY.sort_domain TX (HA.subst W.typed)
  have result := value.app heq hc arg HL HR OL.sources.2
  exact result.sorted_reindex heq hs CL.sort_domain CR.sort_domain OL TL.sources.2

/-- Original strong conversion children and an actual universe interface
suffice for arbitrary alternative Pi annotations. Only the original term
child's source demand is retained; no argument/result transport is assumed. -/
theorem StrongBounded.demand_convert_universe_interface
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ (.forallE A B) (.forallE C E) (.sort w))
    (termChild : StrongBounded env univs k Γ f g (.forallE A B))
    (hfTypes : env.HasType univs Γ f (.forallE (.sort v) (.sort u)))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE A B))) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  exact H.universe_interface_convert heq hs hc hRigid hΓ HT.hasType.1
    (HE.defeq HT.hasType.1) (HE.defeq HT.hasType.2) hfTypes

end Lean4Lean.VEnv.Strengthening
