import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandDerivations
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStrongBounded

/-! # Finite-demand conversion through typed function interfaces

Actual assigned typing supplies application-result sources. A function demand
can then change its selected Pi using contravariant argument transport and
covariant dependent-result transport. These components remain explicit; no
ordinary-core join is inferred from a general type equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private weak_subst from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandBinders
variable [Params] {D : Definitions}

/-- An actual typing witness relating both raw endpoint and selected carrier.
Separate TypedSource witnesses alone do not assert this relationship. -/
def ProofShape.TypedAt (Δ : List ProofShape) (e T : ProofShape) : Prop :=
  ∃ Γ a A, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.HasType univs Γ a A ∧ proofErase Γ a = e ∧ proofErase Γ A = T

/-- Actual typing retains its assigned erased carrier. -/
theorem ProofShape.TypedAt.of_typed (hΓ : OnCtx Γ (env.IsType univs))
    (h : env.HasType univs Γ a A) : TypedAt (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ A) :=
  ⟨Γ, a, A, hΓ, rfl, h, rfl, rfl⟩

/-- Assigned raw typing realizes in every actual context with the same erasure. -/
theorem ProofShape.TypedAt.realize (H : TypedAt (proofEraseCtx Γ) e T)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ a A, env.HasType univs Γ a A ∧ proofErase Γ a = e ∧ proofErase Γ A = T := by
  obtain ⟨Ξ, a, A, hΞ, EΞ, ha, Ea, EA⟩ := H
  have W := proofEraseCtx_defeq hΞ hΓ EΞ
  obtain ⟨_, hA⟩ := ha.isType henv hΞ
  exact ⟨a, A, ha.defeqDFC henv W, (proofErase_defeqCtx hΞ W ha).symm.trans Ea,
    (proofErase_defeqCtx hΞ W hA).symm.trans EA⟩

/-- Typed interpretation preserves the endpoint/carrier relationship. -/
theorem ProofShape.TypedAt.subst (H : TypedAt Δ e T) (W : ContextSubstitution Δ Λ σ) :
    TypedAt Λ (e.subst σ) (T.subst σ) := by
  obtain ⟨Γ, a, A, hΓ, EΓ, ha, Ea, EA⟩ := H
  obtain ⟨Γ₀, ρ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ EΓ
  obtain ⟨_, hA⟩ := ha.isType henv hΓ
  exact ⟨Γ₀, a.subst ρ, A.subst ρ, hΓ₀, EΓ₀, ha.subst henv.orderedStrong WS hΓ₀,
    (proofErase_subst_with hΓ₀ WS ha ES).trans (congrArg (·.subst σ) Ea),
    (proofErase_subst_with hΓ₀ WS hA ES).trans (congrArg (·.subst σ) EA)⟩

/-- Assigned typing supplies both independent source witnesses. -/
theorem ProofShape.TypedAt.sources (H : TypedAt Δ e T) : TypedSource Δ e ∧ TypedSource Δ T := by
  obtain ⟨Γ, a, A, hΓ, EΓ, ha, Ea, EA⟩ := H
  obtain ⟨u, hA⟩ := ha.isType henv hΓ
  exact ⟨⟨Γ, a, A, hΓ, EΓ, ha, Ea⟩, ⟨Γ, A, .sort u, hΓ, EΓ, hA, EA⟩⟩

/-- A whole raw application's typing and its function's assigned Pi recover
source typing for the selected dependent result. Actual erasure reflection
aligns the function representatives; ordinary Pi injectivity types its argument.
No computational equality of the native and selected domains is assumed. -/
theorem ProofShape.TypedAt.app_result (H : TypedAt Δ f (.forallE A B))
    (HX : TypedSource Δ (.app f x)) : TypedSource Δ (B.inst x) := by
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
  obtain ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A₀::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  refine ⟨Γ, B₀.inst y, .sort v, hΓ, EΓ, hB.instN henv Ctx.InstN.zero hy', ?_⟩
  simpa only [EA, EB, Ey] using proofErase_instN hΓA hy' Ctx.InstN.zero hB

/-- A raw sort witness determines the actual sort of any typed realization
of that endpoint, even if its supplied type is an unrelated syntactic alias. -/
theorem ProofShape.DomainSort.realize_type (S : DomainSort Δ e u)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = e) :
    env.HasType univs Γ a (.sort u) := by
  obtain ⟨b, hb, Eb⟩ := (EΓ ▸ S).realize hΓ
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hb ha (Eb.trans Ea.symm)).2
    (not_isProof_of_sort hΓ hb)
  exact ((HE.defeq hΓ).of_l henv hΓ hb).hasType.2

/-- A sort-typed endpoint cannot head an actually sourced raw application.
Actual uniqueness and sort/Pi disjointness rule out the application test. -/
theorem ProofShape.DomainSort.not_app_source (S : DomainSort Δ f u)
    (H : TypedSource Δ (.app f x)) : False := by
  obtain ⟨Γ, t, T, hΓ, EΓ, ht, Et⟩ := H
  obtain ⟨g, y, rfl, _, Eg, _⟩ := erase_app_inv Et
  obtain ⟨A, B, hg, _⟩ := ht.app_inv henv hΓ
  exact ((S.realize_type hΓ hg EΓ Eg).uniqU henv hΓ hg).sort_forallE_inv henv hΓ

/-- For a sorted endpoint, a ground payload supplies every finite demand.
Function tests are impossible, including after every allowed future world. -/
theorem PiInertDemandBase.sorted_demand
    (H : PiInertDemandBase D Δ a b T) (S : DomainSort Δ a u) :
    PiInertDemandValue p D Δ a b T := by
  induction p with
  | ground => exact H
  | both p q ihp ihq => exact ⟨ihp, ihq⟩
  | arrow p q =>
    refine ⟨H, ?_⟩
    intro Λ σ A B x y W HT J HX HL HR HE
    exact (ContextSubstitution.sort W.typed S).not_app_source HL |>.elim

/-- Sorted endpoints turn a carrier residual into ordinary checked comparison.
The left endpoint's actual assigned carrier is retained separately, so this
uses no accidental identification of independent raw source witnesses. -/
theorem PiInertCarrierResidual.sorted_checked
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SA : DomainSort Δ a u) (SB : DomainSort Δ b v) (HT : TypedAt Δ a T)
    (H : PiInertCarrierResidual D n Δ T a b) : PiInertInterpret D n (.compare true) Δ a b := by
  obtain ⟨Γ, x, C, hΓ, EΓ, hx, Ex, EC⟩ := HT
  have hxU := SA.realize_type hΓ hx EΓ Ex
  obtain ⟨y, hy, Ey⟩ := (EΓ ▸ SB).realize hΓ
  have HB : PiInertCarrierInterpret D n (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ x) (proofErase Γ y) := by
    intro a' b' RA RB
    simp only [EΓ, EC, Ex, Ey] at RA RB ⊢
    exact H .refl RA RB
  intro a' b' RA RB
  rw [← EΓ]
  rw [← Ex] at RA
  rw [← Ey] at RB
  exact PiInertCarrierInterpret.types_checked heq hs hΓ hxU hy hx HB RA RB

/-- Universe-valued endpoints admit any selected carrier while retaining the
same history stage and core-world futures. There is no core-join requirement
on the old/new carriers; actual assigned typing justifies reading comparison. -/
theorem PiInertWorldHistory.sorted_reindex
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SA : DomainSort Δ a u) (SB : DomainSort Δ b v) (HT : TypedAt Δ a T)
    (H : PiInertWorldHistory D n Δ T a b) : PiInertWorldHistory D n Δ U a b := by
  refine ⟨fun _ RA RB => .carrierChecked (PiInertCarrierResidual.sorted_checked heq hs SA SB HT H.base RA RB), ?_⟩
  intro Λ σ W U' a' b' RU RA RB
  exact .carrierChecked (PiInertCarrierResidual.sorted_checked heq hs
    (ContextSubstitution.sort W.typed SA) (ContextSubstitution.sort W.typed SB)
    (HT.subst W.typed) (H.future W) RA RB)

/-- The sorted conversion case preserves every finite profile and can supply
a different one. A new carrier needs source typing, but no directed guarded
computation or ordinary-core join from the old carrier is required. -/
theorem PiInertDemandValue.sorted_reindex
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SA : DomainSort Δ a u) (SB : DomainSort Δ b v) (HT : TypedAt Δ a T)
    (HU : TypedSource Δ U) (H : PiInertDemandValue p D Δ a b T) :
    PiInertDemandValue q D Δ a b U := by
  obtain ⟨n, history⟩ := H.base.history
  exact (show PiInertDemandBase D Δ a b U from
    ⟨H.base.leftSource, H.base.rightSource, HU, n, history.sorted_reindex heq hs SA SB HT⟩).sorted_demand SA

/-- A source-typed body ignores replacement of its erased fresh proof variable.
This is the exact fresh-argument substitution used in function conversion. -/
theorem ProofShape.TypedSource.fresh_inst
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (S : DomainSort Δ A u) (H : TypedSource (A::Δ) e) :
    (e.subst (ProofShape.Subst.lift (fun i => .bvar (i+1)))).inst (etaArgument u) = e := by
  obtain ⟨Γ, C, hΓ, EΓ, hC, EC⟩ := S
  have HA : TypedSource Δ A := ⟨Γ, C, .sort u, hΓ, EΓ, hC, EC⟩
  have W := PiInertCoreWorld.identity_source (D := D) heq hc HA
  have ES := H.subst_etaLift (σ := ProofShape.Subst.id) ⟨Γ, C, hΓ, EΓ, hC, EC⟩ (ContextSubstitution.cons W.typed)
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.subst_subst, ProofShape.Subst.lift_comp_one]
  change e.subst (ProofShape.Subst.id.etaLift u) = e
  rw [ES]
  simpa only [ProofShape.Subst.id_lift] using ProofShape.subst_id e

/-- Function-carrier conversion reduces to transport of the argument and
instantiated-result demands. The former is contravariant, the latter covariant.
The input/output profiles may change. Actual typing at both Pis supplies all
application sources; no core join between the Pis or their domains is assumed.
The two transport components are explicit hypotheses, not a claim of general
strong-conversion completeness. -/
theorem PiInertDemandValue.function_convert
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
      PiInertDemandValue r D Λ x y ((proofErase Γ C).subst σ) →
      PiInertDemandValue p D Λ x y ((proofErase Γ A).subst σ))
    (output : ∀ {Λ σ x a b}, PiInertCoreWorld D (proofEraseCtx Γ) Λ σ →
      TypedSource Λ (((proofErase (C::Γ) E).subst σ.lift).inst x) →
      PiInertDemandValue q D Λ a b (((proofErase (A::Γ) B).subst σ.lift).inst x) →
      PiInertDemandValue s D Λ a b (((proofErase (C::Γ) E).subst σ.lift).inst x)) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  have TF := TypedAt.of_typed hΓ hfNew
  have TG := TypedAt.of_typed hΓ hgNew
  by_cases hp : IsProof Γ f
  · have hgp := isProof_of_common_type hΓ hfNew hgNew hp
    have HT := TF.sources.2
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hgp] at H ⊢
    exact pi_inert_proof_demand_value hc H.base.leftSource HT
  have hng : ¬ IsProof Γ g := fun hgp => hp (isProof_of_common_type hΓ hgNew hfNew hgp)
  obtain ⟨_, hPiOld⟩ := hfOld.isType henv hΓ
  obtain ⟨_, hPiNew⟩ := hfNew.isType henv hΓ
  obtain ⟨⟨u, hC⟩, ⟨v, hE⟩⟩ := hPiNew.forallE_inv henv.ordered
  have EPold : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPiOld)
  have EPnew : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) := if_neg (not_isProof_of_sort hΓ hPiNew)
  have run {Λ σ x y} (W : PiInertCoreWorld D (proofEraseCtx Γ) Λ σ)
      (HX : PiInertDemandValue r D Λ x y ((proofErase Γ C).subst σ))
      (HL : TypedSource Λ (.app ((proofErase Γ f).subst σ) x))
      (HR : TypedSource Λ (.app ((proofErase Γ g).subst σ) y)) :
      PiInertDemandValue s D Λ (.app ((proofErase Γ f).subst σ) x)
        (.app ((proofErase Γ g).subst σ) y) (((proofErase (C::Γ) E).subst σ.lift).inst x) := by
    have oldTyped := (TypedAt.of_typed hΓ hfOld).subst W.typed
    have newTyped := TF.subst W.typed
    have value := H.move W
    simp only [EPold, EPnew, ProofShape.subst] at oldTyped newTyped value
    exact output W (newTyped.app_result HL)
      (value.app heq hc (input W HX) HL HR (oldTyped.app_result HL))
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

/-- The original strong conversion constructor is handled when its target is
a universe. The actual type-equality child supplies sorted endpoint typings;
the term child's retained demand is reindexed without a core join, recursive
call on a substituted proof, or increase of the retained history stage. -/
theorem StrongBounded.demand_convert_to_sort
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ A (.sort u) (.sort v))
    (termChild : StrongBounded env univs k Γ a b A)
    (H : PiInertDemandValue p D (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ A)) :
    PiInertDemandValue q D (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ (.sort u)) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  exact H.sorted_reindex heq hs
    (DomainSort.of_typed hΓ (HE.defeq HT.hasType.1))
    (DomainSort.of_typed hΓ (HE.defeq HT.hasType.2))
    (TypedAt.of_typed hΓ HT.hasType.1)
    (TypedAt.of_typed hΓ HE.hasType.2).sources.1

/-- Strong conversion between two literal actual Pis consumes the original
two children at rank k. Argument and dependent-result demand transports remain
the missing components; the lambda/function parent, its ground comparison,
and ordinary application typing are discharged by function_convert. -/
theorem StrongBounded.demand_convert_function
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (typeChild : StrongBounded env univs k Γ (.forallE A B) (.forallE C E) (.sort u))
    (termChild : StrongBounded env univs k Γ f g (.forallE A B))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE A B)))
    (input : ∀ {Λ σ x y}, PiInertCoreWorld D (proofEraseCtx Γ) Λ σ →
      PiInertDemandValue r D Λ x y ((proofErase Γ C).subst σ) →
      PiInertDemandValue p D Λ x y ((proofErase Γ A).subst σ))
    (output : ∀ {Λ σ x a b}, PiInertCoreWorld D (proofEraseCtx Γ) Λ σ →
      TypedSource Λ (((proofErase (C::Γ) E).subst σ.lift).inst x) →
      PiInertDemandValue q D Λ a b (((proofErase (A::Γ) B).subst σ.lift).inst x) →
      PiInertDemandValue s D Λ a b (((proofErase (C::Γ) E).subst σ.lift).inst x)) :
    PiInertDemandValue (.arrow r s) D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  exact H.function_convert heq hs hc hRigid hΓ HT.hasType.1
    (HE.defeq HT.hasType.1) (HE.defeq HT.hasType.2) input output

end Lean4Lean.VEnv.Strengthening
