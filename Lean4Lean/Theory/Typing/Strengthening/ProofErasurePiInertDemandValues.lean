import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCarrierValues

/-! # Finite higher-order demands with retained carrier histories

A demand records the argument and result evidence needed at a function use.
It is independent of checker stages and does not bound core reduction length.
Every value retains a complete carrier history with variable-world futures.
Function demands additionally retain action on the specified argument demand,
returning the specified result demand at the exact dependent carrier.

No theorem here asserts that every strong derivation satisfies every demand.
That coverage question includes paired body substitution and general type
conversion; ordinary-core joins alone do not solve it.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private value_inst_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWorldValues
variable [Params] {D : Definitions}

/-- A finite description of the evidence consumed and returned by a function
use. This is neither a normalization bound nor a bound on checker stages. -/
inductive PiInertDemand where
  | ground
  | arrow (argument result : PiInertDemand)

/-- The common payload at every demand: actual source typing for both terms
and their selected carrier, plus a finite-stage history at that carrier. -/
structure PiInertDemandBase (D : Definitions) (Δ : List ProofShape)
    (a b T : ProofShape) : Prop where
  leftSource : TypedSource Δ a
  rightSource : TypedSource Δ b
  typeSource : TypedSource Δ T
  history : ∃ n, PiInertWorldHistory D n Δ T a b

/-- Function demands test every typed ordinary-core Pi join of the selected
carrier in every core world. Argument and result demands recurse separately;
output stages need not be uniform across arguments or future worlds. -/
def PiInertDemandValue : PiInertDemand → Definitions → List ProofShape →
    ProofShape → ProofShape → ProofShape → Prop
  | .ground, D, Δ, a, b, T => PiInertDemandBase D Δ a b T
  | .arrow p q, D, Δ, a, b, T => PiInertDemandBase D Δ a b T ∧
      ∀ {Δ' τ A B x y}, PiInertCoreWorld D Δ Δ' τ →
        TypedSource Δ' (.forallE A B) →
        ComputeJoin (ErasedLevelCore D) (T.subst τ) (.forallE A B) →
        PiInertDemandValue p D Δ' x y A →
        TypedSource Δ' (.app (a.subst τ) x) →
        TypedSource Δ' (.app (b.subst τ) y) → TypedSource Δ' (B.inst x) →
        PiInertDemandValue q D Δ' (.app (a.subst τ) x) (.app (b.subst τ) y) (B.inst x)

/-- Every demand retains the same typed carrier-history payload. -/
theorem PiInertDemandValue.base (H : PiInertDemandValue p D Δ a b T) :
    PiInertDemandBase D Δ a b T := by
  cases p with
  | ground => exact H
  | arrow => exact H.1

/-- Typed core joins compose at a middle raw shape with an actual source
witness; no global or guarded-stage confluence is used. -/
theorem ProofShape.ComputeJoin.trans_source
    (hc : TypedCoreConfluence (ErasedLevelCore D)) (HT : TypedSource Δ b)
    (H : ComputeJoin (ErasedLevelCore D) a b)
    (K : ComputeJoin (ErasedLevelCore D) b c) : ComputeJoin (ErasedLevelCore D) a c := by
  obtain ⟨Γ, e, T, hΓ, _, ht, rfl⟩ := HT
  exact H.trans_typed hc hΓ ht K

/-- A carrier history transports along a typed ordinary-core join in either
direction. Its residual clauses consume the first branch and prefix the second. -/
theorem PiInertWorldHistory.core_join
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertWorldHistory D n Δ T a b) (HU : TypedSource Δ U)
    (J : ComputeJoin (ErasedLevelCore D) T U) : PiInertWorldHistory D n Δ U a b := by
  obtain ⟨out, RT, RU⟩ := J
  exact (H.carrier_reduct RT).carrier_prefix (PiInertEvidence.core_source hs hc HU RU).world_computation

/-- All demand payloads move through composed variable worlds. The action
clause retains the final world's own source typings and Pi join. -/
theorem PiInertDemandValue.move (H : PiInertDemandValue p D Δ a b T)
    (W : PiInertCoreWorld D Δ Δ' τ) :
    PiInertDemandValue p D Δ' (a.subst τ) (b.subst τ) (T.subst τ) := by
  have base : PiInertDemandBase D Δ' (a.subst τ) (b.subst τ) (T.subst τ) := by
    obtain ⟨n, HN⟩ := H.base.history
    exact ⟨H.base.leftSource.subst W.typed, H.base.rightSource.subst W.typed,
      H.base.typeSource.subst W.typed, n, HN.move W⟩
  cases p with
  | ground => exact base
  | arrow p q =>
    refine ⟨base, ?_⟩
    intro Δ'' υ A B x y V HT J HX HA HB HR
    simp only [ProofShape.subst_subst] at J HA HB ⊢
    exact H.2 (W.compose V) HT J HX HA HB HR

/-- A typed ordinary-core change of selected carrier preserves every finite
demand. Testing all core Pi joins makes this transport preserve the action
clause without changing argument or result demands. -/
theorem PiInertDemandValue.core_join
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertDemandValue p D Δ a b T) (HU : TypedSource Δ U)
    (J : ComputeJoin (ErasedLevelCore D) T U) : PiInertDemandValue p D Δ a b U := by
  have base : PiInertDemandBase D Δ a b U := by
    obtain ⟨n, HN⟩ := H.base.history
    exact ⟨H.base.leftSource, H.base.rightSource, HU, n, HN.core_join hs hc HU J⟩
  cases p with
  | ground => exact base
  | arrow p q =>
    refine ⟨base, ?_⟩
    intro Δ' τ A B x y W HT K HX HA HB HR
    have JW := J.subst (fun R => erased_level_core_subst R) (σ := τ)
    exact H.2 W HT (JW.trans_source hc (HU.subst W.typed) K) HX HA HB HR

/-- Independent typed core prefixes preserve an entire demand, including
higher-order action. The source typing of each reduced application is derived
from its supplied original application typing, then the result demand recurses. -/
theorem PiInertDemandValue.prefixes
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertDemandValue p D Δ a' b' T)
    (HA : TypedSource Δ a) (HB : TypedSource Δ b)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertDemandValue p D Δ a b T := by
  induction p generalizing Δ a b a' b' T with
  | ground =>
    obtain ⟨n, HN⟩ := H.history
    exact ⟨HA, HB, H.typeSource, n, HN.prefixes
      (PiInertEvidence.core_source hs hc HA RA).world_computation
      (PiInertEvidence.core_source hs hc HB RB).world_computation⟩
  | arrow p q _ ih =>
    have base : PiInertDemandBase D Δ a b T := by
      obtain ⟨n, HN⟩ := H.1.history
      exact ⟨HA, HB, H.1.typeSource, n, HN.prefixes
        (PiInertEvidence.core_source hs hc HA RA).world_computation
        (PiInertEvidence.core_source hs hc HB RB).world_computation⟩
    refine ⟨base, ?_⟩
    intro Δ' τ A B x y W HT J HX HL HR HE
    have RL : Compute (ErasedLevelCore D) (.app (a.subst τ) x) (.app (a'.subst τ) x) :=
      .app (RA.subst (fun R => erased_level_core_subst R)) .refl
    have RR : Compute (ErasedLevelCore D) (.app (b.subst τ) y) (.app (b'.subst τ) y) :=
      .app (RB.subst (fun R => erased_level_core_subst R)) .refl
    have HL' := (PiInertEvidence.core_source (n := 0) hs hc HL RL).base.1
    have HR' := (PiInertEvidence.core_source (n := 0) hs hc HR RR).base.1
    exact ih (H.2 W HT J HX HL' HR' HE) HL HR RL RR

/-- Neutral and structural-subsingleton carrier values satisfy every finite
demand. Each application retains a carrier value, which recursively supplies
the requested result demand; only the argument's carrier history is consumed. -/
theorem PiInertCarrierValue.demand
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertCarrierValue D n Δ a b T) (HT : TypedSource Δ T) :
    PiInertDemandValue p D Δ a b T := by
  induction p generalizing n Δ a b T with
  | ground => exact ⟨H.sources.1, H.sources.2, HT, n, H.history heq hs hc hRigid⟩
  | arrow p q _ ih =>
    refine ⟨⟨H.sources.1, H.sources.2, HT, n, H.history heq hs hc hRigid⟩, ?_⟩
    intro Δ' τ A B x y W HP J HX HA HB HR
    have HF := (pi_inert_carrier_value_core_join_iff heq hs hc hRigid (HT.subst W.typed) HP J).mp
      (H.move W)
    obtain ⟨m, HM⟩ := HX.base.history
    exact ih (((HF.raise (Nat.le_max_left n m)).app hs hc
      (HM.raise (Nat.le_max_right n m)) HA HB HR)) HR

/-- Ordinary-core Pi joins expose joins of both components. The core has no
Pi-root rule, so no type-equality inversion hypothesis is needed. -/
theorem ProofShape.ComputeJoin.level_core_pi_parts
    (J : ComputeJoin (ErasedLevelCore D) (.forallE A B) (.forallE C E)) :
    ComputeJoin (ErasedLevelCore D) A C ∧ ComputeJoin (ErasedLevelCore D) B E := by
  obtain ⟨out, RL, RR⟩ := J
  obtain ⟨A', B', rfl, RA, RB⟩ := RL.pi_parts (fun H => erased_level_core_no_pi H)
  obtain ⟨C', E', EQ, RC, RE⟩ := RR.pi_parts (fun H => erased_level_core_no_pi H)
  cases EQ
  exact ⟨⟨_, RA, RC⟩, ⟨_, RB, RE⟩⟩

/-- Actual raw typing and typed ordinary-core confluence supply reflexive
base evidence, including for lambdas which do not return neutral terms. -/
theorem PiInertDemandBase.refl
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HA : TypedSource Δ a) (HT : TypedSource Δ T) : PiInertDemandBase D Δ a a T := by
  have R : PiInertEvidence D 0 .compute Δ a a := .of_core_join hc HA HA .refl
  exact ⟨HA, HA, HT, 0, (R.join hc R).carrier_history.world_history⟩

/-- An actually represented context supplies its identity core world. The
representative may be any typed source in that context. -/
theorem PiInertCoreWorld.identity_source
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HT : TypedSource Δ T) : PiInertCoreWorld D Δ Δ ProofShape.Subst.id := by
  obtain ⟨Γ, e, A, hΓ, rfl, _, _⟩ := HT
  exact .of_exact_actual heq hc hΓ ContextRenaming.identity

/-- A function demand consumes its specified argument demand at the local
world and returns the entire result demand. No new checker-stage bound is
imposed on the argument or result. -/
theorem PiInertDemandValue.app
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertDemandValue (.arrow p q) D Δ a b (.forallE A B))
    (HX : PiInertDemandValue p D Δ x y A)
    (HA : TypedSource Δ (.app a x)) (HB : TypedSource Δ (.app b y))
    (HT : TypedSource Δ (B.inst x)) :
    PiInertDemandValue q D Δ (.app a x) (.app b y) (B.inst x) := by
  have W := PiInertCoreWorld.identity_source heq hc H.1.typeSource
  have J : ComputeJoin (ErasedLevelCore D)
      ((ProofShape.forallE A B).subst ProofShape.Subst.id) (.forallE A B) := by
    simpa only [ProofShape.subst_id] using
      (ComputeJoin.refl : ComputeJoin (ErasedLevelCore D) (.forallE A B) (.forallE A B))
  simpa only [ProofShape.subst_id] using H.2 W H.1.typeSource J HX
    (by simpa only [ProofShape.subst_id] using HA)
    (by simpa only [ProofShape.subst_id] using HB) HT

/-- Identity is itself a value at every finite argument/result demand p.
Thus it can be supplied as a higher-order argument, not merely used as an
external action on the old carrier-value class. Typed Pi aliases are included. -/
theorem pi_inert_identity_demand_value
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HD : TypedSource Δ A) (HF : TypedSource Δ (.lam A (.bvar 0)))
    (HT : TypedSource Δ (.forallE A (A.liftN 1))) :
    PiInertDemandValue (.arrow p p) D Δ (.lam A (.bvar 0)) (.lam A (.bvar 0))
      (.forallE A (A.liftN 1)) := by
  refine ⟨PiInertDemandBase.refl hc HF HT, ?_⟩
  intro Δ' τ C E x y W HP J HX HL HR HE
  simp only [ProofShape.subst, ProofShape.lift_subst_lift] at J
  obtain ⟨JD, JB⟩ := J.level_core_pi_parts
  have JE : ComputeJoin (ErasedLevelCore D) (A.subst τ) (E.inst x) := by
    have K : ComputeJoin (ErasedLevelCore D) ((A.subst τ).liftN 1 |>.inst x) (E.inst x) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        JB.subst (fun R => erased_level_core_subst R) (σ := ProofShape.Subst.one x)
    simpa only [value_inst_lift] using K
  have HC := HX.core_join hs hc HE (JD.symm.trans_source hc (HD.subst W.typed) JE)
  have beta (x : ProofShape) : Compute (ErasedLevelCore D)
      (.app ((ProofShape.lam A (.bvar 0)).subst τ) x) x := by
    apply ProofShape.Compute.beta
    simpa only [ProofShape.subst, ProofShape.Subst.lift, ProofShape.inst,
      Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero] using
      (ProofShape.BetaRed.beta (A := A.subst τ) (b := .bvar 0) (a := x))
  exact HC.prefixes hs hc HL HR (beta x) (beta y)

/-- The dependent evaluator is a value consuming a function demand p -> q
and returning q. Its captured argument supplies p, so lambda function values
can be passed to it without dropping their higher-order result evidence. -/
theorem pi_inert_evaluator_demand_value
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HX : PiInertDemandValue p D Δ x x A)
    (HP : TypedSource Δ (.forallE A B)) (HT : TypedSource Δ (B.inst x))
    (HF : TypedSource Δ (.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1))))
    (HE : TypedSource Δ (.forallE (.forallE A B) ((B.inst x).liftN 1))) :
    PiInertDemandValue (.arrow (.arrow p q) q) D Δ
      (.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1)))
      (.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1)))
      (.forallE (.forallE A B) ((B.inst x).liftN 1)) := by
  refine ⟨PiInertDemandBase.refl hc HF HE, ?_⟩
  intro Δ' τ C E f g W HP' J HV HL HR HResult
  simp only [ProofShape.subst, ProofShape.lift_subst_lift] at J
  obtain ⟨JD, JB⟩ := J.level_core_pi_parts
  simp only [ProofShape.subst_inst] at JB
  have HV' := HV.core_join hs hc (HP.subst W.typed) JD.symm
  have HT' := HT.subst W.typed
  simp only [ProofShape.subst_inst] at HT'
  have beta (f : ProofShape) : Compute (ErasedLevelCore D)
      (.app ((ProofShape.lam (.forallE A B) (.app (.bvar 0) (x.liftN 1))).subst τ) f)
      (.app f (x.subst τ)) := by
    have E : ((ProofShape.app (.bvar 0) (x.liftN 1)).subst τ.lift).inst f = .app f (x.subst τ) := by
      simp only [ProofShape.subst, ProofShape.Subst.lift, ProofShape.lift_subst_lift,
        ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero]
      exact congrArg (ProofShape.app f) (value_inst_lift (x.subst τ) f)
    exact E ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := (ProofShape.forallE A B).subst τ))
  have HL' := (PiInertEvidence.core_source (n := 0) hs hc HL (beta f)).base.1
  have HR' := (PiInertEvidence.core_source (n := 0) hs hc HR (beta g)).base.1
  have HBody := HV'.app heq hc (HX.move W) HL' HR' HT'
  have JE : ComputeJoin (ErasedLevelCore D) ((B.subst τ.lift).inst (x.subst τ)) (E.inst f) := by
    have K : ComputeJoin (ErasedLevelCore D)
        ((((B.subst τ.lift).inst (x.subst τ)).liftN 1).inst f) (E.inst f) := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
        JB.subst (fun R => erased_level_core_subst R) (σ := ProofShape.Subst.one f)
    simpa only [value_inst_lift] using K
  exact (HBody.core_join hs hc HResult JE).prefixes hs hc HL HR (beta f) (beta g)

/-- Actual non-proof application reconstructs the exact erased dependent
carrier and the full requested result demand. The original function and
argument equalities supply actual typing, without constructing a larger
strong derivation to serve as a recursive premise. -/
theorem PiInertDemandValue.apply_actual_nonproof
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.IsDefEq univs Γ f g (.forallE A B))
    (hX : env.IsDefEq univs Γ x y A) (hn : ¬ IsProof Γ (.app f x))
    (H : PiInertDemandValue (.arrow p q) D (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)
      (proofErase Γ (.forallE A B)))
    (HX : PiInertDemandValue p D (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ y) (proofErase Γ A)) :
    PiInertDemandValue q D (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (proofErase Γ (.app g y)) (proofErase Γ (B.inst x)) := by
  have hApp := hF.appDF hX
  have hn' : ¬ IsProof Γ (.app g y) := fun hp =>
    hn (isProof_of_common_type hΓ hApp.hasType.2 hApp.hasType.1 hp)
  obtain ⟨v, hPi⟩ := hF.hasType.1.isType henv hΓ
  obtain ⟨⟨u, hA⟩, ⟨w, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A::Γ) B) := if_neg (not_isProof_of_sort hΓ hPi)
  rw [EP] at H
  have HT : TypedSource (proofEraseCtx Γ) (proofErase Γ (B.inst x)) :=
    ⟨Γ, _, _, hΓ, rfl, hB.instN henv Ctx.InstN.zero hX.hasType.1, rfl⟩
  rw [proofErase_instN hΓA hX.hasType.1 Ctx.InstN.zero hB] at HT
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn,
    show proofErase Γ (.app g y) = .app _ _ from if_neg hn',
    proofErase_instN hΓA hX.hasType.1 Ctx.InstN.zero hB]
  exact H.app heq hc HX ⟨Γ, _, _, hΓ, rfl, hApp.hasType.1, if_neg hn⟩
    ⟨Γ, _, _, hΓ, rfl, hApp.hasType.2, if_neg hn'⟩ HT


/-- Identity at any actual positive type has every matching finite function
demand. The raw lambda and Pi source witnesses are constructed from actual
typing and weakening, rather than postulated as unconnected raw witnesses. -/
theorem pi_inert_actual_identity_demand_value
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort (.succ u))) :
    PiInertDemandValue (.arrow p p) D (proofEraseCtx Γ)
      (proofErase Γ (.lam A (.bvar 0))) (proofErase Γ (.lam A (.bvar 0)))
      (proofErase Γ (.forallE A A.lift)) := by
  have hu := hA.sort_r henv hΓ
  have hΓA : OnCtx (A::Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hPi : env.HasType univs Γ (.forallE A A.lift) (.sort (.succ u)) :=
    (IsDefEq.sortDF (l := .imax (.succ u) (.succ u)) ⟨hu, hu⟩ hu VLevel.imax_self).defeq
      (HasType.forallE hA (hA.weak henv))
  have hf : env.HasType univs Γ (.lam A (.bvar 0)) (.forallE A A.lift) :=
    .lam hA (.bvar .zero)
  have hv : env.HasType univs (A::Γ) (.bvar 0) A.lift := .bvar .zero
  have EF : proofErase Γ (.lam A (.bvar 0)) = .lam (proofErase Γ A) (.bvar 0) := by
    rw [show proofErase Γ (.lam A (.bvar 0)) = .lam _ _ from
      if_neg (not_proof_at_positive_type hΓ hPi hf),
      show proofErase (A::Γ) (.bvar 0) = .bvar 0 from
        if_neg (not_proof_at_positive_type hΓA (hA.weak henv) hv)]
  have ET : proofErase Γ (.forallE A A.lift) =
      .forallE (proofErase Γ A) ((proofErase Γ A).liftN 1) := by
    rw [show proofErase Γ (.forallE A A.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi)]
    exact congrArg (ProofShape.forallE (proofErase Γ A))
      (proofErase_liftN hΓ hΓA Ctx.LiftN.one hA)
  rw [EF, ET]
  exact pi_inert_identity_demand_value hs hc ⟨Γ, _, _, hΓ, rfl, hA, rfl⟩
    ⟨Γ, _, _, hΓ, rfl, hf, EF⟩ ⟨Γ, _, _, hΓ, rfl, hPi, ET⟩

/-- A concrete higher-order use: identity at A -> A accepts identity at A,
and the result retains every matching function demand. This uses actual
non-proof application and does not merely give an external lambda action. -/
theorem pi_inert_actual_identity_as_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort (.succ u))) :
    let F := VExpr.forallE A A.lift
    let e := VExpr.app (.lam F (.bvar 0)) (.lam A (.bvar 0))
    PiInertDemandValue (.arrow p p) D (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ e) (proofErase Γ F) := by
  dsimp only
  have hu := hA.sort_r henv hΓ
  have hF : env.HasType univs Γ (.forallE A A.lift) (.sort (.succ u)) :=
    (IsDefEq.sortDF (l := .imax (.succ u) (.succ u)) ⟨hu, hu⟩ hu VLevel.imax_self).defeq
      (HasType.forallE hA (hA.weak henv))
  have hi : env.HasType univs Γ (.lam A (.bvar 0)) (.forallE A A.lift) := .lam hA (.bvar .zero)
  have ho : env.HasType univs Γ (.lam (.forallE A A.lift) (.bvar 0))
      (.forallE (.forallE A A.lift) (VExpr.forallE A A.lift).lift) := .lam hF (.bvar .zero)
  have happ : env.HasType univs Γ
      (.app (.lam (.forallE A A.lift) (.bvar 0)) (.lam A (.bvar 0))) (.forallE A A.lift) := by
    simpa only [VExpr.inst_lift] using ho.app hi
  have hn := not_proof_at_positive_type hΓ hF happ
  have HI : PiInertDemandValue (.arrow p p) D (proofEraseCtx Γ)
      (proofErase Γ (.lam A (.bvar 0))) (proofErase Γ (.lam A (.bvar 0)))
      (proofErase Γ (.forallE A A.lift)) := pi_inert_actual_identity_demand_value hs hc hΓ hA
  have HO := pi_inert_actual_identity_demand_value (p := .arrow p p) hs hc hΓ hF
  simpa only [VExpr.inst_lift] using HO.apply_actual_nonproof heq hc hΓ ho hi hn HI

end Lean4Lean.VEnv.Strengthening
