import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandGuardedExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEqOpaqueCore

/-! # Opaque Eq-headed arguments and the limit of ordinary finite demands

Every finite ordinary demand at a typed Eq-headed selected carrier is equivalent
to its ground payload: no future core-world instance can core-join a Pi. Guarded
values may be passed to consumers expecting these ordinary demands, but this
forgets their retained interface action. General higher-order guarded coverage
must not infer interface action from that ordinary demand alone.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A typed Eq-headed carrier cannot join any literal Pi by ordinary level
core, including when the Pi's domains and body reduce independently. -/
theorem ProofShape.TypedSource.eq_head_no_pi_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HT : TypedSource Δ T) (HH : T.constHead = some ``Eq.rec) :
    ¬ ComputeJoin (ErasedLevelCore D) T (.forallE A B) := by
  rintro ⟨out, RT, RP⟩
  obtain ⟨A', B', rfl, _, _⟩ := RP.pi_parts (fun R => erased_level_core_no_pi R)
  have H := RT.typed_eq_head heq hs hreg hoff hD HT HH
  cases H

/-- At an Eq-headed carrier, the arrow-action clause is empty in every core
world. Source typing and constant-head preservation exclude each possible
ordinary-core Pi join; both and ground profiles retain the same base. -/
theorem PiInertDemandBase.eq_head_demand
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : PiInertDemandBase D Δ a b T) (HH : T.constHead = some ``Eq.rec) :
    PiInertDemandValue p D Δ a b T := by
  induction p with
  | ground => exact H
  | both p q ihp ihq => exact ⟨ihp, ihq⟩
  | arrow p q =>
    refine ⟨H, ?_⟩
    intro Λ σ A B x y W _ J _ _ _ _
    exact ((H.typeSource.subst W.typed).eq_head_no_pi_join heq hs hreg hoff hD
      (ProofShape.const_head_subst HH) J).elim

/-- The complete ordinary finite-demand hierarchy collapses to its ground
payload at a typed Eq-headed selected carrier. This is a precise limitation
of these core-Pi tests, not a claim that guarded interface action is trivial. -/
theorem pi_inert_eq_head_demand_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HH : T.constHead = some ``Eq.rec) :
    PiInertDemandValue p D Δ a b T ↔ PiInertDemandBase D Δ a b T :=
  ⟨fun H => H.base, fun H => H.eq_head_demand heq hs hreg hoff hD HH⟩

/-- A guarded value supplies every ordinary demand at an Eq-headed selected
carrier via its selected ground history. Its interface action remains in the
original value and is not reconstructed from the forgotten payload. -/
theorem PiInertGuardedDemand.eq_head_forget
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : PiInertGuardedDemand D Δ r a b T U) (HH : T.constHead = some ``Eq.rec) :
    PiInertDemandValue p D Δ a b T :=
  H.base.eq_head_demand heq hs hreg hoff hD HH

/-- A function whose retained interface takes an Eq-headed argument carrier
can consume a guarded argument at that carrier. The result retains assigned
higher-order action. This uses the consumer's existing ordinary action rule;
it does not prove action for arbitrary lambda consumers at opaque domains. -/
theorem PiInertGuardedDemand.app_eq_head_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : PiInertGuardedDemand D Δ (.arrow p q) f g T (.forallE A B))
    (HX : PiInertGuardedDemand D Δ r x y A U) (HH : A.constHead = some ``Eq.rec)
    (HL : TypedSource Δ (.app f x)) (HR : TypedSource Δ (.app g y)) :
    PiInertGuardedDemand D Δ q (.app f x) (.app g y) (B.inst x) (B.inst x) :=
  H.app_guarded heq hs hc (HX.eq_head_forget heq hs hreg hoff hD HH) HL HR

/-- A reflexive cast of a type has an Eq.rec-headed erasure. The major may
be any equality proof; no computation of that proof is required. -/
theorem proofErase_reflexive_type_cast_head
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ (.sort v) (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) (.sort v) (.sort v)))
    (hT : env.HasType univs Γ T (.sort v)) :
    (proofErase Γ (typeCast u (.sort v) (.sort v) q T)).constHead = some ``Eq.rec := by
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hX hq hT
  have ES := proofErase_const_spine hΓ
    (args := [.sort u, .sort v, castMotive u (.sort v), T, .sort v, q])
    HC.hasType.1 (not_isProof_of_sort hΓ HC.hasType.1)
  change (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [u, .succ u])
    [.sort u, .sort v, castMotive u (.sort v), T, .sort v, q])).constHead = _
  rw [ES]
  exact constHead_mkApps _ _

omit [Params] in
/-- In the full environment core, any actual operand assigned a reflexive
type cast has every ordinary finite self-demand solely by ground reflexivity.
No exposed function interface or interface action is needed for this result.
This does not construct a guarded value or non-reflexive application action. -/
theorem EnvironmentCore.reflexive_cast_self_all_demands
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u v Γ q T f}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.sort v) (.sort u) →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) (.sort v) (.sort v)) →
      env.HasType U Γ T (.sort v) →
      env.HasType U Γ f (typeCast u (.sort v) (.sort v) q T) →
      ∀ p, PiInertDemandValue p definitions (proofEraseCtx Γ)
        (proofErase Γ f) (proofErase Γ f)
        (proofErase Γ (typeCast u (.sort v) (.sort v) q T)) := by
  letI := henv.params U
  intro u v Γ q T f heq hu hΓ hX hq hT hf p
  have hs : definitions.Sound env U := EnvironmentCore.sound
  have hcon : ∀ {p r}, Pat p r → ConcretePattern env p r := fun H => H
  have hc : TypedCoreConfluence (ErasedLevelCore definitions) :=
    EnvironmentCore.typed_level_core_confluence hcon
  obtain ⟨data, hreg, hr, hn, _⟩ := heq.recursorRegistration henv
  have TF := TypedAt.of_typed hΓ hf
  exact (PiInertDemandBase.refl hc TF.sources.1 TF.sources.2).eq_head_demand
    heq hs hreg (hr.eqRec_target heq hn).2.1 (EnvironmentCore.no_eqRec heq)
    (proofErase_reflexive_type_cast_head heq hu hΓ hX hq hT)

end Lean4Lean.VEnv.Strengthening
