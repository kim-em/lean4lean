import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortLoopStageRepair
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFirstHeadStep
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKExample

/-! # Reflexive cast repair after arbitrary level-core computation

An erased proof major prevents ordinary computation at every prefix of Eq.rec.
Typed universe factorization therefore returns any full-core cast reduct to a
spine whose arguments descended independently. Recursive endpoint transport
constructs its stage-one guard and removes the cast at that computed spine.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private core_no_eqRec from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKExample
open private split_definition from Lean4Lean.Theory.Typing.Strengthening.ProofErasureQuotCoreConfluence
variable [Params] {D : Definitions}

/-- Ordinary computation of a proof-major Eq recursor preserves the full
spine. Every shorter prefix is checked for possible primitive contraction;
only independent computation of the five earlier arguments remains. -/
theorem ProofShape.Compute.eqRec_proof_core_inv
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (R : ProofShape.Compute (ErasedIotaPrimitive D)
      (ProofShape.eqRec v w α a M m b .proof) out) :
    ∃ α' a' M' m' b', out = ProofShape.eqRec v w α' a' M' m' b' .proof ∧
      ProofShape.Compute (ErasedIotaPrimitive D) α α' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) a a' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) M M' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) m m' ∧
      ProofShape.Compute (ErasedIotaPrimitive D) b b' := by
  have RS : ScopedCompute (fun _ => ErasedIotaPrimitive D) []
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) [α,a,M,m,b,.proof]) out :=
    R.scoped (fun H => .base H)
  rcases RS.const_spine_or_head with ⟨args', E, HA⟩ | ⟨k, args', target, hk, HA, HS⟩
  · cases HA with | cons Rα HA =>
      cases HA with | cons Ra HA =>
        cases HA with | cons RM HA =>
          cases HA with | cons Rm HA =>
            cases HA with | cons Rb HA =>
              cases HA with | cons Rp HA =>
                cases HA
                cases Rp.proof_fixed (fun H => erased_iota_primitive_head H)
                exact ⟨_, _, _, _, _, E, Rα.core_forget, Ra.core_forget,
                  RM.core_forget, Rm.core_forget, Rb.core_forget⟩
  · apply (erased_iota_eqRec_no_root hreg hoff hD (constHead_mkApps _ _) ?_ HS).elim
    by_cases hlen : args'.length ≤ 5
    · exact .inl ⟨_, _, rfl, hlen⟩
    have HL := HA.length_eq
    simp only [List.length_take, List.length_cons, List.length_nil] at HL
    have hk' : 6 ≤ k := by omega
    rw [List.take_of_length_le (by simpa only [List.length_cons, List.length_nil] using hk')] at HA
    cases HA with | cons _ HA =>
      cases HA with | cons _ HA =>
        cases HA with | cons _ HA =>
          cases HA with | cons _ HA =>
            cases HA with | cons _ HA =>
              cases HA with | cons Rp HA =>
                cases HA
                cases Rp.proof_fixed (fun H => erased_iota_primitive_head H)
                exact .inr ⟨_, rfl⟩

/-- Every full level-core reduct of a reflexive cast computes at stage one to
an ordinary reduct of its original payload. The conclusion constructs both
paths; no supplied residual spine or residual endpoint check is required. -/
theorem reflexive_cast_level_core_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (hx : env.HasType univs Γ x X)
    (R : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (typeCast u X X q x)) out) :
    ∃ minor, ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ x) minor ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ out minor := by
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hX hq hx
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ HC.hasType.1 R
  have embed {Δ a b} (R : ProofShape.Compute (ErasedLevelCore D) a b) :
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b :=
    R.scoped (fun H => .base (.inl (.inl H)))
  by_cases hp : IsProof Γ (typeCast u X X q x)
  · have Ex := proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)
    rw [proofErase_eq_proof.2 hp] at RM
    have E := (RM.scoped (Δ := []) (fun H => .base H)).proof_fixed
      (fun H => erased_iota_primitive_head H)
    subst mid
    exact ⟨.proof, Ex ▸ .refl, embed RT⟩
  · have Eq : proofErase Γ q = .proof := proofErase_eq_proof.2
      ⟨_, hq, HasType.eqApp heq (by exact hu) (.sort hu) hX hX⟩
    have ES := proofErase_const_spine hΓ
      (args := [.sort u, X, castMotive u X, x, X, q]) HC.hasType.1 hp
    change proofErase Γ (typeCast u X X q x) = _ at ES
    simp only [List.map_cons, List.map_nil, Eq] at ES
    rw [ES] at RM
    obtain ⟨α', a', M', m', b', rfl, _, Ra, _, Rm, Rb⟩ := RM.eqRec_proof_core_inv hreg hoff hD
    have HG : LevelRecursiveGuard D true (proofErase Γ X) (proofErase Γ X) :=
      .join hΓ hX hX ⟨_, .refl, .refl⟩
    have HG' := HG.forward hs hl hcon hc (Ra.mono (fun H => .inl H)) (Rb.mono (fun H => .inl H))
    exact ⟨m', Rm, (embed RT).trans HG'.first_stage_full⟩

/-- Arbitrary independent full-core computation of a reflexive cast and its
payload has a common reduct at stage one. Only level-core confluence is used. -/
theorem reflexive_cast_level_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
    (hx : env.HasType univs Γ x X)
    (RC : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (typeCast u X X q x)) castOut)
    (RX : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ x) payloadOut) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ castOut shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ payloadOut shared := by
  obtain ⟨minor, RM, RR⟩ := reflexive_cast_level_core_residual heq hs hl hcon hc hreg hoff hD hu hΓ hX hq hx RC
  obtain ⟨shared, RA, RB⟩ := hc hΓ hx (RM.mono (fun H => .inl H)) RX
  exact ⟨shared, RR.trans (RA.scoped (fun H => .base (.inl (.inl H)))),
    RB.scoped (fun H => .base (.inl (.inl H)))⟩

namespace EnvironmentCore

/-- The total actual core never installs an Eq.rec delta program. Optional
quotient and selected structure programs preserve the canonical Eq exclusion. -/
theorem no_eqRec (heq : env.HasCanonicalEq) : ∀ levels rhs, ¬ definitions.unfolds ``Eq.rec levels rhs := by
  intro levels rhs H
  classical
  by_cases hq : QuotRegistered env
  · rw [definitions_of_quot hq] at H
    rcases split_definition hq H with H | ⟨H, _⟩
    · exact core_no_eqRec heq H
    · exact (by decide : ``Eq.rec ≠ ``Quot.lift) H
  · rw [definitions_of_no_quot hq] at H
    exact core_no_eqRec heq H

omit [Params] in
/-- Actual environment specialization discharges core soundness, universe
compatibility, confluence, Eq registration and absence of Eq.rec unfolding. -/
theorem reflexive_cast_computed_join {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u Γ X q x castOut payloadOut}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) X X) → env.HasType U Γ x X →
      ProofShape.Compute (ErasedLevelCore definitions) (proofErase Γ (typeCast u X X q x)) castOut →
      ProofShape.Compute (ErasedLevelCore definitions) (proofErase Γ x) payloadOut →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionStage definitions 1) (proofEraseCtx Γ) castOut shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionStage definitions 1) (proofEraseCtx Γ) payloadOut shared := by
  letI := henv.params U
  intro u Γ X q x castOut payloadOut heq hu hΓ hX hq hx RC RX
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact reflexive_cast_level_core_join heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hu hΓ hX hq hx RC RX

end EnvironmentCore
end Lean4Lean.VEnv.Strengthening
