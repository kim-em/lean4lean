import Lean4Lean.Theory.Typing.Strengthening.ProofErasureValueObservationFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots

/-! # Value-carrying observations through full enriched computation

Opaque value nodes append scoped chains. Control nodes retain the designated
rigid head, while beta substitutes observations with their histories. This
preservation theorem does not yet interpret observations to read out arguments.
-/
namespace Lean4Lean.VEnv.Strengthening.ValueDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Primitive preservation extends to all compatible paths. Value payloads
append complete chains, including computation underneath changed lambda domains. -/
theorem Obs.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hroot : ∀ {Δ a b n S t o}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      Obs D c n Δ S a t o → Obs D c n Δ S b t o)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out)
    (HS : S.Typed Δ) (H : Obs D c n Δ S source t o) : Obs D c n Δ S out t o := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionUnion D) :=
    erased_static_structure_eta_expansion_union_descent heq hs
  induction R using ScopedCompute.rootBeta_induction generalizing n S t o with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward heq hs HS
  | trans _ _ ih₁ ih₂ => exact ih₂ HS (ih₁ HS H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF RX)
    cases H with
    | app _ HF HX => exact .app HT (ihf HS HF) (fun key hk => ihx HS (HX key hk))
    | value _ HC => exact .value HT (HC.compute heq hs (.app RF RX))
    | value_step _ HO HC => exact .value_step HT HO (HC.compute heq hs (.app RF RX))
  | proj R _ =>
    have HT := H.typing.compute hstep (.proj R)
    cases H with
    | value _ HC => exact .value HT (HC.compute heq hs (.proj R))
    | value_step _ HO HC => exact .value_step HT HO (HC.compute heq hs (.proj R))
  | forallE RA RB _ _ =>
    have HT := H.typing.compute hstep (.forallE RA RB)
    cases H with
    | value _ HC => exact .value HT (HC.compute heq hs (.forallE RA RB))
    | value_step _ HO HC => exact .value_step HT HO (HC.compute heq hs (.forallE RA RB))
  | @lam Δ A A' b b' RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.lam RA RB)
    obtain ⟨Γ, f, T, hΓ, EΓ, hf, HP, Ef⟩ := H.typing
    obtain ⟨A₀, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
    have EΓA : proofEraseCtx (A₀ :: Γ) = A :: Δ := by simp only [proofEraseCtx, EA, EΓ]
    have SD : DomainSort Δ A u := ⟨Γ, A₀, hΓ, EΓ, hA, EA⟩
    obtain ⟨A₁, HA, EA'⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA RA
    have HC : IsDefEqCtx env univs [] (A₀ :: Γ) (A₁ :: Γ) := .succ (.refl hΓ) HA
    have WC : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id := by
      intro Γ₀ hΓ₀ EΓ₀
      have HH := control_context_substitution HC hΓ₀ (EΓA.trans EΓ₀.symm).symm
      simpa only [proofEraseCtx, EA', EΓ] using HH
    cases H with
    | lam HL HK HB =>
      exact .lam HT HK ((ihb (HS.cons HL.lam_parts.2 HK SD) HB).context heq hs WC)
    | value _ HV => exact .value HT (HV.compute heq hs (.lam RA RB))
    | value_step _ HO HV => exact .value_step HT HO (HV.compute heq hs (.lam RA RB))

/-- Control observations survive every primitive stage. Opaque values are
handled separately, so no false head-shape restriction is imposed on them. -/
theorem static_structure_stage_control
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    ∀ stage {Δ a b n S t o}, ErasedStaticStructureEtaExpansionStage D stage Δ a b →
      Obs D c n Δ S a t o → o.Control → Obs D c n Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b n S t o R H HK
    rcases R with (R | R) | R
    · exact (erased_iota_primitive_no_rigid hc hD R
        (H.primitive_head HK (erased_iota_primitive_head R))).elim
    · cases R with
      | sort => exact (H.not_sort HK).elim
      | const HL hw =>
        cases H with
        | const HT HP => exact .const (HT.compute
            (erased_static_structure_eta_expansion_stage_descent heq hs 0)
            (.base (.inl (.inr (.const HL hw))))) HP
        | value | value_step => cases HK
    · cases R; exact H.constant_expansion heq hs
  | succ stage ih =>
    intro Δ a b n S t o R H HK
    rcases R with R | R | R | R | R | R
    · exact ih R H HK
    · have hh := H.primitive_head HK R.2.head
      cases R.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans hh)
        exact (V.not_rigid (hn ▸ hc)).elim
    · have hh := H.primitive_head HK R.head
      cases R with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        exact (hc.pats _ _ hp (by
          simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj hh)).elim
    · exact H.native_identity (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta heq hs (erased_static_structure_eta_expansion_stage_descent heq hs stage) HK R
    · exact (H.typing.no_masked_structure
        (erased_static_structure_eta_expansion_stage_descent heq hs stage) (H.demand.headed HK) R).elim

/-- Every full-union primitive preserves all keys. At a data key the primitive
appends a value chain; at a control key the rigid-head invariant applies. -/
theorem static_structure_union_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (R : ErasedStaticStructureEtaExpansionUnion D Δ a b)
    (H : Obs D c n Δ S a t o) : Obs D c n Δ S b t o := by
  cases o with
  | value origin =>
    cases H.demand
    exact H.value_compute heq hs (.base R)
  | head args =>
    obtain ⟨stage, R⟩ := R
    exact static_structure_stage_control heq hs hc hD stage R H .head
  | app keys o =>
    obtain ⟨stage, R⟩ := R
    exact static_structure_stage_control heq hs hc hD stage R H .app

/-- The finite value observer survives arbitrary full structure/function-eta
computation, including beta and arbitrary typed substitutions in control frames.
Operational argument readout and initial telescope supply are still separate. -/
theorem Obs.static_structure_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out)
    (HS : S.Typed Δ) (H : Obs D c n Δ S source t o) : Obs D c n Δ S out t o :=
  H.compute heq hs (fun R H => static_structure_union_observation heq hs hc hD R H) R HS

end Lean4Lean.VEnv.Strengthening.ValueDemandProfile
