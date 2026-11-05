import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasDemandRoots
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots

/-! # Rigid-head observations through full structure/function eta -/
namespace Lean4Lean.VEnv.Strengthening.AliasDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open DemandProfile
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {c : Name} {arity : Nat}

/-- Primitive observation preservation extends to all compatible paths. Node
typings supply the ordinary context interpretations needed at changed binders. -/
theorem Obs.compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b S t o}, Step Δ a b → Obs c arity Δ S a t o → Obs c arity Δ S b t o)
    (R : ScopedCompute Step Δ source out) (HS : S.Typed Δ) (H : Obs c arity Δ S source t o) :
    Obs c arity Δ S out t o := by
  induction R using ScopedCompute.rootBeta_induction generalizing S t o with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward HS
  | trans _ _ ih₁ ih₂ => exact ih₂ HS (ih₁ HS H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF RX)
    cases H with
    | app _ HF HX => exact .app HT (ihf HS HF) (fun key hk => ihx HS (HX key hk))
  | proj => exact H.not_proj.elim
  | forallE => exact H.not_pi.elim
  | @lam Δ D D' b b' RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.lam RA RB)
    obtain ⟨Γ, f, T, hΓ, EΓ, hf, HP, Ef⟩ := H.typing
    obtain ⟨A, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
    have EΓA : proofEraseCtx (A :: Γ) = D :: Δ := by simp only [proofEraseCtx, EA, EΓ]
    have SD : DomainSort Δ D u := ⟨Γ, A, hΓ, EΓ, hA, EA⟩
    obtain ⟨A', HA', EA'⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA RA
    have HC : IsDefEqCtx env univs [] (A :: Γ) (A' :: Γ) := .succ (.refl hΓ) HA'
    have WC : ContextSubstitution (D :: Δ) (D' :: Δ) ProofShape.Subst.id := by
      intro Γ₀ hΓ₀ EΓ₀
      have HH := control_context_substitution HC hΓ₀ (EΓA.trans EΓ₀.symm).symm
      simpa only [proofEraseCtx, EA', EΓ] using HH
    cases H with
    | lam HL HK HB =>
      exact .lam HT HK ((ihb (HS.cons HL.lam_parts.2 HK SD) HB).context WC)

/-- Ordinary computation either unfolds a certified alias or is excluded at
the designated rigid head. Fixed-template and direct delta roots agree. -/
theorem Obs.iota (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid c)
    (R : ErasedIotaPrimitive (PureObservation.Definitions.ofEnv env univs henv) a b)
    (H : Obs c arity Δ S a t o) : Obs c arity Δ S b t o := by
  classical
  have hD : ∀ ls rhs, ¬ (PureObservation.Definitions.ofEnv env univs henv).unfolds c ls rhs :=
    fun _ _ => PureObservation.Definitions.ofEnv_no_rigid henv hc
  by_cases HA : ∃ name, a = .const name []
  · obtain ⟨name, rfl⟩ := HA
    cases H with
    | const HT => exact (erased_iota_primitive_no_rigid hc hD R rfl).elim
    | delta HT HD HB => exact Obs.alias_root hcon HT HD HB R
  · exact (erased_iota_primitive_no_rigid hc hD R
      (H.primitive_head (erased_iota_primitive_head R) (fun name E => HA ⟨name, E⟩))).elim

/-- Full enriched stages preserve finite alias observations. Singleton heads
are separated from stored definitions by their registered iota equations. -/
theorem static_structure_stage_observation
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid c) :
    ∀ stage {Δ a b S t o},
      ErasedStaticStructureEtaExpansionStage (PureObservation.Definitions.ofEnv env univs henv) stage Δ a b →
      Obs c arity Δ S a t o → Obs c arity Δ S b t o := by
  have hs := PureObservation.Definitions.ofEnv_sound (U := univs) henv
  intro stage
  induction stage with
  | zero =>
    intro Δ a b S t o R H
    rcases R with (R | R) | R
    · exact H.iota hcon hc R
    · cases R with
      | sort => exact H.not_sort.elim
      | const HL hw =>
        cases H with
        | const HT => exact .const (HT.compute
            (erased_static_structure_eta_expansion_stage_descent heq hs 0)
            (.base (.inl (.inr (.const HL hw)))))
        | delta HT HD HB =>
          cases HL
          exact .delta HT HD HB
    · cases R; exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b S t o R H
    rcases R with R | R | R | R | R | R
    · exact ih R H
    · have HH := H.primitive_heads R.2.head
      cases R.2 with
      | intro V _ _ _ =>
        rcases HH with HH | ⟨name, rhs, HD, HH⟩
        · have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans HH)
          exact (V.not_rigid (hn ▸ hc)).elim
        · have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans HH)
          obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq V.equation_eq
          exact (PureObservation.Definitions.ofEnv_no_registered henv V.registered ⟨index, howner⟩
            (by simpa only [hn] using HD)).elim
    · have HH := H.primitive_heads R.head
      cases R with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        rcases HH with HH | ⟨name, rhs, HD, HH⟩
        · exact (hc.pats _ _ hp (by
            simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj HH)).elim
        · have hn : ``Eq.rec = name := Option.some.inj HH
          obtain ⟨value, hreg, hname, _⟩ := PureObservation.Definitions.ofEnv_origin henv HD
          exact (henv.defeq_head_not_pat (definitionRegistry_registered hreg).1.2
            (show value.toDefEq.lhs.stripLams.getAppFnArgs.1 =
              .const value.name (VLevel.params value.uvars) from rfl) hp
            (by simp only [canonicalEqRecPattern, SimplePattern.iota_headConst, hn, hname])).elim
    · exact H.native_identity (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact (H.typing.no_masked_structure
        (erased_static_structure_eta_expansion_stage_descent heq hs stage) H.demand.visible R).elim

/-- Arbitrary compatible paths through the full structure/function eta union
preserve alias observations. No native-image recovery premise is required. -/
theorem Obs.static_structure_union
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid c)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion
      (PureObservation.Definitions.ofEnv env univs henv)) Δ source out)
    (HS : S.Typed Δ) (H : Obs c arity Δ S source t o) : Obs c arity Δ S out t o :=
  H.compute (erased_static_structure_eta_expansion_union_descent heq
    (PureObservation.Definitions.ofEnv_sound henv))
    (fun ⟨stage, R⟩ H => static_structure_stage_observation heq hcon hc stage R H) R HS

end Lean4Lean.VEnv.Strengthening.AliasDemandProfile
