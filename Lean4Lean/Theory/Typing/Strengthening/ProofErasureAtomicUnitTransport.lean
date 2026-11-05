import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureUniverseJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiOriginTransport

/-! # Unit demands through the full structure computation union

Structure expansion at the atomic profile reaches the fixed empty constructor.
Sort and function profiles exclude a structure guard by ordinary type uniqueness.
-/
namespace Lean4Lean.VEnv.Strengthening.AtomicUnitObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open AtomicControl (Atom ControlType ControlTyping Demand Sets)
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] [Atom] {c : Name}

/-- A structure step at a control profile is necessarily the atomic unit
case and produces its constructor with the unique empty universe instance. -/
theorem masked_structure_terminal
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (H : ControlTyping Δ e t) (R : NativeMaskedStructureExpansion Step Δ e out) :
    t = .atom ∧ out = .const info.ctorName [] := by
  obtain ⟨Γ, f, hΓ, rfl, hf, rfl⟩ := H
  cases R with
  | intro hi' hx ha hp RN =>
    cases t with
    | sort u =>
      obtain ⟨A, hFA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
      obtain ⟨ps, rfl, _⟩ := proofErase_const_spine_inv EA
      obtain ⟨_, hA⟩ := hFA.isType henv hΓ
      exact (henv.headInversion.sort_rigid hΓ (henv.projectionRigid hi')
        ((hFA.uniqU henv hΓ hf).typeChain henv hΓ hA).symm).elim
    | arrow A B =>
      obtain ⟨T, hFT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
      obtain ⟨ps, rfl, _⟩ := proofErase_const_spine_inv ET
      obtain ⟨_, hT⟩ := hFT.isType henv hΓ
      exact (IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hi') hT
        (hFT.uniqU henv hΓ hf)).elim
    | atom =>
      change env.HasType univs Γ f Atom.type at hf
      rw [EA] at hf
      obtain ⟨rfl, rfl⟩ := proofErase_native_nullary_structure_family hstep hΓ hf hi hi' RN
      cases henv.ordered.projections_unique hi hi'
      obtain ⟨_, hS⟩ := hf.isType henv hΓ
      have hzero := (StructureReplay.family_instance_levels hi hΓ hS).2
      obtain ⟨T, hFT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RN
      obtain ⟨ps, rfl, Eps⟩ := proofErase_const_spine_inv ET
      have Eps : ps = [] := List.map_eq_nil_iff.1 Eps.symm
      subst ps
      obtain ⟨_, hT⟩ := hFT.isType henv hΓ
      have hnil := (StructureReplay.family_instance_levels hi hΓ hT).2.trans hzero.symm
      have hnil := List.length_eq_zero_iff.1 hnil
      subst_vars
      exact ⟨rfl, by simp [nativeStructureOutput, hz, ProofShape.mkApps]⟩

/-- Primitive observation preservation extends to all compatible paths. Node
typings supply the ordinary context interpretations needed at changed binders. -/
theorem Obs.compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b S t o}, Step Δ a b → Obs c Δ S a t o → Obs c Δ S b t o)
    (R : ScopedCompute Step Δ source out) (HS : S.Typed Δ) (H : Obs c Δ S source t o) :
    Obs c Δ S out t o := by
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
    obtain ⟨Γ, f, hΓ, EΓ, hf, Ef⟩ := H.typing
    obtain ⟨A, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
    have EΓA : proofEraseCtx (A :: Γ) = D :: Δ := by simp only [proofEraseCtx, EA, EΓ]
    have SD : DomainSort Δ D u := ⟨Γ, A, hΓ, EΓ, hA, EA⟩
    obtain ⟨A', HA', EA'⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA RA
    have HC : IsDefEqCtx env univs [] (A :: Γ) (A' :: Γ) := .succ (.refl hΓ) HA'
    have WC : ContextSubstitution (D :: Δ) (D' :: Δ) ProofShape.Subst.id := by
      intro Γ₀ hΓ₀ EΓ₀
      have HH := AtomicControl.control_context_substitution HC hΓ₀ (EΓA.trans EΓ₀.symm).symm
      simpa only [proofEraseCtx, EA', EΓ] using HH
    cases H with
    | lam HL HK HB =>
      exact .lam HT HK ((ihb (HS.cons HL.lam_parts.2 SD) HB).context WC)

/-- Every finite enriched stage preserves dependent rigid-head demands.
Visible profiles exclude structure majors even with arbitrary ignored domains. -/
theorem static_structure_stage_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (hc : env.Rigid info.ctorName) (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs) :
    ∀ stage {Δ a b S t o}, ErasedStaticStructureEtaExpansionStage D stage Δ a b →
      Obs info.ctorName Δ S a t o → Obs info.ctorName Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b S t o R H
    rcases R with (R | R) | R
    · exact (erased_iota_primitive_no_rigid hc hD R
        (H.primitive_head (erased_iota_primitive_head R))).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const HL hw =>
        cases H with
        | terminal HT =>
          cases HL
          exact .terminal (HT.compute
            (erased_static_structure_eta_expansion_stage_descent heq hs 0)
            (.base (.inl (.inr (.const .nil hw)))))
    · cases R; exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b S t o R H
    rcases R with R | R | R | R | R | R
    · exact ih R H
    · have hh := H.primitive_head R.2.head
      cases R.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans hh)
        exact (V.not_rigid (hn ▸ hc)).elim
    · have hh := H.primitive_head R.head
      cases R with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        exact (hc.pats _ _ hp (by
          simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj hh)).elim
    · exact H.native_identity (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · obtain ⟨rfl, rfl⟩ := masked_structure_terminal
        (erased_static_structure_eta_expansion_stage_descent heq hs stage) hi hz EA H.typing R
      have HD := H.demand
      cases HD
      exact .terminal (H.typing.compute
        (erased_nativeMaskedStructureExpansion_descent
          (erased_static_structure_eta_expansion_stage_descent heq hs stage)) (.base R))

/-- Full-union compatible computation preserves the dependent observation.
Native images are not required to transport these ordinary typing witnesses. -/
theorem Obs.static_structure_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hz : info.numFields = 0)
    (EA : Atom.type = .const family [])
    (hc : env.Rigid info.ctorName) (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out)
    (HS : S.Typed Δ) (H : Obs info.ctorName Δ S source t o) : Obs info.ctorName Δ S out t o :=
  H.compute (erased_static_structure_eta_expansion_union_descent heq hs)
    (fun ⟨stage, R⟩ H => static_structure_stage_observation heq hs hi hz EA hc hD stage R H) R HS

end Lean4Lean.VEnv.Strengthening.AtomicUnitObservation
