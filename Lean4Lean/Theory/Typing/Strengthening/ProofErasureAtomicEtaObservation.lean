import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicControlObservation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiOriginTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRawBetaJoin

/-! # Neutral readout at opaque carriers through the full eta union

All guarded stages preserve typed neutral observations. This includes arbitrary
eta inside control wrappers and arbitrary computation of their annotations.
Distinct observed variables therefore stay distinct despite function eta.
-/
namespace Lean4Lean.VEnv.Strengthening.AtomicControl
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] [Atom]

/-- All primitive roots of every eta stage preserve the same typed demand. -/
theorem eta_stage_observation (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage {Δ a b S t o}, ErasedEtaExpansionStage D stage Δ a b →
      Obs Δ S a t o → Obs Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b S t o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const => exact (H.not_primitiveHead trivial).elim
    · cases R; exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b S t o R H
    rcases R with R | R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · exact H.native_identity (erased_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta (erased_eta_expansion_stage_descent heq hs stage) R

/-- Primitive observation preservation extends to all compatible paths. Node
typings supply the ordinary context interpretations needed at changed binders. -/
theorem Obs.compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b S t o}, Step Δ a b → Obs Δ S a t o → Obs Δ S b t o)
    (R : ScopedCompute Step Δ source out) (HS : S.Typed Δ) (H : Obs Δ S source t o) :
    Obs Δ S out t o := by
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
      have HH := control_context_substitution HC hΓ₀ (EΓA.trans EΓ₀.symm).symm
      simpa only [proofEraseCtx, EA', EΓ] using HH
    cases H with
    | lam HL HK HB =>
      exact .lam HT HK ((ihb (HS.cons HL.lam_parts.2 SD) HB).context WC)

/-- Arbitrary finite guard depth preserves typed neutral observations. -/
theorem Obs.eta_union (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedCompute (ErasedEtaExpansionUnion D) Δ source out)
    (HS : S.Typed Δ) (H : Obs Δ S source t o) : Obs Δ S out t o :=
  H.compute (erased_eta_expansion_union_descent heq hs)
    (fun ⟨stage, R⟩ H => eta_stage_observation heq hs stage R H) R HS

/-- A variable at the opaque carrier retains an exact beta readout through
all function-eta and singleton stages. Intermediate terms may contain arbitrary
constants, projections, changed annotations and nested control wrappers. -/
theorem eta_union_atomic_variable_persistence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (.bvar i) .atom)
    (R : ScopedCompute (ErasedEtaExpansionUnion D) Δ (.bvar i) out) :
    ProofShape.BetaRed out (.bvar i) := by
  let S : Sets := fun j t o => j = i ∧ t = .atom ∧ o = .pi
  have HS : S.Typed Δ := by rintro j t o ⟨rfl, rfl, rfl⟩; exact HT
  have H : Obs Δ S (.bvar i) .atom .pi := .var HT .atom ⟨rfl, rfl, rfl⟩
  exact ((H.eta_union heq hs R HS).forget
    (T := fun j o => j = i ∧ o = .pi) (fun _ _ _ h => ⟨h.1, h.2.2⟩)).variable_exposure

/-- Distinct variables at an opaque positive carrier cannot share a reduct in
the full function-eta union. This conclusion permits all singleton stages. -/
theorem eta_union_atomic_variables_no_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HI : ControlTyping Δ (.bvar i) .atom) (HJ : ControlTyping Δ (.bvar j) .atom)
    (hne : i ≠ j) :
    ¬ ∃ shared, ScopedCompute (ErasedEtaExpansionUnion D) Δ (.bvar i) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion D) Δ (.bvar j) shared := by
  rintro ⟨shared, RI, RJ⟩
  have RI := eta_union_atomic_variable_persistence heq hs HI RI
  have RJ := eta_union_atomic_variable_persistence heq hs HJ RJ
  obtain ⟨out, HI', HJ'⟩ := RI.raw_confluent RJ
  have EI := HI'.fixed_of_normal (Step := fun _ _ => False) ⟨by simp, trivial⟩
  have EJ := HJ'.fixed_of_normal (Step := fun _ _ => False) ⟨by simp, trivial⟩
  exact hne (ProofShape.bvar.inj (EI.symm.trans EJ))

end Lean4Lean.VEnv.Strengthening.AtomicControl
