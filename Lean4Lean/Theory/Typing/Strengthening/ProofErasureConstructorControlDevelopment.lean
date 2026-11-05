import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitConstructorReadout

/-! # Control developments with unrestricted annotation computation

Term nodes use the three actual control-expansion roots and beta. Displayed
lambda and Pi domains may use the entire enriched computation union. Thus the
observer's canonical closed carriers do not freeze operational annotations.
Record structure expansion at a term node still requires parameter coverage.
-/
namespace Lean4Lean.VEnv.Strengthening.UnitConstructorObservation
open _root_.Lean4Lean Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {unit record : AtomicControl.Atom}

/-- Compatible control computation permits full domain-annotation histories.
This is a restricted term language, not a synonym for the full enriched union. -/
inductive Development (D : PureObservation.Definitions) : List ProofShape → ProofShape → ProofShape → Prop where
  | refl : Development D Δ e e
  | root : ControlStep D Δ e out → Development D Δ e out
  | beta : Development D Δ (.app (.lam A b) a) (b.inst a)
  | trans : Development D Δ a b → Development D Δ b c → Development D Δ a c
  | app : Development D Δ f f' → Development D Δ a a' → Development D Δ (.app f a) (.app f' a')
  | proj : Development D Δ e e' → Development D Δ (.proj s i e) (.proj s i e')
  | lam : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ A A' →
      Development D (A :: Δ) b b' → Development D Δ (.lam A b) (.lam A' b')
  | forallE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ A A' →
      Development D (A :: Δ) B B' → Development D Δ (.forallE A B) (.forallE A' B')

/-- Every recorded development is an actual computation of the full union. -/
theorem Development.full (R : Development D Δ e out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ e out := by
  induction R with
  | refl => exact .refl
  | root R => exact .base R.full
  | beta => exact .beta .beta
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam RA _ ih => exact .lam RA ih
  | forallE RA _ ih => exact .forallE RA ih

/-- Observed bodies survive full changes of their displayed domains. The
fresh variable's ordinary control typing is transported by context conversion;
no native recovery of the new annotation by an argument is assumed. -/
theorem Obs.development (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : Development D Δ source out) (HS : S.Typed Δ)
    (H : Obs unit record c r Δ S source t o) : Obs unit record c r Δ S out t o := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionUnion D) :=
    erased_static_structure_eta_expansion_union_descent heq hs
  induction R generalizing S t o with
  | refl => exact H
  | root R => exact H.control_compute heq hs (.base R) HS
  | beta => exact H.beta_forward HS
  | trans _ _ ih₁ ih₂ => exact ih₂ HS (ih₁ HS H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF.full RX.full)
    cases H with
    | app _ HF HX => exact .app HT (ihf HS HF) (fun key hk => ihx HS (HX key hk))
  | proj => exact H.not_proj.elim
  | forallE => exact H.not_pi.elim
  | @lam Δ A A' b b' RA RB ihb =>
    have HT := H.typing.compute hstep (.lam RA RB.full)
    obtain ⟨Γ, f, hΓ, EΓ, hf, Ef⟩ := H.typing
    obtain ⟨A₀, body, rfl, _, EA, _⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hA⟩, _, _⟩ := hf.lam_inv henv hΓ
    have EΓA : proofEraseCtx (A₀ :: Γ) = A :: Δ := by simp only [proofEraseCtx, EA, EΓ]
    have SD : DomainSort Δ A u := ⟨Γ, A₀, hΓ, EΓ, hA, EA⟩
    obtain ⟨A₁, HA₁, EA₁⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA RA
    have HC : IsDefEqCtx env univs [] (A₀ :: Γ) (A₁ :: Γ) := .succ (.refl hΓ) HA₁
    have WC : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id := by
      intro Γ₀ hΓ₀ EΓ₀
      have HH := AtomicControl.control_context_substitution HC hΓ₀ (EΓA.trans EΓ₀.symm).symm
      simpa only [proofEraseCtx, EA₁, EΓ] using HH
    cases H with
    | lam HL HK HB => exact .lam HT HK ((ihb (HS.cons HL.lam_parts.2 SD) HB).context WC)

/-- Constructor readout includes every beta interleaving and full annotation
history represented by Development. Native structure steps at term nodes are
not covered by this theorem. -/
theorem application_development_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hne : unit ≠ record)
    (HF : HeterogeneousControl.ControlTyping Δ (.const r []) (.arrow (.atom unit) (.atom record)))
    (HX : HeterogeneousControl.ControlTyping Δ (.bvar i) (.atom unit))
    (HT : HeterogeneousControl.ControlTyping Δ (.app (.const r []) (.bvar i)) (.atom record))
    (R : Development D Δ (.app (.const r []) (.bvar i)) out) :
    BetaRed out (.app (.const r []) (.bvar i)) ∨
      BetaRed out (.app (.const r []) (.const c [])) := by
  have HS : (UnitSets unit i).Typed Δ := by
    rintro j t o ⟨rfl, rfl, rfl⟩
    exact HX
  have H : Obs unit record c r Δ (UnitSets unit i)
      (.app (.const r []) (.bvar i)) (.atom record) .pi :=
    .app HT (.rigid HF) (by
      intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact .var HX .atom ⟨rfl, rfl, rfl⟩)
  exact (H.development heq hs R HS).record_readout hne

end Lean4Lean.VEnv.Strengthening.UnitConstructorObservation
