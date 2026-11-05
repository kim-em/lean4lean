import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHeterogeneousControlTyping

/-! # Finite demands linking values to their native types

A type demand retains its value demand as data. Function keys also retain the
assigned input carrier, even for an empty argument-demand list. Thus a recovered
Pi cannot silently reinterpret an input key at a different control type.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Finite term demands and the corresponding native-type demands. -/
inductive Key where
  | unit
  | record
  | fn (domain : HeterogeneousControl.ControlType) (arguments : List Key) (result : Key)
  | type (value : Key)

/-- Each key fixes one ordinary closed control type. -/
def Key.control (unit record : AtomicControl.Atom) : Key → HeterogeneousControl.ControlType
  | .unit => .atom unit
  | .record => .atom record
  | .fn A _ result => .arrow A (result.control unit record)
  | .type value => .sort (value.control unit record).level

/-- Every demanded input must have the carrier recorded in its function key. -/
def Key.Valid (unit record : AtomicControl.Atom) : Key → Prop
  | .unit | .record => True
  | .fn A keys result =>
      (∀ key ∈ keys, key.control unit record = A ∧ key.Valid unit record) ∧ result.Valid unit record
  | .type value => value.Valid unit record
termination_by key => sizeOf key

/-- An annotation is ordinarily equal to a selected closed control type.
This witness alone supplies no dependent record-parameter provenance. -/
def TypeEquality (Δ : List ProofShape) (e : ProofShape) (t : HeterogeneousControl.ControlType) : Prop :=
  ∃ Γ A, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.IsDefEq univs Γ A t.expr (.sort t.level) ∧ proofErase Γ A = e

/-- An annotation equality supplies its positive universe typing. -/
theorem TypeEquality.typing (H : TypeEquality Δ e t) :
    HeterogeneousControl.ControlTyping Δ e (.sort t.level) := by
  obtain ⟨Γ, A, hΓ, EΓ, HE, EA⟩ := H
  exact ⟨Γ, A, hΓ, EΓ, HE.hasType.1, EA⟩

/-- Ordinary substitution preserves the annotation equality at its fixed
closed carrier. No native certificate is required for an image. -/
theorem TypeEquality.subst (H : TypeEquality Δ e t) (W : ContextSubstitution Δ Δ' σ) :
    TypeEquality Δ' (e.subst σ) t := by
  obtain ⟨Γ, A, hΓ, EΓ, HE, EA⟩ := H
  obtain ⟨Γ', τ, hΓ', EΓ', HT, ET⟩ := W hΓ EΓ
  refine ⟨Γ', A.subst τ, hΓ', EΓ', ?_, ?_⟩
  · simpa only [HeterogeneousControl.ControlType.expr_subst, VExpr.subst] using
      HE.subst henv.orderedStrong HT hΓ'
  · rw [proofErase_subst_with hΓ' HT HE.hasType.1 ET, EA]

/-- Complete annotation computation preserves its ordinary carrier equality. -/
theorem TypeEquality.compute (hstep : ErasedScopedPrimitiveDescent Step)
    (H : TypeEquality Δ e t) (R : ScopedCompute Step Δ e out) : TypeEquality Δ out t := by
  obtain ⟨Γ, A, hΓ, EΓ, HE, EA⟩ := H
  obtain ⟨A', HA', EA'⟩ := proofErase_scoped_compute_realize hstep hΓ HE.hasType.1 EΓ EA R
  exact ⟨Γ, A', hΓ, EΓ, HA'.symm.trans HE, EA'⟩

/-- The actual displayed annotation types its fresh variable at the selected
closed carrier. Positivity guarantees that the variable is retained. -/
theorem TypeEquality.fresh (H : TypeEquality Δ A t) :
    HeterogeneousControl.ControlTyping (A :: Δ) (.bvar 0) t := by
  obtain ⟨Γ, A₀, hΓ, EΓ, HE, EA⟩ := H
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, HE.hasType.1⟩
  have hx : env.HasType univs (A₀ :: Γ) (.bvar 0) t.expr := by
    have HX := (HE.weak henv.ordered).defeq (HasType.bvar .zero)
    simpa only [(t.closedN (k := 0)).lift_eq] using HX
  exact ⟨A₀ :: Γ, .bvar 0, hΓA, by simp only [proofEraseCtx, EA, EΓ], hx,
    if_neg (HeterogeneousControl.ControlType.not_isProof hΓA hx)⟩

/-- Annotated lambda typing supplies the ordinary equality of its displayed
input type and its closed control carrier. -/
theorem lambda_domain_equality
    (H : HeterogeneousControl.ControlTyping Δ (.lam A b) (.arrow domain result)) :
    TypeEquality Δ A domain := by
  obtain ⟨Γ, f, hΓ, EΓ, hf, Ef⟩ := H
  obtain ⟨A₀, b₀, rfl, _, EA, _⟩ :=
    erase_lam_inv Ef
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨_, HA⟩, _⟩ := ((HasType.lam hA hb).uniqU henv hΓ hf).forallE_inv henv hΓ
  have hW := (HeterogeneousControl.ControlTyping.of_typed hΓ hf).wf.1
  exact ⟨Γ, A₀, hΓ, EΓ, HA.toU.of_r henv hΓ (HeterogeneousControl.ControlType.typed hW), EA⟩

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
