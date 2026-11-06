import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixComponentDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPrefixArity

/-! # Type-valued roots cannot use function or structure eta

At a type-valued source, an escaping root must be a general singleton. A
saturated Eq.rec source has too many arguments for such a rule. Thus an Eq
probe's useful guarded occurrence must be sought at a proper prefix or another
nested position, not directly at its unchanged saturated root.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- An actual sort assignment excludes literal lambda syntax after erasure. -/
theorem ControlTyping.not_lam_sort (H : ControlTyping Δ (.lam A b) (.sort u)) : False := by
  obtain ⟨Γ, e, hΓ, _, ht, Ee⟩ := H
  obtain ⟨A₀, b₀, rfl, _, _, _⟩ := erase_lam_inv Ee
  obtain ⟨⟨v, hA⟩, B, hb⟩ := ht.lam_inv henv hΓ
  exact (ht.uniqU henv hΓ (HasType.lam hA hb)).sort_forallE_inv henv hΓ

/-- A specialized Eq-prefix root returns a literal lambda. Source-typed replay
therefore excludes this root at any independently sort-typed source. -/
theorem ControlTyping.no_eq_prefix_sort
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ControlTyping Δ e (.sort u)) (R : ComputedJointPrefixPrimitive Step Δ e out) : False := by
  have HT := H.compute (erased_computed_joint_prefix_descent heq hstep) (.base R)
  cases R with
  | intro HG => exact HT.not_lam_sort

/-- At a type-valued root outside the mixed fragment, only the general
singleton alternative remains. Its guard still uses a strictly earlier stage. -/
theorem static_sorted_root_outside_core_expansion
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ a (.sort u))
    (H : ErasedStaticStructureEtaExpansionStage D n Δ a b)
    (HN : ¬ ErasedLevelCoreExpansion D (ErasedStaticStructureEtaExpansionStage D n) Δ a b) :
    ∃ k, k < n ∧ CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D k) Δ a b := by
  obtain ⟨k, hk, HG⟩ := static_stage_outside_core_expansion (Nat.le_refl n) H HN
  have hd : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D k) :=
    erased_static_structure_eta_expansion_stage_descent heq hs k
  rcases HG with HG | HG | HG | HG
  · exact ⟨k, hk, HG⟩
  · exact (HT.no_eq_prefix_sort heq hd HG).elim
  · exact (HT.no_eta_sort hd HG).elim
  · exact (HT.no_masked_structure hd HG).elim

/-- A saturated Eq.rec has six arguments, while valid general singleton code
stops before its proof major. At a type-valued literal saturated spine, every
full-stage root is consequently ordinary core or controlled beta expansion. -/
theorem static_sorted_eq_rec_root_transparent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : ControlTyping Δ (ProofShape.eqRec v w α a M m b p) (.sort u))
    (H : ErasedStaticStructureEtaExpansionStage D n Δ (ProofShape.eqRec v w α a M m b p) out) :
    ErasedLevelCoreExpansion D (ErasedStaticStructureEtaExpansionStage D n) Δ
      (ProofShape.eqRec v w α a M m b p) out := by
  by_contra HN
  obtain ⟨k, hk, HG⟩ := static_sorted_root_outside_core_expansion heq hs HT H HN
  have hn := SingletonPrimitiveWith.eq_rec_arity_le
    (args := [α, a, M, m, b, p]) (ls := [v, w]) heq HG.2
  simp only [List.length_cons, List.length_nil] at hn
  omega

end Lean4Lean.VEnv.Strengthening
