import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFiniteIndexEvidence

/-! # Interpret native unit origins through strictly smaller type children

An original strong derivation retains more information than its erased endpoint
histories. If either endpoint is a variable declared at a nullary empty
structure, its native-to-selected type trace consists of original type children
strictly below the parent rank. Interpreting those children constructs a whole
paired interpreter directly, including the transitivity constructor in this
case. No composition law for bare term histories is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Fold the original strictly ranked type edges into current ground-tree
transport. Each intermediate assignment comes from the trace's ordinary type
equality. No composed or symmetrized strong derivation is submitted to the
handler, and every handler invocation keeps its original rank below bound. -/
theorem BoundedTypeTrace.ground_tree_transport
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (H : BoundedTypeTrace env univs bound Γ A B)
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertTreeTransport D (proofEraseCtx Γ)
        (.plain .ground) (proofErase Γ X) (.plain .ground) (proofErase Γ Y)) :
    PiInertTreeTransport D (proofEraseCtx Γ)
      (.plain .ground) (proofErase Γ A) (.plain .ground) (proofErase Γ B) := by
  induction H with
  | refl =>
    intro Λ σ W a b X HA HB
    exact X
  | step hlt trace HE ih =>
    have HAB :=
      (trace.forget.defeq hΓ ⟨u, hA⟩).of_l henv hΓ hA
    intro Λ σ W a b X HA HB
    exact PiInertTreeTransport.trans_typed hΓ HAB (ih hA) (edge hlt HE) W X HA HB

/-- A native unit carrier and a ranked conversion trace construct the entire
ground paired interpreter at the selected type. The two endpoints need only
be assigned the selected type; trace equality supplies their native typings.
The only semantic hypotheses concern original lower-rank conversion edges. -/
theorem BoundedTypeTrace.unit_ground_interpretation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (trace : BoundedTypeTrace env univs bound Γ (.const family ls) T)
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertTreeTransport D (proofEraseCtx Γ)
        (.plain .ground) (proofErase Γ X) (.plain .ground) (proofErase Γ Y)) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ T) (proofErase Γ T)
      (.plain .ground) (.plain .ground) := by
  have HE := (trace.forget.defeq hΓ ⟨u, hS⟩).of_l henv hΓ hS
  have ES : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hS)
  have native := PiInertGuardedPairInterpretation.unit_ground hi hp hx hf hD
    (ES ▸ TypedAt.of_typed hΓ (HE.symm.defeq ha))
    (ES ▸ TypedAt.of_typed hΓ (HE.symm.defeq hb))
  have transport : PiInertTreeTransport D (proofEraseCtx Γ)
      (.plain .ground) (proofErase Γ (.const family ls)) (.plain .ground) (proofErase Γ T) :=
    trace.ground_tree_transport hΓ hS edge
  rw [ES] at transport
  exact native.convert_trees heq hs transport transport
    (.of_typed hΓ ha) (.of_typed hΓ hb)

/-- Any original strong comparison with a native unit variable at either
endpoint constructs its ground interpreter from strictly smaller type children.
The endpoint may have an opaque selected carrier, and the other endpoint is
unrestricted. No endpoint interpreter or term-composition law is assumed. -/
theorem StrongBounded.native_unit_ground_of_lower
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : StrongBounded env univs bound Γ a b T)
    (endpoint : a = .bvar i ∨ b = .bvar i)
    (lookup : Lookup Γ i (.const family ls))
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertTreeTransport D (proofEraseCtx Γ)
        (.plain .ground) (proofErase Γ X) (.plain .ground) (proofErase Γ Y)) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ T) (proofErase Γ T)
      (.plain .ground) (.plain .ground) := by
  obtain ⟨S, hlookup, trace⟩ := H.variable_assignment_trace endpoint
  cases lookup.uniq hlookup
  obtain ⟨u, hS⟩ := IsType.lookup henv hΓ lookup
  exact trace.unit_ground_interpretation heq hs hi hp hx hf hD hΓ hS
    H.strong.defeq.hasType.1 H.strong.defeq.hasType.2 edge

/-- The original transitivity constructor is interpreted in the native-unit
endpoint case. Its children are used as original derivations to extract the
typing origin; their erased histories are not composed. Every semantic type
handler call is strictly below the rank-(k+1) parent. This does not cover
general transitivity or construct the lower-rank handlers themselves. -/
theorem StrongBounded.trans_native_unit_ground_of_lower
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (left : StrongBounded env univs k Γ a m T)
    (right : StrongBounded env univs k Γ m b T)
    (endpoint : a = .bvar i ∨ b = .bvar i)
    (lookup : Lookup Γ i (.const family ls))
    (edge : ∀ {j X Y v}, j < k+1 → StrongBounded env univs j Γ X Y (.sort v) →
      PiInertTreeTransport D (proofEraseCtx Γ)
        (.plain .ground) (proofErase Γ X) (.plain .ground) (proofErase Γ Y)) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ T) (proofErase Γ T)
      (.plain .ground) (.plain .ground) :=
  (StrongBounded.trans left right).native_unit_ground_of_lower heq hs hi hp hx hf hD hΓ
    endpoint lookup edge

/-- The ranked native-unit construction supplies the finite index histories
consumed by arbitrary Eq recursors, with all typed substitutions and all
core-world futures. It does not ask for a uniform stage over substitutions. -/
theorem StrongBounded.native_unit_finite_history_of_lower
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : StrongBounded env univs bound Γ a b T)
    (endpoint : a = .bvar i ∨ b = .bvar i)
    (lookup : Lookup Γ i (.const family ls))
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertTreeTransport D (proofEraseCtx Γ)
        (.plain .ground) (proofErase Γ X) (.plain .ground) (proofErase Γ Y)) :
    PiInertFiniteHistory D (proofEraseCtx Γ) (proofErase Γ T) (proofErase Γ a) (proofErase Γ b) := by
  have result := H.native_unit_ground_of_lower heq hs hi hp hx hf hD hΓ endpoint lookup edge
  intro Λ σ W
  exact result.empty_finite_history W

end Lean4Lean.VEnv.Strengthening
