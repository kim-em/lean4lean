import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonGuardSubstitution

/-! # Substitution of general singleton primitives at typed sources

A source realization suffices to transport the exact general primitive through
a typed simultaneous substitution. Adding existence of such a realization to
the primitive yields an unconditional context-substitution law; the actual raw
guard and output still come from the fixed code, independently of that witness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature
open private const_spine_ne_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrimitive
variable [Params]

/-- General raw singleton computation transports exactly through a typed source
substitution, assuming descent and substitution for its recursive guard relation. -/
theorem proofErase_scoped_singleton_prefix_subst (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedSingletonPrefixPrimitive Step (proofEraseCtx Γ) (proofErase Γ e) out) :
    ProofShape.ScopedSingletonPrefixPrimitive Step (proofEraseCtx Γ₀)
      ((proofErase Γ e).subst τ) (out.subst τ) := by
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro C args domains result V ha hcalc HG =>
    have hn : ¬ IsProof Γ e := by
      intro hp
      exact const_spine_ne_proof (hsrc.symm.trans (proofErase_eq_proof.2 hp))
    obtain ⟨original, rfl, rfl⟩ := proofErase_const_spine_inv hsrc
    simp only [List.length_map] at ha
    obtain ⟨program, hg, hd, HG⟩ := V.realize heq W.wf ha ⟨_, ht⟩ hcalc HG
    have HC := V.check heq hstep W.wf hg ⟨_, ht⟩ HG
    have hg' := RecursorData.singletonUnfolding_subst henv V.registered V.large V.zero
      V.recType_eq (V.registered.recursorType_closed henv V.recType_eq) hg (σ := σ)
    have ht' : env.HasType univs Γ₀
        (mkApps (.const C.data.name C.levels) (original.map (·.subst σ))) (T.subst σ) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst_const] using ht.subst henv.orderedStrong W hΓ₀
    have HG' := V.family_guard_subst heq hsubst hΓ₀ W E hg ⟨_, ht⟩ HG
    have HC' := V.check heq hstep hΓ₀ hg' ⟨_, ht'⟩ HG'
    have hn' : ¬ IsProof Γ₀
        (mkApps (.const C.data.name C.levels) (original.map (·.subst σ))) := by
      simpa only [VExpr.subst_mkApps, VExpr.subst_const] using
        mt (isProof_subst hΓ₀ W ht).1 hn
    have HE := V.output_eq heq W.wf hg HC hn
    rw [hd] at HE
    have HE' := V.output_eq heq hΓ₀ hg' HC' hn'
    have HS := proofErase_subst_with hΓ₀ W (HC.defeq henv W.wf).hasType.2 E
    rw [← program.subst_rhs (HC.templateScope henv).2.1, HE', HE] at HS
    rw [← hsrc, ← proofErase_subst_with hΓ₀ W ht E, VExpr.subst_mkApps, VExpr.subst_const,
      proofErase_const_spine hΓ₀ ht' hn', ← HS]
    exact .intro V (by simpa only [List.length_map] using ha) (V.telescope_eq hΓ₀ hg' ⟨_, ht'⟩)
      ((V.guard_iff heq hΓ₀ hg' ⟨_, ht'⟩).2 HG')

namespace ProofShape
/-- Existence of a well-formed typed realization of a raw source at its raw
context. No particular representative is chosen by subsequent primitive rules. -/
def TypedSource (Δ : List ProofShape) (e : ProofShape) : Prop :=
  ∃ Γ a T, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.HasType univs Γ a T ∧ proofErase Γ a = e

/-- Typed sources transport along every interpreted raw context substitution. -/
theorem TypedSource.subst (H : TypedSource Δ e) (W : ContextSubstitution Δ Δ' τ) :
    TypedSource Δ' (e.subst τ) := by
  obtain ⟨Γ, a, T, hΓ, EΓ, ht, HE⟩ := H
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ EΓ
  exact ⟨Γ₀, a.subst σ, T.subst σ, hΓ₀, EΓ₀, ht.subst henv.orderedStrong WS hΓ₀,
    (proofErase_subst_with hΓ₀ WS ht ES).trans (congrArg (·.subst τ) HE)⟩

/-- The general singleton primitive restricted to sources with a typed
realization. Its guard, computed telescope, and exact output are unchanged. -/
def ScopedTypedSingletonPrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (e out : ProofShape) : Prop :=
  TypedSource Δ e ∧ ScopedSingletonPrefixPrimitive Step Δ e out

/-- The typed general primitive transports under every context interpretation.
Existence of a source realization supplies the semantic fresh-variable transport. -/
theorem ScopedTypedSingletonPrimitive.subst (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : ScopedTypedSingletonPrimitive Step Δ e out) (W : ContextSubstitution Δ Δ' τ) :
    ScopedTypedSingletonPrimitive Step Δ' (e.subst τ) (out.subst τ) := by
  refine ⟨H.1.subst W, ?_⟩
  obtain ⟨Γ, a, T, hΓ, EΓ, ht, HE⟩ := H.1
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ EΓ
  have HR : ScopedSingletonPrefixPrimitive Step (proofEraseCtx Γ) (proofErase Γ a) out := by
    rw [EΓ, HE]
    exact H.2
  have HH := proofErase_scoped_singleton_prefix_subst heq hstep hsubst hΓ₀ WS ES ht HR
  rwa [EΓ₀, HE] at HH
end ProofShape

/-- Restricting general singleton primitives to typed sources preserves descent. -/
theorem erased_scoped_typed_singleton_descent (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (ProofShape.ScopedTypedSingletonPrimitive Step) :=
  fun hΓ hΓ' W ht R => erased_scoped_singleton_prefix_descent heq hstep hΓ hΓ' W ht R.2

/-- Typed general singleton primitives retain exact operational replay. -/
theorem erased_scoped_typed_singleton_replay (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrefixReplay D (ProofShape.ScopedTypedSingletonPrimitive Step) :=
  fun hΓ ht R => erased_scoped_singleton_prefix_replay heq hstep hΓ ht R.2

end Lean4Lean.VEnv.Strengthening
