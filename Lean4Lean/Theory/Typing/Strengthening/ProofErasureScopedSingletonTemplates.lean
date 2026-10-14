import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonFamilyTemplate
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSingletonPrefix

/-! # Scoped singleton guards stated using fixed erased templates

Both endpoints are built from declaration templates and raw parameter/index
providers. The major has already become a proof marker. Exact specialization
connects this raw guard to generated-prefix descent without asserting coverage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PropElim InductiveSignature
variable [Params] {S : SingletonLayout} {E : PropElim} {params : List VExpr}

/-- The raw singleton guard compares fixed transported/requested templates at
erased parameter and index providers. It carries no original major proof. -/
def ScopedSingletonFamilyGuard
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (S : SingletonLayout) (params : List VExpr) (E : PropElim)
    (ps idx : List ProofShape) : Prop :=
  ProofShape.ScopedCompare Step Δ true
    ((erasedTransportedFamilyTemplate S params E).instOuter (ps ++ idx ++ [.proof]))
    ((erasedRequestedFamilyTemplate S params E).instOuter (ps ++ idx ++ [.proof]))

/-- At any typed occurrence, the raw template guard is exactly the contextual
family comparison, without requiring either family conversion or bare fields. -/
theorem scoped_singleton_family_template_iff (heq : env.HasCanonicalEq)
    (W : E.WF S params env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hps : ps.length = params.length)
    (hargs : TelInst env univs Γ (singletonOccurrenceDomains S params E) (ps ++ idx ++ [m])) :
    GuardedSingleton.ScopedFamilyComparison Step Γ
      (transportedFamily S params E ps idx m) (mkApps E.family (ps ++ idx)) ↔
      ScopedSingletonFamilyGuard Step (proofEraseCtx Γ) S params E
        (ps.map (proofErase Γ)) (idx.map (proofErase Γ)) := by
  unfold GuardedSingleton.ScopedFamilyComparison ScopedSingletonFamilyGuard
  rw [proofErase_transportedFamily_template heq W hΓ hps hargs,
    proofErase_requestedFamily_template W hΓ hps hargs]

/-- A generated prefix's contextual family guard is exactly the fixed-template
raw guard beneath its erased residual telescope. Only source typing is needed
to identify it; guard coverage and validity remain separate questions. -/
theorem scoped_singleton_prefix_template_iff (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args)) :
    GuardedSingleton.FamilyGuard (GuardedSingleton.ScopedFamilyComparison Step)
      Γ data levels args program S E ↔
      let Δ := program.domains.reverse ++ Γ
      let all := (data.openedArguments args).map (proofErase Δ)
      ScopedSingletonFamilyGuard Step
        ((proofEraseDomains Γ program.domains).reverse ++ proofEraseCtx Γ)
        S (data.propParams levels) E (all.take data.numParams)
        ((all.drop data.indexOffset).take data.numIndices) := by
  dsimp only
  obtain ⟨_, _, hlv, hlvlen, hseq, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : levels.length = data.uvars := by
    rw [hlv] at hlvlen
    exact hlvlen.trans (RecursorData.singletonEquation_uvars hseq)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq hseq
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  obtain ⟨hctx, hps, _, _, _, _, hargs⟩ :=
    GuardedSingleton.registered_opened_args henv hΓ H hlarge hzero hw hlen howner hS hE hg ht W
  simpa only [GuardedSingleton.FamilyGuard, List.map_take, List.map_drop, proofEraseDomains_context] using
    scoped_singleton_family_template_iff (Step := Step) heq W hctx hps hargs

end Lean4Lean.VEnv.Strengthening
