import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryDescent

/-! # Recovery with context-indexed type computation

Each conversion runs in the context of the recovered expression. Recovery under
a displayed binder extends that context, so carrier-aware computation may use
its actual domain. Proof markers still have no independent recovery rule.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

namespace ProofShape
/-- Syntax-directed recovery with contextual conversion. This retains the raw
recovery rules, including projection recipes, while recording every binder's scope. -/
inductive ScopedTypeRecovery (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → ProofShape → ProofShape → Prop where
  | bvar : ScopedTypeRecovery Step Δ (.bvar i) (contextOracle Δ i)
  | sort : u.WF univs → ScopedTypeRecovery Step Δ (.sort u) (.sort (.succ u))
  | const : env.constants c = some ci → (∀ l ∈ ls, l.WF univs) → ls.length = ci.uvars →
      ScopedTypeRecovery Step Δ (.const c ls) (proofErase [] (ci.type.instL ls))
  | lam : ScopedTypeRecovery Step (A :: Δ) b B →
      ScopedTypeRecovery Step Δ (.lam A b) (.forallE A B)
  | app : ScopedTypeRecovery Step Δ f (.forallE A B) →
      ScopedTypeRecovery Step Δ (.app f a) (B.inst a)
  | forallE : ScopedTypeRecovery Step Δ A (.sort u) →
      ScopedTypeRecovery Step (A :: Δ) B (.sort v) →
      ScopedTypeRecovery Step Δ (.forallE A B) (.sort (.imax u v))
  | proj {s : Name} {info : VProjectionInfo} {ls : List VLevel}
      {doms : List VExpr} {result : VExpr} {j : Nat} {args : List ProofShape} :
      env.projections s info → ProjTele env univs s info ls doms result →
      (hj : info.nparams + j < doms.length) → args.length = info.nparams + info.nindices →
      ScopedTypeRecovery Step Δ m (mkApps (.const s ls) args) →
      ScopedTypeRecovery Step Δ (.proj s j m) (projectionType s info doms j hj args m)
  | convert : ScopedTypeRecovery Step Δ e T → ScopedCompute Step Δ T T' → ScopedTypeRecovery Step Δ e T'

/-- Enlarging contextual computation preserves every recovery certificate. -/
theorem ScopedTypeRecovery.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (R : ScopedTypeRecovery Step Δ e T) : ScopedTypeRecovery Step' Δ e T := by
  induction R with
  | bvar => exact .bvar
  | sort h => exact .sort h
  | const hc hw hn => exact .const hc hw hn
  | lam _ ih => exact .lam ih
  | app _ ih => exact .app ih
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | proj hi HT hj hlen _ ih => exact .proj hi HT hj hlen ih
  | convert _ H ih => exact .convert ih (H.mono hstep)

/-- Old recovery embeds whenever each old primitive has a contextual simulation.
The simulation is required at every binder scope, not just at the outer context. -/
theorem TypeRecovery.scoped
    (hstep : ∀ {Δ a b}, Step a b → ScopedCompute Step' Δ a b)
    (R : TypeRecovery Step (contextOracle Δ) e T) : ScopedTypeRecovery Step' Δ e T := by
  generalize hσ : contextOracle Δ = σ at R
  induction R generalizing Δ with
  | bvar => cases hσ; exact .bvar
  | sort h => exact .sort h
  | const hc hw hn => exact .const hc hw hn
  | lam _ ih => exact .lam (ih (by simp only [contextOracle, hσ]))
  | app _ ih => exact .app (ih hσ)
  | forallE _ _ ihA ihB => exact .forallE (ihA hσ) (ihB (by simp only [contextOracle, hσ]))
  | proj hi HT hj hlen _ ih => exact .proj hi HT hj hlen (ih hσ)
  | convert _ H ih => exact .convert (ih hσ) (H.scoped hstep)

/-- Recovery of a variable's type consists solely of computation from its
context lookup. This gives a direct test for missing Pi exposure. -/
theorem ScopedTypeRecovery.bvar_compute
    (R : ScopedTypeRecovery Step Δ (.bvar i) T) :
    ScopedCompute Step Δ (contextOracle Δ i) T := by
  generalize E : ProofShape.bvar i = e at R
  induction R with
  | bvar => cases E; exact .refl
  | convert _ H ih => exact (ih E).trans H
  | sort | const | lam | app | forallE | proj => cases E
end ProofShape

/-- Contextual computation transports along an ordinary typed substitution.
Both endpoint erasures follow their supplied original typings. -/
theorem proofErase_scoped_compute_subst
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute Step (proofEraseCtx Γ₀)
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  let τ : ProofShape.Subst := fun i => proofErase Γ₀ (σ i)
  have E : ErasedSubstAgreement Γ Γ₀ σ τ := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W ha E, proofErase_subst_with hΓ₀ W hb E]
  exact H.subst hsubst (ProofShape.ContextSubstitution.of_typed hΓ₀ W E)

/-- A typed context thinning transports contextual type computations without
assuming recovery substitution or providing inhabitants for new binders. -/
theorem proofErase_scoped_compute_weak'
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompute Step (proofEraseCtx Γ')
      (proofErase Γ' (a.lift' ρ)) (proofErase Γ' (b.lift' ρ)) := by
  simpa only [← lift'_subst, subst_id] using
    proofErase_scoped_compute_subst hsubst hΓ' (substEq_of_thinning hΓ W) ha hb H

/-- A non-proof variable recovers any type reached by contextual computation
from its actual declared type. -/
theorem proofErase_scoped_lookup_recovery
    (hΓ : OnCtx Γ (env.IsType univs)) (hl : Lookup Γ i T) (hn : ¬ IsProof Γ (.bvar i))
    (R : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) out) :
    ProofShape.ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ (.bvar i)) out := by
  rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hn]
  have HR : ProofShape.ScopedTypeRecovery Step (proofEraseCtx Γ) (.bvar i) (proofErase Γ T) := by
    rw [← erasedTypeOracle_valid hΓ hl, ← proofEraseCtx_oracle]
    exact .bvar
  exact HR.convert R

end Lean4Lean.VEnv.Strengthening
