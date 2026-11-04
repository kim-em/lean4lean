import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpineEtaDiamond

/-! # Native recovery while a neutral spine's arguments change

The head stays a fixed variable or named constant. Arguments may independently
share core reducts. Every native source certificate then supplies a target
certificate at a core reduct of its old output, with no target recovery premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

namespace ProofShape
/-- Same variable/constant head, with independently core-joined arguments.
Neither argument needs native recovery or a syntactic normal form. -/
inductive NativeSpineJoin (Core : ProofShape → ProofShape → Prop) : ProofShape → ProofShape → Prop where
  | bvar : NativeSpineJoin Core (.bvar i) (.bvar i)
  | const : NativeSpineJoin Core (.const c ls) (.const c ls)
  | app : NativeSpineJoin Core f g → ComputeJoin Core a b → NativeSpineJoin Core (.app f a) (.app g b)

/-- The structural spine relation supplies a join of the whole expressions. -/
theorem NativeSpineJoin.join (H : NativeSpineJoin Core a b) : ComputeJoin Core a b := by
  induction H with
  | bvar | const => exact .refl
  | app _ HA ih => exact ih.app HA

variable {Core : ProofShape → ProofShape → Prop} {body : ProofShape}

/-- A raw substitution-closed core is also closed under insertion of binders. -/
theorem core_liftN_of_subst
    (hs : ∀ {a b τ}, Core a b → Core (a.subst τ) (b.subst τ))
    (R : Core a b) : Core (a.liftN n k) (b.liftN n k) := by
  simpa only [subst_bvar_liftN] using hs (τ := fun i => .bvar (liftVar n i k)) R

/-- Computing an argument computes every occurrence in an instantiated body,
including occurrences below binders, without type-recovery assumptions. -/
theorem Compute.inst_argument_of_subst
    (hs : ∀ {a b τ}, Core a b → Core (a.subst τ) (b.subst τ))
    (R : Compute Core a b) : Compute Core (body.inst a) (body.inst b) := by
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
  apply Compute.subst_images (fun H => core_liftN_of_subst hs H)
  intro i
  cases i with
  | zero => exact R
  | succ i => exact .refl
end ProofShape

variable [Params]
/-- Source-typed native recovery transports across joined spine arguments.
The target certificate uses only the core; the old selected output computes
forward to the new output. Guard conversions need typed core joins, not source
confluence. No argument or target native certificate is assumed. -/
theorem proofErase_spine_native_transport
    (hstep : ErasedScopedPrimitiveDescent Source) (hc : TypedCoreConfluence Core)
    (hpi : ∀ {A B out}, ¬ Core (.forallE A B) out)
    (hsubst : ∀ {a b τ}, Core a b → Core (a.subst τ) (b.subst τ))
    (hjoin : ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) out → ComputeJoin Core (proofErase Γ e) out)
    (R : ScopedTypeRecovery Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (H : NativeSpineJoin Core source target) :
    ∃ out', ScopedTypeRecovery (fun _ => Core) Δ target out' ∧ Compute Core out out' := by
  induction R generalizing Γ e T target with
  | bvar => cases H; exact ⟨_, .bvar, .refl⟩
  | const hc hw hl => cases H; exact ⟨_, .const hc hw hl, .refl⟩
  | sort | lam | forallE | proj => cases H
  | app R ih =>
    cases H with
    | @app f₁ f₂ a₁ a₂ HF HA =>
      obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
      obtain ⟨_, _, hf, _⟩ := he.app_inv henv hΓ
      obtain ⟨out', RN, RC⟩ := ih hΓ hf EΓ Ef HF
      obtain ⟨X, Y, rfl, _, RY⟩ := RC.pi_parts hpi
      obtain ⟨arg, RA, RB⟩ := HA
      refine ⟨Y.inst arg, (ScopedTypeRecovery.app RN).convert ((RB.inst_argument_of_subst hsubst).scoped
        (fun H => .base H)), ?_⟩
      refine Compute.trans ?_ (RA.inst_argument_of_subst hsubst (body := Y))
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, Ea] using
        RY.subst hsubst (σ := ProofShape.Subst.one (proofErase Γ a))
  | convert R RC ih =>
    obtain ⟨out', RN, RO⟩ := ih hΓ he EΓ Ee H
    obtain ⟨A, htA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ he
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨_, hA⟩ := htA.isType henv hΓ
    have RC' := RC
    rw [← EΓ, ← EA] at RC'
    obtain ⟨shared, RA, RB⟩ := hjoin hΓ hA RC'
    obtain ⟨final, RN', RS⟩ := hc hΓ hA (EA ▸ RO) RA
    exact ⟨final, RN.convert (RN'.scoped (fun H => .base H)), RB.trans RS⟩

end Lean4Lean.VEnv.Strengthening
