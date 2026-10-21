import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqNativeCarrierRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeSupplyJoin

/-! # Extracting computation of dependent residual telescopes

Each annotation computes in the original preceding binder context. Finite Pi
inversion extracts these paths from a computation of the whole residual type.
They can then wrap a body computation into a computation of generated lambdas.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

namespace ProofShape
/-- Pointwise telescope computation indexed by each source prefix context.
Annotations may depend on earlier binders, whose new values are not substituted
into the indexing context of later paths. -/
inductive ScopedTelescopeCompute (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → List ProofShape → List ProofShape → Prop where
  | nil : ScopedTelescopeCompute Step Δ [] []
  | cons : ScopedCompute Step Δ A A' → ScopedTelescopeCompute Step (A :: Δ) ds ds' →
      ScopedTelescopeCompute Step Δ (A :: ds) (A' :: ds')

/-- Telescope computation preserves the number of residual binders. -/
theorem ScopedTelescopeCompute.length_eq (R : ScopedTelescopeCompute Step Δ ds ds') :
    ds.length = ds'.length := by
  induction R with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- Telescope paths and a body path in the original full context assemble a
single computation of the wrapped lambda output. No body typing is required. -/
theorem ScopedTelescopeCompute.wrapLams (R : ScopedTelescopeCompute Step Δ ds ds')
    (RB : ScopedCompute Step (ds.reverse ++ Δ) b b') :
    ScopedCompute Step Δ (ProofShape.wrapLams ds b) (ProofShape.wrapLams ds' b') := by
  induction R with
  | nil => exact RB
  | cons RA RT ih =>
    apply ScopedCompute.lam RA
    apply ih
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using RB
end ProofShape

open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Peeling equally many binders from a typed type and one of its computed
outputs extracts both the annotation paths and a residual-body path. Every
path stays in the original prefix context. Sound replay and interpreted
primitive substitution handle all intermediate domain changes. -/
theorem proofErase_takeForalls_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) out)
    (HT : takeForalls count (proofErase Γ T) = some (ds, body))
    (HO : takeForalls count out = some (ds', body')) :
    ScopedTelescopeCompute Step (proofEraseCtx Γ) ds ds' ∧
      ScopedCompute Step (ds.reverse ++ proofEraseCtx Γ) body body' := by
  induction count generalizing Γ T u out ds body ds' body' with
  | zero => cases HT; cases HO; exact ⟨.nil, R⟩
  | succ count ih =>
    cases ET : proofErase Γ T <;> simp only [ET, ProofShape.takeForalls] at HT <;> try contradiction
    rename_i Araw Braw
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv ET
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    rw [ET, ← EA, ← EB] at R
    rw [← EA, ← EB] at HT
    obtain ⟨D, C, rfl, RD, RC⟩ := R.forallE_inv_typed hstep hsubst hhead hΓ hA rfl
    cases HB : takeForalls count (proofErase (A :: Γ) B) with
    | none => simp [HB] at HT
    | some p =>
      obtain ⟨ds₀, body₀⟩ := p
      simp only [HB, Option.pure_def] at HT
      cases HT
      cases HC : takeForalls count C with
      | none => simp [ProofShape.takeForalls, HC] at HO
      | some p' =>
        obtain ⟨ds₁, body₁⟩ := p'
        simp only [ProofShape.takeForalls, HC, Option.pure_def] at HO
        cases HO
        obtain ⟨RT, RB⟩ := ih hΓA hB RC HB HC
        refine ⟨.cons RD RT, ?_⟩
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, proofEraseCtx] using RB

/-- Computing a typed prefix's arguments computes every annotation of its
residual telescope. Successful target peeling supplies the target shape; the
existing native supply theorem constructs the whole residual-type path before
it is split. No exact recovery of the arguments or native type congruence law
is assumed. -/
theorem proofErase_computed_residual_telescope
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args residual)
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ)) (args.map (proofErase Γ)) args')
    (HT : ProofShape.takeForalls count (proofErase Γ residual) = some (ds, body))
    (HO : ProofShape.residualTelescope count args' (proofErase Γ T) = some (ds', body')) :
    ScopedTelescopeCompute Step (proofEraseCtx Γ) ds ds' ∧
      ScopedCompute Step (ds.reverse ++ proofEraseCtx Γ) body body' := by
  have hres : env.IsType univs Γ residual := by
    clear HA HT HO
    induction HW generalizing u with
    | nil => exact ⟨u, hT⟩
    | cons ha HW ih =>
      obtain ⟨_, v, hB⟩ := hT.forallE_inv henv
      exact ih (hB.instN henv Ctx.InstN.zero ha)
  obtain ⟨out, HS, R⟩ := proofErase_computed_native_supply hstep hhead hsubst hΓ hT HW .refl HA
  simp only [ProofShape.residualTelescope, HS] at HO
  exact proofErase_takeForalls_compute hstep hsubst hhead hΓ hres.choose_spec R HT HO

end Lean4Lean.VEnv.Strengthening
