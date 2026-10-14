import Lean4Lean.Theory.Typing.Strengthening.CertifiedKSubstitution
import Lean4Lean.Theory.Typing.Strengthening.TypeRecoveryCore

/-! # Recovery using finite certified K computations

This specializes the generic recovery rules to the original K computation.
All expression constructors are covered; conversion completeness is not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- The original recovery certificates use fixed-depth certified K computation. -/
abbrev TypeRecovery (D : Definitions) (depth : Nat) :=
  TypeRecoveryWith (CertifiedKCompute D depth)

namespace TypeRecovery
export TypeRecoveryWith (sort const bvar lam app forallE proj convert)
end TypeRecovery

/-- Certified K computation satisfies the generic scoped computation interface. -/
theorem CertifiedKCompute.computeDescent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ComputeDescent (CertifiedKCompute D depth) := by
  intro ρ Γ Γ' e target T R W hΓ hΓ' ht
  obtain ⟨out, hout, H⟩ := CertifiedKCompute.descend R heq hs W hΓ hΓ'
  exact ⟨out, hout, H _ ht⟩

/-- Recovery certificates survive finite binder insertion. -/
theorem TypeRecovery.weakN (W : Ctx.LiftN n k Γ Γ') (R : TypeRecovery D depth Γ e T) :
    TypeRecovery D depth Γ' (e.liftN n k) (T.liftN n k) :=
  TypeRecoveryWith.weakN (fun W H => H.weakN (fun W H => KCertificate.weakN W H) W) W R

/-- Reconstruction needs only source well-formedness. -/
theorem TypeRecovery.hasType (R : TypeRecovery D depth Γ e T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    env.HasType univs Γ e T :=
  TypeRecoveryWith.hasType R (CertifiedKCompute.computeDescent heq hs) hΓ ht

/-- The entire recovered type and its source typing descend. -/
theorem TypeRecovery.descend (R : TypeRecovery D depth Γ' (e.lift' ρ) T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    ∃ T₀, T = T₀.lift' ρ ∧ env.HasType univs Γ e T₀ :=
  TypeRecoveryWith.descend R (CertifiedKCompute.computeDescent heq hs) W hΓ hΓ' ht

/-- Recovered Pi typings provide scoped eta annotations. -/
theorem TypeRecovery.pi_below (R : TypeRecovery D depth Γ' (e.lift' ρ) (.forallE A B))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    ∃ A₀ B₀, A = A₀.lift' ρ ∧ B = B₀.lift' ρ.cons ∧ env.HasType univs Γ e (.forallE A₀ B₀) :=
  TypeRecoveryWith.pi_below R (CertifiedKCompute.computeDescent heq hs) W hΓ hΓ' ht

end Lean4Lean.VEnv.Strengthening
