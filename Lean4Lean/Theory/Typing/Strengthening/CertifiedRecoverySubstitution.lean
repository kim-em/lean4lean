import Lean4Lean.Theory.Typing.Strengthening.RecoveredComparison
import Lean4Lean.Theory.Typing.Strengthening.BidirectionalApplication
import Lean4Lean.Theory.Typing.Strengthening.RecoverySubstitutionCore

/-! # Substitution with a recovered argument type

Exact recovery is not preserved by arbitrary typed substitution. Supplying a
recovery certificate for the argument at the substituted declaration discharges
the variable case and preserves the full selected output type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- Substituting a recoverable argument into a lookup preserves its exact type.
The substituted occurrence uses that argument certificate; other occurrences
remain lookups, with the appropriate weakening under subsequent binders. -/
theorem TypeRecovery.lookup_instN
    (Rx : TypeRecovery D depth Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (h : Lookup Γ₁ i T) :
    TypeRecovery D depth Γ ((.bvar i : VExpr).inst x k) (T.inst x k) :=
  TypeRecoveryWith.lookup_instN
    (fun W H => H.weakN (fun W H => KCertificate.weakN W H) W) Rx W h

/-- Exact output preservation holds when the argument itself recovers the
source declaration type. Source well-formedness supplies the intermediate type
needed by substitution of certified K computations. -/
theorem TypeRecovery.instN_of_recovery (R : TypeRecovery D depth Γ₁ e T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecovery D depth Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ht : VExpr.WF env univs Γ₁ e) :
    TypeRecovery D depth Γ (e.inst x k) (T.inst x k) :=
  TypeRecoveryWith.instN_to R (CertifiedKCompute.computeDescent heq hs)
    (fun W H => H.weakN (fun W H => KCertificate.weakN W H) W)
    (fun hΓ W ht H => CertifiedKCompute.instN H heq hs hΓ hx W ht) hΓ₁ hx Rx W ht

/-- Both comparison modes survive homogeneous substitution with a recovered
argument type. This does not assert the heterogeneous or arbitrary-argument law
needed for every delayed beta comparison. -/
theorem RecoveredComparison.instN_of_recovery
    (H : RecoveredComparison D depth mode Γ₁ a b)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (Rx : TypeRecovery D depth Γ₀ x A₀) (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) :
    RecoveredComparison D depth mode Γ (a.inst x k) (b.inst x k) := by
  induction H generalizing k Γ with
  | base H => exact .base (H.instN hx W)
  | app hf hg ha hb _ _ ihf iha =>
    exact .app (hf.instN henv W hx) (hg.instN henv W hx) (ha.instN henv W hx)
      (hb.instN henv W hx) (ihf hΓ₁ W) (iha hΓ₁ W)
  | recover Ra Rb HT Hab ihT ihab =>
    obtain ⟨_, hab⟩ := Hab.defeq hΓ₁
    exact .recover (Ra.instN_of_recovery heq hs hΓ₁ hx Rx W ⟨_, hab.hasType.1⟩)
      (Rb.instN_of_recovery heq hs hΓ₁ hx Rx W ⟨_, hab.hasType.2⟩) (ihT hΓ₁ W) (ihab hΓ₁ W)
  | sameType Ra Rb Hab ih =>
    obtain ⟨_, hab⟩ := Hab.defeq hΓ₁
    exact .sameType (Ra.instN_of_recovery heq hs hΓ₁ hx Rx W ⟨_, hab.hasType.1⟩)
      (Rb.instN_of_recovery heq hs hΓ₁ hx Rx W ⟨_, hab.hasType.2⟩) (ih hΓ₁ W)

end Lean4Lean.VEnv.Strengthening
