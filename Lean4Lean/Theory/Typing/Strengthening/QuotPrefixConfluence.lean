import Lean4Lean.Theory.Typing.Strengthening.ClosedQuotPrefix
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointQuotRepair
import Lean4Lean.Theory.Typing.Strengthening.PrefixConfluence

/-! # Exact prefix confluence for the quotient-repaired declarations

The extra closed declaration is already a checked zero-argument quotient
prefix. Replacing it preserves literal paths in both directions. Thus existing
typed prefix confluence applies to the collection used by repaired joint stages.
This does not supply erased certificates for the residual singleton prefixes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params] {D D' : Definitions}

private theorem compute_replace
    (hd : ∀ Γ c ls rhs, D.unfolds c ls rhs → PrefixCompute D' Γ (.const c ls) rhs)
    (R : Compute D a b) : PrefixCompute D' Γ a b := by
  induction R generalizing Γ with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta => exact .base (.base (.base .beta))
  | delta H => exact hd _ _ _ _ H
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

private theorem projection_replace
    (hd : ∀ Γ c ls rhs, D.unfolds c ls rhs → PrefixCompute D' Γ (.const c ls) rhs)
    (R : ProjectionCompute D a b) : PrefixCompute D' Γ a b := by
  induction R generalizing Γ with
  | base H => exact compute_replace hd H
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | projIota hi hl hg => exact .base (.base (.projIota hi hl hg))
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

private theorem pattern_replace
    (hd : ∀ Γ c ls rhs, D.unfolds c ls rhs → PrefixCompute D' Γ (.const c ls) rhs)
    (R : PatternCompute D a b) : PrefixCompute D' Γ a b := by
  induction R generalizing Γ with
  | base H => exact projection_replace hd H
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | pattern hp hm hc => exact .base (.pattern hp hm hc)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Replace every declaration step by a checked prefix path in each context.
The path endpoints are unchanged, without any source typing premise. -/
theorem PureObservation.PrefixCompute.of_equations
    (hd : ∀ Γ c ls rhs, D.unfolds c ls rhs → PrefixCompute D' Γ (.const c ls) rhs)
    (R : PrefixCompute D Γ a b) : PrefixCompute D' Γ a b := by
  induction R with
  | base H => exact pattern_replace hd H
  | singleton H => exact .singleton H
  | quotient H => exact .quotient H
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

namespace ErasedQuotCore

/-- Restoring the closed quotient declaration does not change actual checked
prefix computation, including in contexts that are not assumed well formed. -/
theorem prefix_iff (hq : QuotRegistered env) :
    PrefixCompute (definitions hq) Γ a b ↔ PrefixCompute ErasedCore.definitions Γ a b := by
  constructor
  · apply PrefixCompute.of_equations
    rintro Δ c ls rhs ((H | ⟨rfl, u, v, rfl, hu, hv, hz, rfl⟩) | H)
    · exact .base (.base (.base (.delta (.inl H))))
    · exact .quotient (ClosedQuot.zero_prefix henv hq hu hv hz)
    · exact .base (.base (.base (.delta (.inr H))))
  · exact PrefixCompute.of_equations
      (fun _ _ _ _ H => .base (.base (.base (.delta (includes_core hq H)))))

/-- Exact confluence of the repaired actual prefix relation from typed sources.
The residual paths include checked singleton prefixes; their erased joint
certificates are not asserted by this theorem. -/
theorem prefix_confluent (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (RA : PrefixCompute (definitions hq) Γ e a)
    (RB : PrefixCompute (definitions hq) Γ e b) :
    ∃ out, PrefixCompute (definitions hq) Γ a out ∧
      PrefixCompute (definitions hq) Γ b out := by
  obtain ⟨out, HA, HB⟩ := ((prefix_iff hq).1 RA).confluent hcon hΓ ht ((prefix_iff hq).1 RB)
  exact ⟨out, (prefix_iff hq).2 HA, (prefix_iff hq).2 HB⟩

end ErasedQuotCore
end Lean4Lean.VEnv.Strengthening
