import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredThinning
import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonPrefixDescent

/-! # Registered singleton prefixes guarded by recovered erased comparison

The generated family propositions may contain arbitrary data indices and
transported fields. A recursive erased comparison above inserted binders lowers
the guard, rebuilds the actual generated check, and replays the prefix below.
Coverage of arbitrary declarative family conversions remains open.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim Params
variable [Params] {S : SingletonLayout} {E : PropElim}

/-- The concrete recursive certificate used for a generated family guard. -/
def RecoveredFamilyComparison (D : PureObservation.Definitions) (stage : Nat)
    (Γ : List VExpr) (a b : VExpr) : Prop :=
  ErasedRecoveredComparison D stage true Γ a b

/-- Typed recovered comparison discharges the general
endpoint-descent interface, including arbitrary context thinnings. -/
theorem RecoveredFamilyComparison.descends (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) : EndpointDescent (RecoveredFamilyComparison D stage) := by
  intro ρ Γ Γ' a b A W hΓ hΓ' ha hb H
  exact ⟨_, ErasedRecoveredComparison.common_descend heq hs hΓ hΓ' W ha hb H⟩

/-- Guarded canonical Eq computation may use recovered inferred eta at any
compatible position of its endpoint certificate, and still replays below. -/
theorem recovered_K_descend
    (R : GuardedKCompute D (RecoveredFamilyComparison D stage) Γ' (e.lift' ρ) target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) :
    ∃ out, target = out.lift' ρ ∧ env.SimAt univs Γ e out :=
  R.descend heq hs (RecoveredFamilyComparison.descends heq hs) W hΓ hΓ'

/-- Replay the actual generated prefix below an arbitrary context thinning
using its upper erased family certificate. No upper declarative replay check or
lower result typing is assumed. Data fields and data indices are allowed. -/
theorem recovered_prefix_descend (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels (args.map (·.lift' ρ)) = some program)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) args) T)
    (HG : FamilyGuard (RecoveredFamilyComparison D stage) Γ' data levels (args.map (·.lift' ρ)) program S E) :
    ∃ out, program.rhs = out.lift' ρ ∧
      env.IsDefEq univs Γ (mkApps (.const data.name levels) args) out T :=
  prefix_descend heq (RecoveredFamilyComparison.descends heq hs)
    hW hΓ hΓ' H hlarge hzero hw hlen howner hS hE hg ht HG

/-- Erased family guards supply the existing compatible computation interface
for every registered singleton prefix, with its actual generated reduct. -/
theorem PrefixStep.recovered_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ComputeDescent (PrefixStep (RecoveredFamilyComparison D stage)) :=
  PrefixStep.computeDescent heq (RecoveredFamilyComparison.descends heq hs)

end Lean4Lean.VEnv.Strengthening.GuardedSingleton
