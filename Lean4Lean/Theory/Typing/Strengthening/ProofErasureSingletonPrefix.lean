import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetraction
import Lean4Lean.Theory.Typing.Strengthening.GuardedSingletonPrefixDescent

/-! # Registered singleton prefixes guarded by recursive erased comparison

The generated family propositions may contain arbitrary data indices and
transported fields. A recursive erased comparison above inserted binders lowers
the guard, rebuilds the actual generated check, and replays the prefix below.
Coverage of arbitrary declarative family conversions remains open.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim Params
variable [Params] {S : SingletonLayout} {E : PropElim}

/-- The concrete recursive certificate used for a generated family guard. -/
def ErasedFamilyComparison (D : PureObservation.Definitions) (stage : Nat)
    (Γ : List VExpr) (a b : VExpr) : Prop :=
  ProofShape.Compare (ErasedComparedKStage D stage) true (proofErase Γ a) (proofErase Γ b)

/-- Raw retraction of recursive erased comparisons discharges the general
endpoint-descent interface, including arbitrary context thinnings. -/
theorem ErasedFamilyComparison.descends (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) : EndpointDescent (ErasedFamilyComparison D stage) := by
  intro ρ Γ Γ' a b A W hΓ hΓ' ha hb H
  obtain ⟨_, hA⟩ := ha.isType henv hΓ
  exact (proofErase_compared_K_thinning heq hs hΓ hΓ' W ha hb H).1 ⟨_, hA⟩

/-- Replay the actual generated prefix below an arbitrary context thinning
using its upper erased family certificate. No upper declarative replay check or
lower result typing is assumed. Data fields and data indices are allowed. -/
theorem erased_prefix_descend (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs) (hlen : levels.length = data.uvars)
    {index : Fin data.schema.signature.constructors.size}
    (howner : data.schema.signature.constructors[index].owner = data.owner)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels (args.map (·.lift' ρ)) = some program)
    (ht : env.HasType univs Γ (mkApps (.const data.name levels) args) T)
    (HG : FamilyGuard (ErasedFamilyComparison D stage) Γ' data levels (args.map (·.lift' ρ)) program S E) :
    ∃ out, program.rhs = out.lift' ρ ∧
      env.IsDefEq univs Γ (mkApps (.const data.name levels) args) out T :=
  prefix_descend heq (ErasedFamilyComparison.descends heq hs)
    hW hΓ hΓ' H hlarge hzero hw hlen howner hS hE hg ht HG

/-- Erased family guards supply the existing compatible computation interface
for every registered singleton prefix, with its actual generated reduct. -/
theorem PrefixStep.erased_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ComputeDescent (PrefixStep (ErasedFamilyComparison D stage)) :=
  PrefixStep.computeDescent heq (ErasedFamilyComparison.descends heq hs)

end Lean4Lean.VEnv.Strengthening.GuardedSingleton
