import Lean4Lean.Theory.Typing.AnchoredNativeDepth
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedClosures
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedSort

/-! The declaration-relative motive bounds CURRENT-head nesting in both
returned source observations and source type certificates. Its variable
valuation contains bounded actual certificates. Transitivity spends no fuel:
it interprets the first child's bounded returned observer at the same bound.

The remaining declaration induction needs two distinct source phases. For a
completed prefix, counted names must be fresh for that prefix (or an equivalent
explicit absence-of-current-equations invariant). For the current block's
header environment, all current constants are present but their equations are
absent: its global Strong theorem is proved by native fuel induction. A current
native node spends one unit and interprets its original certificate/plan
children at the smaller fuel in that SAME header environment. Old registered
heads use their original earlier declaration stages without spending current
fuel. Transitivity and conversion recurse only on original Strong children at
unchanged fuel. The stage index is the original declaration position plus this
header phase, not the length of a reconstructed header well-formedness proof.

No full declaration induction is asserted here. In particular, a same-current,
same-fuel theorem after current equations are installed would be false as a
resource claim: reverse unfolding may turn a depth-zero RHS observation into a
depth-one current native observation. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure Fits (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat) (left right : Subst)
    (available : Valuation) : Prop where
  entry : ∀ index need, need ∈ available index → ∀ sourceType,
    Lookup source index sourceType →
      ∃ entry : ValuationEntry env U registry target locals left right available index need sourceType,
        entry.certificate.nativeDepth current ≤ fuel

namespace Fits
variable {current : Name → Bool} {fuel : Nat} {env : VEnv} {U : Nat}
  {registry : CanonicalHead.Registry} {source target : List VExpr}
  {locals : List Nat} {σ τ : Subst} {available : Valuation}

theorem forget (fits : Fits current fuel env U registry source target locals σ τ available) :
    Adapted.Fits env U registry source target locals σ τ available := by
  constructor
  intro index need member sourceType lookup
  obtain ⟨entry, _⟩ := fits.entry index need member sourceType lookup
  exact ⟨entry⟩

theorem left (fits : Fits current fuel env U registry source target locals σ τ available) :
    Fits current fuel env U registry source target locals σ σ available := by
  constructor
  intro index need member sourceType lookup
  obtain ⟨entry, bounded⟩ := fits.entry index need member sourceType lookup
  exact ⟨{ entry with related := entry.related.left_diagonal }, bounded⟩
end Fits

structure PairedFits (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat) (σ τ : Subst)
    (available : Valuation) : Prop where
  forward : Fits current fuel env U registry source target locals σ τ available
  backward : Fits current fuel env U registry source target locals τ σ available

namespace PairedFits
variable {current : Name → Bool} {fuel : Nat} {env : VEnv} {U : Nat}
  {registry : CanonicalHead.Registry} {source target : List VExpr}
  {locals : List Nat} {σ τ : Subst} {available : Valuation}

theorem forget (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    Adapted.PairedFits env U registry source target locals σ τ available :=
  ⟨fits.forward.forget, fits.backward.forget⟩
theorem left (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    PairedFits current fuel env U registry source target locals σ σ available :=
  ⟨fits.forward.left, fits.forward.left⟩
theorem right (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    PairedFits current fuel env U registry source target locals τ τ available :=
  ⟨fits.backward.left, fits.backward.left⟩
theorem symm (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    PairedFits current fuel env U registry source target locals τ σ available :=
  ⟨fits.backward, fits.forward⟩
end PairedFits

structure Result (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst)
    (available : Valuation) (left right sourceType : VExpr) (demand : Profile n)
    extends GradedTransferResult env U registry target locals σ τ available left right sourceType demand where
  observationBound : observation.nativeDepth current ≤ fuel
  certificateBound : certificate.nativeDepth current ≤ fuel

def Transfer (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst)
    (available : Valuation) (left right sourceType : VExpr) : Prop :=
  ∀ {n : Nat} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ left demand footprint),
    observation.nativeDepth current ≤ fuel → footprint.Available available →
      Nonempty (Result current fuel env U registry target locals σ τ available left right sourceType demand)

def SortCorrect (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst)
    (available : Valuation) (expression sourceType : VExpr) : Prop :=
  ∀ level relevant, sourceType = .sort level → Relevant level relevant →
    ∀ {n : Nat} {demand : Profile n} {footprint : Footprint}
      (observation : Obs env U registry target locals σ expression demand footprint),
    observation.nativeDepth current ≤ fuel → footprint.Available available →
      demand.HasType (.sort relevant)

def Joint (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source : List VExpr) (left right sourceType : VExpr) : Prop :=
  ∀ target locals σ τ available, available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    PairedFits current fuel env U registry source target locals σ τ available →
      Transfer current fuel env U registry target locals σ τ available left right sourceType ∧
      Transfer current fuel env U registry target locals σ τ available right left sourceType ∧
      SortCorrect current fuel env U registry target locals σ available left sourceType ∧
      SortCorrect current fuel env U registry target locals σ available right sourceType

variable {current : Name → Bool} {fuel : Nat} {env : VEnv} {U : Nat}
  {registry : CanonicalHead.Registry} {source target : List VExpr}
  {locals : List Nat} {σ τ : Subst} {available : Valuation}
  {left middle right sourceType : VExpr}

private theorem code_union
    (first : TypeRelated env U registry target A B p)
    (second : TypeRelated env U registry target A B q) :
    TypeRelated env U registry target A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

theorem Transfer.trans
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (first : Transfer current fuel env U registry target locals σ σ available left middle sourceType)
    (second : Transfer current fuel env U registry target locals σ τ available middle right sourceType) :
    Transfer current fuel env U registry target locals σ τ available left right sourceType := by
  intro n demand footprint observation bound resources
  obtain ⟨a⟩ := first observation bound resources
  obtain ⟨b⟩ := second a.observation a.observationBound a.resultAvailable
  have firstTyped := Profile.HasType.raise b.bound a.typed
  have firstRelated := Related.raise henv b.bound a.related
  have firstCode := TypeRelated.raise henv b.bound a.typeCode
  have firstAdapter := NormalProfileAdapter.raise henv hscoped hTarget b.bound a.adapter
  simp only [raiseProfile_trans] at firstTyped firstRelated firstAdapter
  have wf := firstTyped.wf_type.union b.typed.wf_type
  have typed := firstTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := b.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have code := code_union firstCode b.typeCode
  have cross := NormalProfileAdapter.termMap firstAdapter henv hscoped hTarget typed code b.related
  exact ⟨{
    rank := b.rank
    bound := Nat.le_trans a.bound b.bound
    rawDemand := b.rawDemand
    resultFootprint := b.resultFootprint
    observation := b.observation
    adapter := NormalProfileAdapter.comp b.adapter firstAdapter
    resultAvailable := b.resultAvailable
    support := (raiseProfile b.rank b.bound a.support).union b.support
    typeFootprint := a.typeFootprint ++ b.typeFootprint
    certificate := .union (a.certificate.raise b.bound) b.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.typeAvailable i need) (b.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.trans henv hscoped firstRelated cross
    rawRelated := Related.retag henv rawTyped code b.rawRelated
    observationBound := b.observationBound
    certificateBound := by
      simpa only [CodeCert.nativeDepth, CodeCert.nativeDepth_raise] using
        (Nat.max_le.mpr ⟨a.certificateBound, b.certificateBound⟩) }⟩

theorem Joint.trans
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (first : Joint current fuel env U registry source left middle sourceType)
    (second : Joint current fuel env U registry source middle right sourceType) :
    Joint current fuel env U registry source left right sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  have a := first target locals σ τ available closed hTarget substitutions fits
  have b := second target locals σ τ available closed hTarget substitutions fits
  have ad := first target locals σ σ available closed hTarget substitutions.left fits.left
  have bd := second target locals σ σ available closed hTarget substitutions.left fits.left
  exact ⟨Transfer.trans henv hscoped hTarget ad.1 b.1,
    Transfer.trans henv hscoped hTarget bd.2.1 a.2.1, a.2.2.1, b.2.2.2⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
