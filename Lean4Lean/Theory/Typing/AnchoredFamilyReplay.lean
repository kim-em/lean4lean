import Lean4Lean.Theory.Typing.AnchoredFamilySourceObservation

/-! A family descriptor is fixed before grading its application replay.
Retained argument observations and guards are raised to the finite maximum
needed by each remaining binder; the descriptor's original keys are never
recomputed. The resulting source replay uses ordinary `Obs.app`, preserving
the whole-variable cut mechanism of inverse substitution. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

namespace SeededApplicationCodeInput
variable {result : Profile n}
  (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)

def familyReplayRank (outputRank : Nat) : Nat := max frame.collected.rank outputRank

def familyReplayKey (outputRank : Nat) : Key (frame.familyReplayRank outputRank) :=
  raiseKey _ (Nat.le_max_left _ _) frame.key

def familyReplayOutput (atom : Atom m) : Atom (frame.familyReplayRank m) :=
  raiseAtom _ (Nat.le_max_right _ _) atom

def familyReplayDemand (atom : Atom m) : Atom (frame.familyReplayRank m + 1) :=
  .fn (frame.familyReplayKey m) (frame.familyReplayOutput atom)

/-- Domain certificates and guards retain their original source leaves.
Only finite profile padding changes. -/
noncomputable def familyReplayDomain (outputRank : Nat) :
    CodeCert env U registry target locals σ A
      (raiseProfile (frame.familyReplayRank outputRank) (Nat.le_max_left _ _) frame.support)
      frame.domainFootprint :=
  frame.domain.raise (Nat.le_max_left _ _)

theorem familyReplayGuard (henv : env.Ordered) (outputRank : Nat) :
    LambdaGuard env U registry target σ A (frame.familyReplayKey outputRank)
      (raiseProfile (frame.familyReplayRank outputRank) (Nat.le_max_left _ _) frame.support) :=
  frame.guard.raise henv (Nat.le_max_left _ _)

/-- A raised binder admission supplies the original frozen family key.
Its support may be arbitrary; no new source request is made. -/
theorem familyReplayAdmission (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {x y : VExpr} (admitted : Admitted env U registry target (frame.familyReplayKey m) x y) :
    Admitted env U registry target frame.key x y :=
  Admitted.lowerFamily henv (Nat.le_max_left _ _) hTarget admitted

end SeededApplicationCodeInput

/-- The requested terminal atom can have any finite rank. In particular,
its frozen family keys may have been chosen by an earlier lower-grade pass. -/
inductive FamilyReplayPath (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    (expression assigned : VExpr) → {m : Nat} → Atom m → {M : Nat} → Atom M → Type where
  | constant {atom : Atom m} :
      FamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        (.const name levels) assigned atom atom
  | application {atom : Atom m} {root : Atom M}
      (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)
      (function : FamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        f (.forallE A B) (frame.familyReplayDemand atom) root) :
      FamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        (.app f a) (B.inst a) atom root
  | conversion {atom : Atom m} {root : Atom M}
      {original : sourceEnv.IsDefEqStrong U source A B (.sort level)}
      (edge : OriginalPayload sourceEnv env U registry original)
      (term : FamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        expression A atom root) :
      FamilyReplayPath sourceEnv env U registry source target locals σ available name levels
        expression B atom root

/-- This bound is computed by one finite pass over retained applications.
No pass rebuilds the original frozen key sequence. -/
def NativeSeededSpineCertificate.familyReplayRank
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) (outputRank : Nat) : Nat :=
  match spine with
  | .constant .. => outputRank
  | .application frame function => function.familyReplayRank (frame.familyReplayRank outputRank + 1)
  | .conversion _ _ _ term => term.familyReplayRank outputRank

structure FamilyReplayRoot
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) (atom : Atom m) where
  demand : Atom (spine.familyReplayRank m)
  path : FamilyReplayPath sourceEnv env U registry source target locals σ available name levels
    expression assigned atom demand

noncomputable def NativeSeededSpineCertificate.familyReplay
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) (atom : Atom m) : FamilyReplayRoot spine atom := by
  induction spine generalizing m with
  | constant lookup formation certificate resources => exact ⟨atom, .constant⟩
  | application frame function ih =>
    let previous := ih (frame.familyReplayDemand atom)
    exact ⟨previous.demand, .application frame previous.path⟩
  | conversion edge certificate transfer term ih =>
    let previous := ih atom
    exact ⟨previous.demand, .conversion edge previous.path⟩

/-- Once the finite bare-family plan is installed, this checked replay
constructs the saturated source observer through the existing application
grammar. Source footprints stay exactly the retained original leaves. -/
theorem FamilyReplayPath.observe
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {name : Name} {levels : List VLevel} {expression assigned : VExpr}
    {atom : Atom m} {root : Atom M}
    (path : FamilyReplayPath sourceEnv env U registry source target locals σ available
      name levels expression assigned atom root)
    {headFootprint : Footprint}
    (head : Obs env U registry target locals σ (.const name levels) (.singleton root) headFootprint)
    (headResources : headFootprint.Available available) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ expression (.singleton atom) footprint) ∧
      footprint.Available available := by
  induction path with
  | constant => exact ⟨headFootprint, ⟨head⟩, headResources⟩
  | @application m atom M root A B a n result before f frame function ih =>
    obtain ⟨footprint, ⟨fn⟩, resources⟩ := ih head
    have argument := frame.argumentObservation.raise (Nat.le_max_left frame.collected.rank m)
    have anchor := (frame.familyReplayGuard henv m).anchor
    have application := Obs.app fn argument (.refl _) anchor
    refine ⟨footprint ++ (frame.seed.footprint ++ frame.collected.argumentFootprint), ⟨?_⟩,
      fun i need member => (List.mem_append.mp member).elim
        (resources i need) (frame.argumentResources i need)⟩
    apply Obs.lower (Nat.le_max_right frame.collected.rank m)
    simpa only [raiseProfile_singleton, SeededApplicationCodeInput.familyReplayOutput,
      SeededApplicationCodeInput.familyReplayRank] using application
  | conversion _ _ ih => exact ih head

end Lean4Lean.AnchoredSource.Adapted
