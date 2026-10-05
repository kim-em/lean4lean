import Lean4Lean.Theory.Typing.AnchoredNativeSeededSpine

/-! The computational demand is threaded through the same retained original
application/conversion spine as its source type certificate. Application
frames retain both actual argument seeds and inverse-substitution type cuts. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

namespace SeededApplicationCodeInput
variable {result : Profile n} (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)

def output (atom : Atom n) : Atom frame.collected.rank :=
  raiseAtom frame.collected.rank (Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound) atom

def demand (atom : Atom n) : Atom (frame.collected.rank + 1) :=
  AtomData.fn frame.key (frame.output atom)

theorem demandTyped {atom : Atom n} (typed : (Profile.singleton atom).HasType result) :
    (Profile.singleton (frame.demand atom)).HasType frame.profile := by
  apply Profile.HasType.fn frame.certificate.formed.wf_value (List.mem_singleton_self _)
  simpa only [output, raiseProfile_singleton] using
    Profile.HasType.raise (Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound) typed

end SeededApplicationCodeInput

/-- A finite constructor-for-constructor path. In particular, conversion
keeps the requested atom literally; it does not synthesize a new demand. -/
inductive NativeSpineDemandPath (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    (expression assigned : VExpr) → {n : Nat} → Atom n → {N : Nat} → Atom N → Type where
  | constant {atom : Atom n} :
      NativeSpineDemandPath sourceEnv env U registry source target locals σ available name levels
        (.const name levels) assigned atom atom
  | application {atom : Atom n} {root : Atom N}
      (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)
      (function : NativeSpineDemandPath sourceEnv env U registry source target locals σ available name levels
        f (.forallE A B) (frame.demand atom) root) :
      NativeSpineDemandPath sourceEnv env U registry source target locals σ available name levels
        (.app f a) (B.inst a) atom root
  | conversion {atom : Atom n} {root : Atom N}
      {original : sourceEnv.IsDefEqStrong U source A B (.sort level)}
      (edge : OriginalPayload sourceEnv env U registry original)
      (term : NativeSpineDemandPath sourceEnv env U registry source target locals σ available name levels
        expression A atom root) :
      NativeSpineDemandPath sourceEnv env U registry source target locals σ available name levels
        expression B atom root

/-- The root certificate and root computational atom have the same grade and
are connected to the selected terminal atom by the actual original spine. -/
structure NativeSpineRootDemand (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel)
    (expression assigned : VExpr) (atom : Atom n) where
  info : VConstant
  lookup : sourceEnv.constants name = some info
  formation : SourcePiFormation (OriginalTypePayload sourceEnv env U registry)
    source (info.type.instL levels)
  rank : Nat
  demand : Atom rank
  support : Profile rank
  footprint : Footprint
  certificate : CodeCert env U registry target locals σ (info.type.instL levels) support footprint
  resources : footprint.Available available
  typed : (Profile.singleton demand).HasType support
  path : NativeSpineDemandPath sourceEnv env U registry source target locals σ available name levels
    expression assigned atom demand

/-- Construct the actual function-demand tower, rather than guessing one
from a type profile after forgetting the application frames. -/
noncomputable def NativeSeededSpineCertificate.rootDemand
    {profile : Profile n}
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint)
    {atom : Atom n} (typed : (Profile.singleton atom).HasType profile) :
    NativeSpineRootDemand sourceEnv env U registry source target locals σ available
      name levels expression assigned atom := by
  induction spine with
  | constant lookup formation certificate resources =>
    exact ⟨_, lookup, formation, _, atom, _, _, certificate, resources, typed, .constant⟩
  | application frame function ih =>
    let root := ih (frame.demandTyped typed)
    exact ⟨root.info, root.lookup, root.formation, root.rank, root.demand, root.support,
      root.footprint, root.certificate, root.resources, root.typed, .application frame root.path⟩
  | conversion edge certificate transfer term ih =>
    let root := ih typed
    exact ⟨root.info, root.lookup, root.formation, root.rank, root.demand, root.support,
      root.footprint, root.certificate, root.resources, root.typed, .conversion edge root.path⟩

end Lean4Lean.AnchoredSource.Adapted
