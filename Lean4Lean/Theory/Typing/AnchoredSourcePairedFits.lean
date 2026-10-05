import Lean4Lean.Theory.Typing.AnchoredSourceFuture

/-! A paired valuation retains actual source type certificates at both
realizations. The empty context needs no evidence; binder extension is built
from the original domain child in AnchoredSourcePairedBinder. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure PairedFits (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat) (σ τ : Subst)
    (available : Valuation) : Prop where
  forward : Fits env U registry source target locals σ τ available
  backward : Fits env U registry source target locals τ σ available

namespace PairedFits
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
  {available : Valuation}

theorem symm (fits : PairedFits env U registry source target locals σ τ available) :
    PairedFits env U registry source target locals τ σ available :=
  ⟨fits.backward, fits.forward⟩

theorem left (fits : PairedFits env U registry source target locals σ τ available) :
    PairedFits env U registry source target locals σ σ available :=
  ⟨fits.forward.left, fits.forward.left⟩

theorem right (fits : PairedFits env U registry source target locals σ τ available) :
    PairedFits env U registry source target locals τ τ available :=
  ⟨fits.backward.left, fits.backward.left⟩

theorem diagonal (fits : Fits env U registry source target locals σ σ available) :
    PairedFits env U registry source target locals σ σ available := ⟨fits, fits⟩

theorem nil : PairedFits env U registry [] target locals σ τ available := by
  constructor <;> constructor <;> intro index need member sourceType lookup <;> cases lookup

theorem future (henv : env.Ordered) {future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    (fits : PairedFits env U registry source target locals σ τ available) :
    PairedFits env U registry source future locals (σ.lift_r ρ) (τ.lift_r ρ)
      (Valuation.rename ρ available) :=
  ⟨fits.forward.future henv insertion, fits.backward.future henv insertion⟩

/-- Both entries are finite source certificates. The higher-level binder
producer constructs the second certificate through the original domain child. -/
theorem pushCertificates (henv : env.Ordered)
    (hTarget : OnCtx target (env.IsType U))
    {A x y : VExpr} {input leftSupport rightSupport : Profile N}
    {leftFootprint rightFootprint : Footprint}
    (fits : PairedFits env U registry source target locals σ τ available)
    (leftDomain : CodeCert env U registry target locals σ A leftSupport leftFootprint)
    (rightDomain : CodeCert env U registry target locals τ A rightSupport rightFootprint)
    (leftAvailable : leftFootprint.Available available)
    (rightAvailable : rightFootprint.Available available)
    (leftTyped : input.HasType leftSupport) (rightTyped : input.HasType rightSupport)
    (forward : Related env U registry target x y (A.subst σ) input leftSupport)
    (backward : Related env U registry target y x (A.subst τ) input rightSupport)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available) :=
  ⟨fits.forward.push henv hTarget leftDomain leftAvailable leftTyped forward
      localNeeds bounded covered,
    fits.backward.push henv hTarget rightDomain rightAvailable rightTyped backward
      localNeeds bounded covered⟩

end PairedFits
end Lean4Lean.AnchoredSource
