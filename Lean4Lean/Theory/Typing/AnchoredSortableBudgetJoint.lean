import Lean4Lean.Theory.Typing.AnchoredSortableBudgetComposition

/-! Original paired rule hypotheses and typed binder extension keep their
caller controls while reusing exact stored context formations. -/
namespace Lean4Lean.AnchoredSource.Adapted.HereditaryBudgeted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

def TailJointAt (budgets : Budgets) (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    (context : ContextDerivation sourceEnv U source) (left right type : VExpr) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    ∀ frame : SortableTailPairedFits env registry target context locals σ τ available,
      Within budgets frame.nativeDepth →
      Transfer budgets env U registry target locals σ τ available left right type ∧
      Transfer budgets env U registry target locals σ τ available right left type

theorem TailJointAt.symm (original : TailJointAt budgets env registry context left right type) :
    TailJointAt budgets env registry context right left type := by
  intro target locals σ τ available closed hTarget substitutions fits bounded
  exact (original target locals σ τ available closed hTarget substitutions fits bounded).symm

theorem TailJointAt.left
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} {left right type : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : TailJointAt budgets env registry context left right type) :
    TailJointAt budgets env registry context left left type := by
  intro target locals σ τ available closed hTarget substitutions fits bounded
  have diagonal := original target locals σ σ available closed hTarget substitutions.left fits.left (frame_left bounded)
  have paired := original target locals σ τ available closed hTarget substitutions fits bounded
  have forward : Transfer budgets env U registry target locals σ τ available left left type :=
    Transfer.trans henv hscoped hTarget diagonal.1 paired.2
  exact ⟨forward, forward⟩

theorem TailJointAt.right
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} {left right type : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : TailJointAt budgets env registry context left right type) :
    TailJointAt budgets env registry context right right type := original.symm.left henv hscoped

def TailJoint (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    (context : ContextDerivation sourceEnv U source) (left right type : VExpr) : Prop :=
  ∀ (budgets : Budgets) (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    ∀ frame : SortableTailPairedFits env registry target context locals σ τ available,
      Within budgets frame.nativeDepth →
      Transfer budgets env U registry target locals σ τ available left right type ∧
      Transfer budgets env U registry target locals σ τ available right left type

theorem TailJoint.symm (original : TailJoint env registry context left right type) :
    TailJoint env registry context right left type := by
  intro budgets target locals σ τ available closed hTarget substitutions fits bounded
  exact (original budgets target locals σ τ available closed hTarget substitutions fits bounded).symm

theorem TailJoint.left
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} {left right type : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : TailJoint env registry context left right type) :
    TailJoint env registry context left left type := by
  intro budgets target locals σ τ available closed hTarget substitutions fits bounded
  have diagonal := original budgets target locals σ σ available closed hTarget substitutions.left fits.left (frame_left bounded)
  have paired := original budgets target locals σ τ available closed hTarget substitutions fits bounded
  have forward : Transfer budgets env U registry target locals σ τ available left left type :=
    Transfer.trans henv hscoped hTarget diagonal.1 paired.2
  exact ⟨forward, forward⟩

theorem TailJoint.right
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} {left right type : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : TailJoint env registry context left right type) :
    TailJoint env registry context right right type := original.symm.left henv hscoped

theorem pushOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {context : ContextDerivation sourceEnv U source}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (originalDomain : EndpointRef sourceEnv U source A (.sort level))
    (closed : available.AtomClosed)
    (domainChild : Transfer budgets env U registry target locals σ τ available A A (.sort level))
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (frameBound : Within budgets fits.nativeDepth)
    (domain : SortableCert env U registry target locals σ A true support domainFootprint)
    (domainBound : Within budgets domain.nativeDepth)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    ∃ result : SortableTailPairedFits env registry target (.cons context originalDomain) (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available),
      Within budgets result.nativeDepth := by
  obtain ⟨rightDomain⟩ := domainChild.sortable henv hscoped hTarget closed domain domainBound domainAvailable
  refine ⟨fits.pushCertificates originalDomain domain rightDomain.certificate
    domainAvailable rightDomain.available typed typed arguments
    (Related.convert henv typed rightDomain.related (arguments.symm henv))
    localNeeds bounded covered, ?_⟩
  intro current fuel member
  simp only [SortableTailPairedFits.nativeDepth, SortableTailPairedFits.pushCertificates,
    SortableTailFits.nativeDepth]
  have original := Nat.max_le.mp (frameBound current fuel member)
  exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨domainBound current fuel member, original.1⟩,
    Nat.max_le.mpr ⟨rightDomain.valueBound current fuel member, original.2⟩⟩

end Lean4Lean.AnchoredSource.Adapted.HereditaryBudgeted
