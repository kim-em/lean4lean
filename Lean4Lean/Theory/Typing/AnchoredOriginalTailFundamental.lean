import Lean4Lean.Theory.Typing.AnchoredOriginalQueryCompatibility
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedFundamental
import Lean4Lean.Theory.Typing.AnchoredOriginalTailFuture
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode

/-! Internal fundamental-theorem frames retaining both actual source tails.
These contracts are obligations of the original-derivation induction, not
additional assumptions on declarations or the final checker theorem. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalTail
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

structure TailPairedFits (env : VEnv) (registry : CanonicalHead.Registry)
    (target : List VExpr) {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    (context : ContextDerivation sourceEnv U source)
    (locals : List Nat) (left right : Subst) (available : Valuation) where
  forward : TailFits sourceEnv env U registry target source locals left right available
  backward : TailFits sourceEnv env U registry target source locals right left available
  forwardContext : forward.contextDerivation = context
  backwardContext : backward.contextDerivation = context

variable {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}

noncomputable def TailFits.left
    (tail : TailFits sourceEnv env U registry target source locals σ τ available) :
    TailFits sourceEnv env U registry target source locals σ σ available := by
  induction tail with
  | nil => exact .nil
  | push rest original domain resources typed arguments needs bounded covered ih =>
    exact .push ih original domain resources typed arguments.left_diagonal needs bounded covered

@[simp] theorem TailFits.contextDerivation_left
    (tail : TailFits sourceEnv env U registry target source locals σ τ available) :
    tail.left.contextDerivation = tail.contextDerivation := by
  induction tail with
  | nil => rfl
  | push rest original domain resources typed arguments needs bounded covered ih =>
    exact congrArg (fun context => ContextDerivation.cons context original) ih

variable {context : ContextDerivation sourceEnv U source}

def TailPairedFits.diagonal
    (context : ContextDerivation sourceEnv U source)
    (tail : TailFits sourceEnv env U registry target source locals σ σ available) :
    TailPairedFits env registry target context locals σ σ available :=
  ⟨tail.reorigin context, tail.reorigin context,
    tail.reorigin_contextDerivation context, tail.reorigin_contextDerivation context⟩

theorem TailPairedFits.toPairedFits
    (frame : TailPairedFits env registry target context locals σ τ available)
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U)) :
    PairedFits env U registry source target locals σ τ available :=
  ⟨frame.forward.toFits henv hTarget, frame.backward.toFits henv hTarget⟩

def TailPairedFits.symm
    (frame : TailPairedFits env registry target context locals σ τ available) :
    TailPairedFits env registry target context locals τ σ available :=
  ⟨frame.backward, frame.forward, frame.backwardContext, frame.forwardContext⟩

noncomputable def TailPairedFits.left
    (frame : TailPairedFits env registry target context locals σ τ available) :
    TailPairedFits env registry target context locals σ σ available :=
  ⟨frame.forward.left, frame.forward.left,
    frame.forward.contextDerivation_left.trans frame.forwardContext,
    frame.forward.contextDerivation_left.trans frame.forwardContext⟩

noncomputable def TailPairedFits.right
    (frame : TailPairedFits env registry target context locals σ τ available) :
    TailPairedFits env registry target context locals τ τ available := frame.symm.left

/-- The new head is charged to the actual original domain formation on both
sides; source certificates remain in the earlier tail where they were built. -/
def TailPairedFits.pushCertificates
    {n : Nat} {input leftSupport rightSupport : Profile n}
    (frame : TailPairedFits env registry target context locals σ τ available)
    (originalDomain : EndpointRef sourceEnv U source A (.sort level))
    (leftDomain : CodeCert env U registry target locals σ A leftSupport leftFootprint)
    (rightDomain : CodeCert env U registry target locals τ A rightSupport rightFootprint)
    (leftResources : leftFootprint.Available available)
    (rightResources : rightFootprint.Available available)
    (leftTyped : (input : Profile n).HasType leftSupport)
    (rightTyped : input.HasType rightSupport)
    (forward : Related env U registry target x y (A.subst σ) input leftSupport)
    (backward : Related env U registry target y x (A.subst τ) input rightSupport)
    (needs : List Need)
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    TailPairedFits env registry target (.cons context originalDomain) (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push needs available) :=
  { forward := frame.forward.push originalDomain leftDomain leftResources leftTyped
      forward needs bounded covered
    backward := frame.backward.push originalDomain rightDomain rightResources rightTyped
      backward needs bounded covered
    forwardContext := congrArg (fun tail => ContextDerivation.cons tail originalDomain) frame.forwardContext
    backwardContext := congrArg (fun tail => ContextDerivation.cons tail originalDomain) frame.backwardContext }

def TailJoint (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    (context : ContextDerivation sourceEnv U source) (left right type : VExpr) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    TailPairedFits env registry target context locals σ τ available →
    GradedTransfer env U registry target locals σ τ available left right type ∧
      GradedTransfer env U registry target locals σ τ available right left type ∧
      SortCorrect env U registry target locals σ available left type ∧
      SortCorrect env U registry target locals σ available right type

theorem TailJoint.symm
    (original : TailJoint env registry context left right type) :
    TailJoint env registry context right left type := by
  intro target locals σ τ available closed hTarget substitutions fits
  have answer := original target locals σ τ available closed hTarget substitutions fits
  exact ⟨answer.2.1, answer.1, answer.2.2.2, answer.2.2.1⟩

theorem TailJoint.left
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} {left right type : VExpr} (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : TailJoint env registry context left right type) :
    TailJoint env registry context left left type := by
  intro target locals σ τ available closed hTarget substitutions fits
  have diagonal := original target locals σ σ available closed hTarget substitutions.left fits.left
  have paired := original target locals σ τ available closed hTarget substitutions fits
  have forward : GradedTransfer env U registry target locals σ τ available left left type :=
    GradedTransfer.trans henv hscoped hTarget diagonal.1 paired.2.1
  exact ⟨forward, forward, diagonal.2.2.1, diagonal.2.2.1⟩

noncomputable def TailPairedFits.future
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} (henv : env.Ordered)
    (insertion : FutureInsertion env U target futureTarget ρ)
    (frame : TailPairedFits env registry target context locals σ τ available) :
    TailPairedFits env registry futureTarget context locals
      (σ.lift_r ρ) (τ.lift_r ρ) (Valuation.rename ρ available) :=
  ⟨frame.forward.future henv insertion, frame.backward.future henv insertion,
    (frame.forward.contextDerivation_future henv insertion).trans frame.forwardContext,
    (frame.backward.contextDerivation_future henv insertion).trans frame.backwardContext⟩

theorem TailPairedFits.pushGradedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {context : ContextDerivation sourceEnv U source}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (originalDomain : EndpointRef sourceEnv U source A (.sort level))
    (closed : available.AtomClosed)
    (domainChild : GradedTransfer env U registry target locals σ τ available A A (.sort level))
    (fits : TailPairedFits env registry target context locals σ τ available)
    (domain : CodeCert env U registry target locals σ A support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    Nonempty (TailPairedFits env registry target (.cons context originalDomain) (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available)) := by
  obtain ⟨rightDomain⟩ := domain.transfer_graded henv hscoped hTarget closed domainChild domainAvailable
  exact ⟨fits.pushCertificates originalDomain domain rightDomain.certificate
    domainAvailable rightDomain.available typed typed arguments
    (Related.convert henv typed rightDomain.related (arguments.symm henv))
    localNeeds bounded covered⟩

theorem TailJoint.right
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} {left right type : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : TailJoint env registry context left right type) :
    TailJoint env registry context right right type := original.symm.left henv hscoped

/-- A fixed original endpoint, interpreted only in frames retaining its
original captured context. Varying queries and target worlds does not change
the source closure used by the induction measure. -/
def StateFundamental (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {expression type : VExpr}
    (context : ContextDerivation sourceEnv U source)
    (_original : EndpointState sourceEnv U source expression type) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    TailPairedFits env registry target context locals σ τ available →
    GradedTransfer env U registry target locals σ τ available expression expression type ∧
      SortCorrect env U registry target locals σ available expression type

abbrev EndpointFundamental (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {expression type : VExpr}
    (context : ContextDerivation sourceEnv U source)
    (original : EndpointRef sourceEnv U source expression type) : Prop :=
  StateFundamental env registry context (.ref original)

/-- The equality part of the original induction. Both transfer directions
are needed before selecting the semantics of either original endpoint. -/
def DerivationFundamental (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr} {left right type : VExpr}
    (context : ContextDerivation sourceEnv U source)
    (_original : Derivation sourceEnv U source left right type) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    TailPairedFits env registry target context locals σ τ available →
    GradedTransfer env U registry target locals σ τ available left right type ∧
      GradedTransfer env U registry target locals σ τ available right left type ∧
      SortCorrect env U registry target locals σ available left type ∧
      SortCorrect env U registry target locals σ available right type

theorem DerivationFundamental.left
    {left right type : VExpr}
    {original : Derivation sourceEnv U source left right type}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (fundamental : DerivationFundamental env registry context original) :
    EndpointFundamental env registry context (.left original) := by
  intro target locals σ τ available closed hTarget substitutions frame
  have diagonal := fundamental target locals σ σ available closed hTarget substitutions.left frame.left
  have paired := fundamental target locals σ τ available closed hTarget substitutions frame
  exact ⟨GradedTransfer.trans henv hscoped hTarget diagonal.1 paired.2.1, diagonal.2.2.1⟩

theorem DerivationFundamental.right
    {left right type : VExpr}
    {original : Derivation sourceEnv U source left right type}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (fundamental : DerivationFundamental env registry context original) :
    EndpointFundamental env registry context (.right original) := by
  intro target locals σ τ available closed hTarget substitutions frame
  have diagonal := fundamental target locals σ σ available closed hTarget substitutions.left frame.left
  have paired := fundamental target locals σ τ available closed hTarget substitutions frame
  exact ⟨GradedTransfer.trans henv hscoped hTarget diagonal.2.1 paired.1, diagonal.2.2.2⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalTail
