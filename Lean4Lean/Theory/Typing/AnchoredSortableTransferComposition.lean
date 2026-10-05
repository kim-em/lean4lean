import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFundamental
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFuture
import Lean4Lean.Theory.Typing.AnchoredSortAdequacy

/-! Composition and source binder frames for the hereditary fundamental
motive. Sort correctness follows from the actual assigned-type capability;
it is not an extra induction assumption. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

namespace SortableComputationalTransferResult
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
  {left right sourceType : VExpr} {demand : Profile n}

noncomputable def requestedCertificate
    (result : SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType demand) :
    SortableCert env U registry target locals σ sourceType true
      (lowerProfile n result.bound result.support) result.typeFootprint :=
  result.typeCertificate.lower n result.bound

theorem requestedTyped
    (result : SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType demand) :
    demand.HasType (lowerProfile n result.bound result.support) :=
  lowerProfile.hasType result.bound result.typed

theorem requestedRelated (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (result : SortableComputationalTransferResult env U registry target locals σ τ
      available left right sourceType demand) :
    Related env U registry target (left.subst σ) (right.subst τ) (sourceType.subst σ)
      demand (lowerProfile n result.bound result.support) :=
  lowerProfile.related result.bound henv hTarget result.related
end SortableComputationalTransferResult

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

theorem SortableComputationalTransfer.trans
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left middle right sourceType : VExpr}
    (first : SortableComputationalTransfer env U registry target locals σ σ
      available left middle sourceType)
    (second : SortableComputationalTransfer env U registry target locals σ τ
      available middle right sourceType) :
    SortableComputationalTransfer env U registry target locals σ τ
      available left right sourceType := by
  intro n demand footprint observation resources
  obtain ⟨a⟩ := first observation resources
  obtain ⟨b⟩ := second a.observation a.resources
  have firstTyped := Profile.HasType.raise b.bound a.typed
  have firstRelated := Related.raise henv b.bound a.related
  have firstCode := TypeRelated.raise henv b.bound a.typeCode
  have firstAdapter := GeneralNormalProfileAdapter.raise henv hscoped hTarget b.bound a.adapter
  simp only [raiseProfile_trans] at firstTyped firstRelated firstAdapter
  have wf := firstTyped.wf_type.union b.typed.wf_type
  have typed := firstTyped.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := b.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have code := code_union firstCode b.typeCode
  have cross := GeneralNormalProfileAdapter.termMap firstAdapter henv hscoped hTarget typed code b.related
  exact ⟨{
    rank := b.rank
    bound := Nat.le_trans a.bound b.bound
    raw := b.raw
    footprint := b.footprint
    observation := b.observation
    adapter := GeneralNormalProfileAdapter.comp b.adapter firstAdapter
    resources := b.resources
    support := (raiseProfile b.rank b.bound a.support).union b.support
    typeFootprint := a.typeFootprint ++ b.typeFootprint
    typeCertificate := .union (a.typeCertificate.raise b.bound) b.typeCertificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.typeAvailable i need) (b.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.trans henv hscoped firstRelated cross
    rawRelated := Related.retag henv rawTyped code b.rawRelated
    live := b.live }⟩


theorem SortableTransfer.sortCorrect
    (hTarget : OnCtx target (env.IsType U))
    (original : SortableTransfer env U registry target locals σ τ available left right (.sort level))
    (certificate : SortableCert env U registry target locals σ left requestedFlag profile footprint)
    (resources : footprint.Available available)
    (flag : Relevant level relevant) : profile.HasType (.sort relevant) := by
  obtain ⟨answer⟩ := original certificate resources
  exact TypeRelated.sort_typed hTarget flag answer.typeCode answer.typed

namespace OriginalTail

def HereditaryTailJoint (env : VEnv) (registry : CanonicalHead.Registry)
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    (context : ContextDerivation sourceEnv U source) (left right type : VExpr) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    SortableTailPairedFits env registry target context locals σ τ available →
    SortableComputationalTransfer env U registry target locals σ τ available left right type ∧
      SortableComputationalTransfer env U registry target locals σ τ available right left type

theorem HereditaryTailJoint.symm
    (original : HereditaryTailJoint env registry context left right type) :
    HereditaryTailJoint env registry context right left type := by
  intro target locals σ τ available closed hTarget substitutions fits
  exact (original target locals σ τ available closed hTarget substitutions fits).symm

theorem HereditaryTailJoint.left
    {sourceEnv env : VEnv} {U : Nat} {source : List VExpr}
    {context : ContextDerivation sourceEnv U source} {left right type : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (original : HereditaryTailJoint env registry context left right type) :
    HereditaryTailJoint env registry context left left type := by
  intro target locals σ τ available closed hTarget substitutions fits
  have diagonal := original target locals σ σ available closed hTarget substitutions.left fits.left
  have paired := original target locals σ τ available closed hTarget substitutions fits
  have forward : SortableComputationalTransfer env U registry target locals σ τ available left left type :=
    SortableComputationalTransfer.trans henv hscoped hTarget diagonal.1 paired.2
  exact ⟨forward, forward⟩

theorem SortableTailPairedFits.pushHereditaryOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr}
    {context : ContextDerivation sourceEnv U source}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {A x y : VExpr} {input support : Profile N} {domainFootprint : Footprint}
    (originalDomain : EndpointRef sourceEnv U source A (.sort level))
    (domainChild : SortableTransfer env U registry target locals σ τ available A A (.sort level))
    (fits : SortableTailPairedFits env registry target context locals σ τ available)
    (domain : SortableCert env U registry target locals σ A true support domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (localNeeds : List Need)
    (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
    (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ input.atoms) :
    Nonempty (SortableTailPairedFits env registry target (.cons context originalDomain) (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push localNeeds available)) := by
  obtain ⟨rightDomain⟩ := domainChild domain domainAvailable
  exact ⟨fits.pushCertificates originalDomain domain rightDomain.certificate
    domainAvailable rightDomain.available typed typed arguments
    (Related.convert henv typed rightDomain.related (arguments.symm henv))
    localNeeds bounded covered⟩

end OriginalTail
end Lean4Lean.AnchoredSource.Adapted
