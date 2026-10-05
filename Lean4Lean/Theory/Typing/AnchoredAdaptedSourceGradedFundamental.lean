import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceBinder
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGrades
import Lean4Lean.Theory.Typing.AnchoredGradedAdapters

/-! Computational transfer may retain a larger finite grade than requested.
This is necessary when unpadding follows an input-changing function adapter.
One actual source type certificate covers both raw and raised requested
demands; projection back to the requested grade is a checked operation. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure GradedTransferResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right sourceType : VExpr) (demand : Profile n) where
  rank : Nat
  bound : n ≤ rank
  rawDemand : Profile rank
  resultFootprint : Footprint
  observation : Obs env U registry target locals rightSubst right rawDemand resultFootprint
  adapter : NormalProfileAdapter env U registry target rawDemand (raiseProfile rank bound demand)
  resultAvailable : resultFootprint.Available available
  support : Profile rank
  typeFootprint : Footprint
  certificate : CodeCert env U registry target locals leftSubst sourceType support typeFootprint
  typeAvailable : typeFootprint.Available available
  typed : (raiseProfile rank bound demand).HasType support
  rawTyped : rawDemand.HasType support
  typeCode : TypeRelated env U registry target (sourceType.subst leftSubst)
    (sourceType.subst leftSubst) support
  related : Related env U registry target (left.subst leftSubst) (right.subst rightSubst)
    (sourceType.subst leftSubst) (raiseProfile rank bound demand) support
  rawRelated : Related env U registry target (right.subst rightSubst) (right.subst rightSubst)
    (sourceType.subst leftSubst) rawDemand support

namespace GradedTransferResult
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
  {left right sourceType : VExpr} {demand : Profile n}

noncomputable def ofFixed
    (result : TransferResult env U registry target locals σ τ
      available left right sourceType demand) :
    GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand where
  rank := n
  bound := Nat.le_refl n
  rawDemand := result.rawDemand
  resultFootprint := result.resultFootprint
  observation := result.observation
  adapter := by simpa only [raiseProfile_self] using result.adapter
  resultAvailable := result.resultAvailable
  support := result.support
  typeFootprint := result.typeFootprint
  certificate := result.certificate
  typeAvailable := result.typeAvailable
  typed := by simpa only [raiseProfile_self] using result.typed
  rawTyped := result.rawTyped
  typeCode := result.typeCode
  related := by simpa only [raiseProfile_self] using result.related
  rawRelated := result.rawRelated

noncomputable def requestedCertificate
    (result : GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand) :
    CodeCert env U registry target locals σ sourceType
      (lowerProfile n result.bound result.support) result.typeFootprint :=
  result.certificate.lower n result.bound

theorem requestedTyped
    (result : GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand) :
    demand.HasType (lowerProfile n result.bound result.support) :=
  lowerProfile.hasType result.bound result.typed

theorem requestedRelated (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (result : GradedTransferResult env U registry target locals σ τ
      available left right sourceType demand) :
    Related env U registry target (left.subst σ) (right.subst τ) (sourceType.subst σ)
      demand (lowerProfile n result.bound result.support) :=
  lowerProfile.related result.bound henv hTarget result.related

end GradedTransferResult

def GradedTransfer (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right sourceType : VExpr) : Prop :=
  ∀ {n : Nat} {demand : Profile n} {footprint : Footprint},
    Obs env U registry target locals leftSubst left demand footprint →
    footprint.Available available →
      Nonempty (GradedTransferResult env U registry target locals leftSubst rightSubst
        available left right sourceType demand)

def GradedJoint (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source : List VExpr) (left right sourceType : VExpr) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation), available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target leftSubst rightSubst source →
    PairedFits env U registry source target locals leftSubst rightSubst available →
      GradedTransfer env U registry target locals leftSubst rightSubst available left right sourceType ∧
      GradedTransfer env U registry target locals leftSubst rightSubst available right left sourceType ∧
      SortCorrect env U registry target locals leftSubst available left sourceType ∧
      SortCorrect env U registry target locals leftSubst available right sourceType

theorem Transfer.graded
    (original : Transfer env U registry target locals σ τ available left right sourceType) :
    GradedTransfer env U registry target locals σ τ available left right sourceType := by
  intro n demand footprint observation resources
  obtain ⟨result⟩ := original observation resources
  exact ⟨.ofFixed result⟩

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

theorem GradedTransfer.trans
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left middle right sourceType : VExpr}
    (first : GradedTransfer env U registry target locals σ σ
      available left middle sourceType)
    (second : GradedTransfer env U registry target locals σ τ
      available middle right sourceType) :
    GradedTransfer env U registry target locals σ τ
      available left right sourceType := by
  intro n demand footprint observation resources
  obtain ⟨a⟩ := first observation resources
  obtain ⟨b⟩ := second a.observation a.resultAvailable
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
    rawRelated := Related.retag henv rawTyped code b.rawRelated }⟩

theorem GradedJoint.symm
    (original : GradedJoint env U registry source left right sourceType) :
    GradedJoint env U registry source right left sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  have result := original target locals σ τ available closed hTarget substitutions fits
  exact ⟨result.2.1, result.1, result.2.2.2, result.2.2.1⟩

theorem GradedJoint.trans
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left middle right sourceType : VExpr}
    (first : GradedJoint env U registry source left middle sourceType)
    (second : GradedJoint env U registry source middle right sourceType) :
    GradedJoint env U registry source left right sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  have a := first target locals σ τ available closed hTarget substitutions fits
  have b := second target locals σ τ available closed hTarget substitutions fits
  have ad := first target locals σ σ available closed hTarget substitutions.left fits.left
  have bd := second target locals σ σ available closed hTarget substitutions.left fits.left
  exact ⟨GradedTransfer.trans henv hscoped hTarget ad.1 b.1,
    GradedTransfer.trans henv hscoped hTarget bd.2.1 a.2.1,
    a.2.2.1, b.2.2.2⟩

theorem GradedJoint.left
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left right sourceType : VExpr}
    (original : GradedJoint env U registry source left right sourceType) :
    GradedJoint env U registry source left left sourceType :=
  GradedJoint.trans henv hscoped original (GradedJoint.symm original)

theorem GradedJoint.right
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left right sourceType : VExpr}
    (original : GradedJoint env U registry source left right sourceType) :
    GradedJoint env U registry source right right sourceType :=
  GradedJoint.trans henv hscoped (GradedJoint.symm original) original

end Lean4Lean.AnchoredSource.Adapted
