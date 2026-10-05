import Lean4Lean.Theory.Typing.AnchoredSourceEnvelope
import Lean4Lean.Theory.Typing.AnchoredAdapterNormalization
import Lean4Lean.Theory.Typing.AnchoredSourceAdapterCode
import Lean4Lean.Theory.Typing.AnchoredSourcePairedFits

/-! Original-child transfer with an explicit raw observation and a finite
endpoint-supported adapter. Both the requested and raw demands retain actual
assigned-type provenance; no adapter interpretation is stored as a premise. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure AdaptedTransferResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right sourceType : VExpr) (demand : Profile n) where
  rawDemand : Profile n
  resultFootprint : Footprint
  observation : Obs env U registry target locals rightSubst right rawDemand resultFootprint
  adapter : NormalProfileAdapter env U registry target rawDemand demand
  resultAvailable : resultFootprint.Available available
  support : Profile n
  typeFootprint : Footprint
  certificate : CodeCert env U registry target locals leftSubst sourceType support typeFootprint
  typeAvailable : typeFootprint.Available available
  typed : demand.HasType support
  rawTyped : rawDemand.HasType support
  typeCode : TypeRelated env U registry target (sourceType.subst leftSubst)
    (sourceType.subst leftSubst) support
  related : Related env U registry target (left.subst leftSubst) (right.subst rightSubst)
    (sourceType.subst leftSubst) demand support
  rawRelated : Related env U registry target (right.subst rightSubst) (right.subst rightSubst)
    (sourceType.subst leftSubst) rawDemand support

def AdaptedTransfer (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right sourceType : VExpr) : Prop :=
  ∀ {n : Nat} {demand : Profile n} {footprint : Footprint},
    Obs env U registry target locals leftSubst left demand footprint →
    footprint.Available available →
      Nonempty (AdaptedTransferResult env U registry target locals leftSubst rightSubst
        available left right sourceType demand)

def AdaptedJoint (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source : List VExpr) (left right sourceType : VExpr) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation), available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target leftSubst rightSubst source →
    PairedFits env U registry source target locals leftSubst rightSubst available →
      AdaptedTransfer env U registry target locals leftSubst rightSubst available left right sourceType ∧
      AdaptedTransfer env U registry target locals leftSubst rightSubst available right left sourceType ∧
      SortCorrect env U registry target locals leftSubst available left sourceType ∧
      SortCorrect env U registry target locals leftSubst available right sourceType

/-- Symmetry exchanges endpoint clauses without rebuilding any observation. -/
theorem AdaptedJoint.symm
    (original : AdaptedJoint env U registry source left right sourceType) :
    AdaptedJoint env U registry source right left sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  have result := original target locals σ τ available closed hTarget substitutions fits
  exact ⟨result.2.1, result.1, result.2.2.2, result.2.2.1⟩

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom hm
  exact (List.mem_append.mp hm).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

/-- The middle observation is raw. Its adapter is replayed only after the
second original child has supplied its own actual assigned-type evidence. -/
theorem AdaptedTransfer.trans
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {leftSubst rightSubst : Subst}
    (hTarget : OnCtx target (env.IsType U))
    {available : Valuation} {left middle right sourceType : VExpr}
    (first : AdaptedTransfer env U registry target locals leftSubst leftSubst
      available left middle sourceType)
    (second : AdaptedTransfer env U registry target locals leftSubst rightSubst
      available middle right sourceType) :
    AdaptedTransfer env U registry target locals leftSubst rightSubst
      available left right sourceType := by
  intro n demand footprint observation resources
  obtain ⟨a⟩ := first observation resources
  obtain ⟨b⟩ := second a.observation a.resultAvailable
  have wf := a.typed.wf_type.union b.typed.wf_type
  have typed := a.typed.enlarge (Profile.le_union_left _ _) wf
  have rawTyped := b.rawTyped.enlarge (Profile.le_union_right _ _) wf
  have code := code_union a.typeCode b.typeCode
  have cross := NormalProfileAdapter.termMap a.adapter henv hscoped hTarget typed code b.related
  exact ⟨{
    rawDemand := b.rawDemand
    resultFootprint := b.resultFootprint
    observation := b.observation
    adapter := NormalProfileAdapter.comp b.adapter a.adapter
    resultAvailable := b.resultAvailable
    support := a.support.union b.support
    typeFootprint := a.typeFootprint ++ b.typeFootprint
    certificate := .union a.certificate b.certificate
    typeAvailable := fun i need hm => (List.mem_append.mp hm).elim
      (a.typeAvailable i need) (b.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.trans henv hscoped a.related cross
    rawRelated := Related.retag henv rawTyped code b.rawRelated }⟩

theorem AdaptedJoint.trans
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left middle right sourceType : VExpr}
    (first : AdaptedJoint env U registry source left middle sourceType)
    (second : AdaptedJoint env U registry source middle right sourceType) :
    AdaptedJoint env U registry source left right sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  have a := first target locals σ τ available closed hTarget substitutions fits
  have b := second target locals σ τ available closed hTarget substitutions fits
  have ad := first target locals σ σ available closed hTarget substitutions.left fits.left
  have bd := second target locals σ σ available closed hTarget substitutions.left fits.left
  exact ⟨AdaptedTransfer.trans henv hscoped hTarget ad.1 b.1,
    AdaptedTransfer.trans henv hscoped hTarget bd.2.1 a.2.1,
    a.2.2.1, b.2.2.2⟩

/-- Reflexive endpoint comparisons compose already established original-child
clauses. They do not interpret a synthesized source typing derivation. -/
theorem AdaptedJoint.left
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left right sourceType : VExpr}
    (original : AdaptedJoint env U registry source left right sourceType) :
    AdaptedJoint env U registry source left left sourceType :=
  AdaptedJoint.trans henv hscoped original (AdaptedJoint.symm original)

theorem AdaptedJoint.right
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left right sourceType : VExpr}
    (original : AdaptedJoint env U registry source left right sourceType) :
    AdaptedJoint env U registry source right right sourceType :=
  AdaptedJoint.trans henv hscoped (AdaptedJoint.symm original) original

theorem CodeCert.transfer_adapted
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {leftSubst rightSubst : Subst} {available : Valuation}
    {left right sourceType : VExpr}
    (closed : available.AtomClosed)
    (original : AdaptedTransfer env U registry target locals leftSubst rightSubst
      available left right sourceType)
    {profile : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry target locals leftSubst left profile footprint)
    (resources : footprint.Available available) :
    Nonempty (CodeTransferResult env U registry target locals leftSubst rightSubst
      available left right profile) := by
  match cert with
  | .seed observation formed =>
    obtain ⟨result⟩ := original observation resources
    obtain ⟨footprint, ⟨certificate⟩, _, available⟩ :=
      result.observation.codeCert_of_adapter henv result.adapter formed result.resultAvailable closed
    exact ⟨⟨footprint, certificate, available,
      result.related.code_of_sortable henv hscoped hTarget formed⟩⟩
  | .union left right =>
    obtain ⟨hl⟩ := left.transfer_adapted henv hscoped hTarget closed original
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := right.transfer_adapted henv hscoped hTarget closed original
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨⟨hl.footprint ++ hr.footprint, .union hl.certificate hr.certificate, ?_, ?_⟩⟩
    · intro i need hm
      exact (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
    · apply TypeRelated.of_singletons
      intro atom hm
      exact (List.mem_append.mp hm).elim
        (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
  | .pad source =>
    obtain ⟨result⟩ := source.transfer_adapted henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .pad result.certificate, result.available,
      result.related.pad henv⟩⟩
  | .unpad source =>
    obtain ⟨result⟩ := source.transfer_adapted henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .unpad result.certificate, result.available,
      (TypeRelated.pad_iff henv).mp result.related⟩⟩
  | .down source =>
    obtain ⟨result⟩ := source.transfer_adapted henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .down result.certificate, result.available,
      result.related.down henv⟩⟩
  | .map view source =>
    obtain ⟨result⟩ := source.transfer_adapted henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .map view result.certificate, result.available,
      view.codeMap henv hscoped result.related⟩⟩
  | .select source member =>
    obtain ⟨result⟩ := source.transfer_adapted henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .select result.certificate member, result.available,
      result.related.singleton member⟩⟩
termination_by sizeOf cert

theorem AdaptedTransfer.convert
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {leftSubst rightSubst : Subst}
    {available : Valuation} {left right A B : VExpr}
    (originalType : AdaptedJoint env U registry source A B (.sort level))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target leftSubst rightSubst source)
    (fits : PairedFits env U registry source target locals leftSubst rightSubst available)
    (originalTerm : AdaptedTransfer env U registry target locals leftSubst rightSubst
      available left right A) :
    AdaptedTransfer env U registry target locals leftSubst rightSubst available left right B := by
  intro n demand footprint observation resources
  obtain ⟨value⟩ := originalTerm observation resources
  have producer : AdaptedTransfer env U registry target locals leftSubst leftSubst
      available A B (.sort level) :=
    (originalType target locals leftSubst leftSubst available closed hTarget
      substitutions.left fits.left).1
  obtain ⟨type⟩ := value.certificate.transfer_adapted henv hscoped hTarget closed producer value.typeAvailable
  exact ⟨{
    rawDemand := value.rawDemand
    adapter := value.adapter
    resultFootprint := value.resultFootprint
    observation := value.observation
    resultAvailable := value.resultAvailable
    support := value.support
    typeFootprint := type.footprint
    certificate := type.certificate
    typeAvailable := type.available
    typed := value.typed
    rawTyped := value.rawTyped
    typeCode := TypeRelated.left_diagonal
      (TypeRelated.symm henv value.typed.wf_type type.related)
    rawRelated := Related.convert henv value.rawTyped type.related value.rawRelated
    related := Related.convert henv value.typed type.related value.related }⟩

end Lean4Lean.AnchoredSource
