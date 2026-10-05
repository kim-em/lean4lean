import Lean4Lean.Theory.Typing.AnchoredAdaptedSourcePruning
import Lean4Lean.Theory.Typing.AnchoredSourcePairedFits

/-! Joint original-derivation contract over the replacement mutual core.
The finite fitting entries and returned certificates are NEW-core evidence. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure ValuationEntry (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (left right : Subst)
    (available : Valuation) (index : Nat) (need : Need) (sourceType : VExpr) where
  support : Profile need.rank
  footprint : Footprint
  certificate : CodeCert env U registry target locals left sourceType support footprint
  available : footprint.Available available
  typed : need.profile.HasType support
  related : Related env U registry target (left index) (right index)
    (sourceType.subst left) need.profile support

/-- Every available lookup demand has an actual source type certificate.
There is no universal semantic producer stored in an entry. -/
structure Fits (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat) (left right : Subst)
    (available : Valuation) : Prop where
  entry : ∀ index need, need ∈ available index → ∀ sourceType,
    Lookup source index sourceType →
      Nonempty (ValuationEntry env U registry target locals left right
        available index need sourceType)

theorem Fits.left
    (fits : Fits env U registry source target locals leftSubst rightSubst available) :
    Fits env U registry source target locals leftSubst leftSubst available := by
  constructor
  intro index need hm sourceType lookup
  obtain ⟨entry⟩ := fits.entry index need hm sourceType lookup
  exact ⟨⟨entry.support, entry.footprint, entry.certificate, entry.available,
    entry.typed, entry.related.left_diagonal⟩⟩

theorem Fits.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {source target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    {locals : List Nat} {left right : Subst} {available : Valuation}
    (fits : Fits env U registry source target locals left right available) :
    Fits env U registry source future locals (left.lift_r ρ) (right.lift_r ρ)
      (Valuation.rename ρ available) := by
  constructor
  intro index need hm sourceType lookup
  obtain ⟨original, horiginal, he⟩ := List.mem_map.mp hm
  subst need
  obtain ⟨entry⟩ := fits.entry index original horiginal sourceType lookup
  refine ⟨⟨entry.support.rename ρ, Footprint.rename ρ entry.footprint,
    entry.certificate.future henv insertion, entry.available.rename ρ,
    Profile.rename_hasType_iff.mpr entry.typed, ?_⟩⟩
  simpa only [Need.rename, Subst.lift_r, lift'_subst] using
    entry.related.future henv insertion

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


end PairedFits

structure CodeTransferResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right : VExpr) (profile : Profile n) where
  footprint : Footprint
  certificate : CodeCert env U registry target locals rightSubst right profile footprint
  available : footprint.Available available
  related : TypeRelated env U registry target (left.subst leftSubst)
    (right.subst rightSubst) profile


def SortCorrect (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst)
    (available : Valuation) (expression sourceType : VExpr) : Prop :=
  ∀ level relevant, sourceType = .sort level → Relevant level relevant →
    ∀ {n : Nat} {demand : Profile n} {footprint : Footprint},
      Obs env U registry target locals realization expression demand footprint →
      footprint.Available available → demand.HasType (.sort relevant)


structure TransferResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
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

def Transfer (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right sourceType : VExpr) : Prop :=
  ∀ {n : Nat} {demand : Profile n} {footprint : Footprint},
    Obs env U registry target locals leftSubst left demand footprint →
    footprint.Available available →
      Nonempty (TransferResult env U registry target locals leftSubst rightSubst
        available left right sourceType demand)

def Joint (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source : List VExpr) (left right sourceType : VExpr) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation), available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target leftSubst rightSubst source →
    PairedFits env U registry source target locals leftSubst rightSubst available →
      Transfer env U registry target locals leftSubst rightSubst available left right sourceType ∧
      Transfer env U registry target locals leftSubst rightSubst available right left sourceType ∧
      SortCorrect env U registry target locals leftSubst available left sourceType ∧
      SortCorrect env U registry target locals leftSubst available right sourceType

/-- Symmetry exchanges endpoint clauses without rebuilding any observation. -/
theorem Joint.symm
    (original : Joint env U registry source left right sourceType) :
    Joint env U registry source right left sourceType := by
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
theorem Transfer.trans
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {leftSubst rightSubst : Subst}
    (hTarget : OnCtx target (env.IsType U))
    {available : Valuation} {left middle right sourceType : VExpr}
    (first : Transfer env U registry target locals leftSubst leftSubst
      available left middle sourceType)
    (second : Transfer env U registry target locals leftSubst rightSubst
      available middle right sourceType) :
    Transfer env U registry target locals leftSubst rightSubst
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

theorem Joint.trans
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left middle right sourceType : VExpr}
    (first : Joint env U registry source left middle sourceType)
    (second : Joint env U registry source middle right sourceType) :
    Joint env U registry source left right sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  have a := first target locals σ τ available closed hTarget substitutions fits
  have b := second target locals σ τ available closed hTarget substitutions fits
  have ad := first target locals σ σ available closed hTarget substitutions.left fits.left
  have bd := second target locals σ σ available closed hTarget substitutions.left fits.left
  exact ⟨Transfer.trans henv hscoped hTarget ad.1 b.1,
    Transfer.trans henv hscoped hTarget bd.2.1 a.2.1,
    a.2.2.1, b.2.2.2⟩

/-- Reflexive endpoint comparisons compose already established original-child
clauses. They do not interpret a synthesized source typing derivation. -/
theorem Joint.left
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left right sourceType : VExpr}
    (original : Joint env U registry source left right sourceType) :
    Joint env U registry source left left sourceType :=
  Joint.trans henv hscoped original (Joint.symm original)

theorem Joint.right
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left right sourceType : VExpr}
    (original : Joint env U registry source left right sourceType) :
    Joint env U registry source right right sourceType :=
  Joint.trans henv hscoped (Joint.symm original) original

theorem CodeCert.transfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {leftSubst rightSubst : Subst} {available : Valuation}
    {left right sourceType : VExpr}
    (closed : available.AtomClosed)
    (original : Transfer env U registry target locals leftSubst rightSubst
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
    obtain ⟨hl⟩ := left.transfer henv hscoped hTarget closed original
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := right.transfer henv hscoped hTarget closed original
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨⟨hl.footprint ++ hr.footprint, .union hl.certificate hr.certificate, ?_, ?_⟩⟩
    · intro i need hm
      exact (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
    · apply TypeRelated.of_singletons
      intro atom hm
      exact (List.mem_append.mp hm).elim
        (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
  | .pad source =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .pad result.certificate, result.available,
      result.related.pad henv⟩⟩
  | .familyPad source =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .familyPad result.certificate, result.available,
      result.related.familyPad henv⟩⟩
  | .unpad source =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .unpad result.certificate, result.available,
      (TypeRelated.pad_iff henv).mp result.related⟩⟩
  | .down source =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .down result.certificate, result.available,
      result.related.down henv⟩⟩
  | .map view source =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .map view result.certificate, result.available,
      view.codeMap henv hscoped result.related⟩⟩
  | .select source member =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .select result.certificate member, result.available,
      result.related.singleton member⟩⟩
  | .focusMinimal source minimal focusedBound =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget closed original resources
    exact ⟨⟨result.footprint, .focusMinimal result.certificate minimal focusedBound, result.available,
      result.related.focusMinimal henv minimal focusedBound⟩⟩
termination_by sizeOf cert

theorem Transfer.convert
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {leftSubst rightSubst : Subst}
    {available : Valuation} {left right A B : VExpr}
    (originalType : Joint env U registry source A B (.sort level))
    (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target leftSubst rightSubst source)
    (fits : PairedFits env U registry source target locals leftSubst rightSubst available)
    (originalTerm : Transfer env U registry target locals leftSubst rightSubst
      available left right A) :
    Transfer env U registry target locals leftSubst rightSubst available left right B := by
  intro n demand footprint observation resources
  obtain ⟨value⟩ := originalTerm observation resources
  have producer : Transfer env U registry target locals leftSubst leftSubst
      available A B (.sort level) :=
    (originalType target locals leftSubst leftSubst available closed hTarget
      substitutions.left fits.left).1
  obtain ⟨type⟩ := value.certificate.transfer henv hscoped hTarget closed producer value.typeAvailable
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

end Lean4Lean.AnchoredSource.Adapted
