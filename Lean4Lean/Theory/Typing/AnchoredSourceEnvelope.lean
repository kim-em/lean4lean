import Lean4Lean.Theory.Typing.AnchoredSourceFundamental

/-! Transport actual source type certificates through an original type-child
induction result. The envelope below records a typed support choice; it does
not claim the protected-resource preservation required for lambda transfer.
In particular, arbitrary envelopes are not new source-observation constructors.
-/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure CodeTransferResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right : VExpr) (profile : Profile n) where
  footprint : Footprint
  certificate : CodeCert env U registry target locals rightSubst right profile footprint
  available : footprint.Available available
  related : TypeRelated env U registry target (left.subst leftSubst)
    (right.subst rightSubst) profile

/-- The only semantic premise is the original child's transfer result. Each
recursive call below follows an actual stored certificate, including its maps
and grade changes. No synthesized source typing proof is interpreted. -/
theorem CodeCert.transfer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {leftSubst rightSubst : Subst} {available : Valuation}
    {left right sourceType : VExpr}
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
    exact ⟨⟨result.resultFootprint, .seed result.observation formed,
      result.resultAvailable,
      result.related.code_of_sortable henv hscoped hTarget formed⟩⟩
  | .union left right =>
    obtain ⟨hl⟩ := left.transfer henv hscoped hTarget original
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := right.transfer henv hscoped hTarget original
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨⟨hl.footprint ++ hr.footprint, .union hl.certificate hr.certificate, ?_, ?_⟩⟩
    · intro i need hm
      exact (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
    · apply TypeRelated.of_singletons
      intro atom hm
      exact (List.mem_append.mp hm).elim
        (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
  | .pad source =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget original resources
    exact ⟨⟨result.footprint, .pad result.certificate, result.available,
      result.related.pad henv⟩⟩
  | .unpad source =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget original resources
    exact ⟨⟨result.footprint, .unpad result.certificate, result.available,
      (TypeRelated.pad_iff henv).mp result.related⟩⟩
  | .down source =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget original resources
    exact ⟨⟨result.footprint, .down result.certificate, result.available,
      result.related.down henv⟩⟩
  | .map view source =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget original resources
    exact ⟨⟨result.footprint, .map view result.certificate, result.available,
      view.codeMap henv hscoped result.related⟩⟩
  | .select source member =>
    obtain ⟨result⟩ := source.transfer henv hscoped hTarget original resources
    exact ⟨⟨result.footprint, .select result.certificate member, result.available,
      result.related.singleton member⟩⟩
termination_by sizeOf cert

/-- A support envelope is a record of actual source evidence. Its two
footprints are deliberately separate: this record alone is not a rule for
adding arbitrary local demands to a computational observation. -/
structure SupportEnvelope (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst)
    (expression sourceType : VExpr) (demand : Profile n) where
  valueFootprint : Footprint
  observation : Obs env U registry target locals realization expression demand valueFootprint
  support : Profile n
  typeFootprint : Footprint
  certificate : CodeCert env U registry target locals realization sourceType support typeFootprint
  typed : demand.HasType support

/-- Retyping uses precisely the original A=B child, at the same realization.
It preserves the computational observation and support, and returns the binary
code bridge together with the actual new source type certificate. -/
theorem SupportEnvelope.retype
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {realization : Subst}
    {available : Valuation} {expression A B : VExpr} {demand : Profile n}
    (originalType : Joint env U registry source A B (.sort level))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target realization realization source)
    (fits : Fits env U registry source target locals realization realization available)
    (envelope : SupportEnvelope env U registry target locals realization expression A demand)
    (resources : envelope.typeFootprint.Available available) :
    ∃ result : SupportEnvelope env U registry target locals realization expression B demand,
      result.valueFootprint = envelope.valueFootprint ∧
      result.support = envelope.support ∧ result.typeFootprint.Available available ∧
      TypeRelated env U registry target (A.subst realization) (B.subst realization)
        envelope.support := by
  have producer : Transfer env U registry target locals realization realization
      available A B (.sort level) :=
    (originalType target locals realization realization available hTarget substitutions fits).1
  obtain ⟨changed⟩ := envelope.certificate.transfer henv hscoped hTarget producer resources
  exact ⟨⟨envelope.valueFootprint, envelope.observation, envelope.support,
    changed.footprint, changed.certificate, envelope.typed⟩,
    rfl, rfl, changed.available, changed.related⟩

theorem Fits.left
    (fits : Fits env U registry source target locals leftSubst rightSubst available) :
    Fits env U registry source target locals leftSubst leftSubst available := by
  constructor
  intro index need hm sourceType lookup
  obtain ⟨entry⟩ := fits.entry index need hm sourceType lookup
  exact ⟨⟨entry.support, entry.footprint, entry.certificate, entry.available,
    entry.typed, entry.related.left_diagonal⟩⟩

/-- The value-and-certificate part of the original `defeqDF` case. The
original term child keeps its demand and target observation; the original
type child transfers its actual assigned-type certificate before conversion.
This does not claim the separate `SortCorrect` or protected-resource clauses.
-/
theorem Transfer.convert
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {leftSubst rightSubst : Subst}
    {available : Valuation} {left right A B : VExpr}
    (originalType : Joint env U registry source A B (.sort level))
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target leftSubst rightSubst source)
    (fits : Fits env U registry source target locals leftSubst rightSubst available)
    (originalTerm : Transfer env U registry target locals leftSubst rightSubst
      available left right A) :
    Transfer env U registry target locals leftSubst rightSubst available left right B := by
  intro n demand footprint observation resources
  obtain ⟨value⟩ := originalTerm observation resources
  have producer : Transfer env U registry target locals leftSubst leftSubst
      available A B (.sort level) :=
    (originalType target locals leftSubst leftSubst available hTarget
      substitutions.left fits.left).1
  obtain ⟨type⟩ := value.certificate.transfer henv hscoped hTarget producer value.typeAvailable
  exact ⟨{
    resultFootprint := value.resultFootprint
    observation := value.observation
    resultAvailable := value.resultAvailable
    support := value.support
    typeFootprint := type.footprint
    certificate := type.certificate
    typeAvailable := type.available
    typed := value.typed
    related := Related.convert henv value.typed type.related value.related }⟩

end Lean4Lean.AnchoredSource
