import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceBinder
import Lean4Lean.Theory.Typing.AnchoredFamilySeededAlignment
import Lean4Lean.Theory.Typing.AnchoredProjectionRows

/-! An unused declaration-prefix binder needs raw typing for substitution,
but no semantic interpretation of its domain. Empty needs at any grades can
be fitted directly, including the empty request retained by a row ledger.
This is the sparse-prefix case of projection source reification. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Fits.pushEmptyNeeds
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A x y : VExpr} {needs : List Need}
    (fits : Fits env U registry source target locals left right available)
    (empty : ∀ need ∈ needs, need.profile = .empty) :
    Fits env U registry (A :: source) target (Locals.push locals)
      (left.cons x) (right.cons y) (Valuation.push needs available) := by
  constructor
  intro index need member sourceType lookup
  cases lookup with
  | zero =>
    refine ⟨⟨.empty, [], .seed .empty
      (Profile.HasType.empty (Profile.HasType.sort true).wf_value),
      (fun _ _ impossible => nomatch impossible), ?_, ?_⟩⟩
    · rw [empty need member]
      exact Profile.HasType.empty Profile.WF.empty
    · rw [empty need member]
      cases need.rank <;> exact fun _ impossible => nomatch impossible
  | succ lookup =>
    obtain ⟨entry⟩ := fits.entry _ need member _ lookup
    have certificate := entry.certificate.renameSource (.skip .refl)
      (left.cons x) rfl (Locals.push locals)
    refine ⟨⟨entry.support, entry.footprint.sourceLift (.skip .refl),
      ?_, ?_, entry.typed, ?_⟩⟩
    · simpa only [← lift_eq_lift'] using certificate
    · intro index requested present
      obtain ⟨⟨originalIndex, originalNeed⟩, originalMember, equal⟩ := List.mem_map.mp present
      cases equal
      exact entry.available _ _ originalMember
    · simpa only [Subst.cons, lift_subst_cons] using entry.related

theorem PairedFits.pushEmptyNeeds
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation} {A x y : VExpr} {needs : List Need}
    (fits : PairedFits env U registry source target locals left right available)
    (empty : ∀ need ∈ needs, need.profile = .empty) :
    PairedFits env U registry (A :: source) target (Locals.push locals)
      (left.cons x) (right.cons y) (Valuation.push needs available) :=
  ⟨fits.forward.pushEmptyNeeds empty, fits.backward.pushEmptyNeeds empty⟩

/-- Advance an unused prefix position with only original raw formation and
raw argument equalities. Neither a domain CodeCert nor a GradedJoint callback
is required. Source leaves for the later selected field remain unchanged. -/
theorem FamilyPrefixAlignment.pushEmptyNeeds
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {A anchor x y : VExpr} {level : VLevel} {needs : List Need}
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    (formation : env.HasType U source A (.sort level))
    (anchorPair : env.IsDefEq U target anchor x (A.subst seed))
    (arguments : env.IsDefEq U target x y (A.subst left))
    (empty : ∀ need ∈ needs, need.profile = .empty) :
    FamilyPrefixAlignment env U registry (A :: source) target (Locals.push locals)
      (seed.cons anchor) (left.cons x) (right.cons y) (Valuation.push needs available) :=
  ⟨.cons initial.seedSubstitutions formation anchorPair,
    initial.seedFits.pushEmptyNeeds empty,
    .cons initial.substitutions formation arguments,
    initial.fits.pushEmptyNeeds empty⟩

/-- The actual declaration-row consumer also avoids a semantic domain call
when the retained requests are empty. Its raw alignment still uses the
declared domain and the actual two argument substitutions. -/
theorem ProjectionDomainRow.alignEmpty
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {A x y : VExpr} {level : VLevel} {key : Key n}
    (row : ProjectionDomainRow env U registry target locals seed available A key)
    (formation : env.HasType U source A (.sort level))
    (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    (argument : Admitted env U registry target key x y)
    (emptyInput : key.input = .empty) {needs : List Need}
    (emptyNeeds : ∀ need ∈ needs, need.profile = .empty) :
    Nonempty (PiRowCertificate.FamilyArgumentAlignment env U registry target locals left available
      A key x y) ∧
    FamilyPrefixAlignment env U registry (A :: source) target (Locals.push locals)
      (seed.cons key.anchor) (left.cons x) (right.cons y) (Valuation.push needs available) := by
  have rawAnchor := row.alignment.path.cast argument.1
  have rawPair := row.alignment.path.cast argument.2.1
  have prefixPath : TypeConversion env U target (A.subst seed) (A.subst left) :=
    .single (formation.substDF henv initial.seedSubstitutions.wf hTarget initial.seedSubstitutions)
  have actualPair := prefixPath.cast rawPair
  refine ⟨⟨{
    support := .empty
    footprint := []
    domain := .seed .empty (Profile.HasType.empty (Profile.HasType.sort true).wf_value)
    resources := fun _ _ impossible => nomatch impossible
    typed := ?_
    path := row.alignment.path.trans prefixPath
    raw := actualPair
    related := ?_ }⟩,
    initial.pushEmptyNeeds formation rawAnchor actualPair emptyNeeds⟩
  · rw [emptyInput]
    exact Profile.HasType.empty Profile.WF.empty
  · rw [emptyInput]
    cases n <;> exact fun _ impossible => nomatch impossible

end Lean4Lean.AnchoredSource.Adapted
