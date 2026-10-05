import Lean4Lean.Theory.Typing.AnchoredProjectionRows
import Lean4Lean.Theory.Typing.AnchoredFamilySeededAlignment

/-! Declaration replay for the minimal projection ledger. The original
formation tree is supplied here, outside source syntax, and consumed only
along its original telescope children. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem pushedClosed (closed : available.AtomClosed)
    (singletons : ∀ need ∈ needs, ∀ selected ∈ need.singletons, selected ∈ needs) :
    (Valuation.push needs available).AtomClosed := by
  intro index need member selected chosen
  cases index with
  | zero => exact singletons need member selected chosen
  | succ index => exact closed index need member selected chosen

/-- Erasure retains the exact domain observer, fixed admission and complete
finite binder ledger. No semantic field survives erasure. -/
def FamilySeededCodeRows.projectionRows
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source locals seed available expression domains keys) :
    ProjectionRows env U registry target required locals seed available expression domains keys :=
  match rows with
  | .nil resources => .nil resources
  | .cons _ row admission extra bounded covered inputPresent tail =>
    .cons ⟨row.domainSupport, row.domainFootprint, row.domain, row.domainAvailable,
        row.inputTyped, row.alignment⟩ admission (row.seedNeeds extra)
      (fun need member => (row.seedCoverage extra bounded covered need member).1)
      (fun need member => (row.seedCoverage extra bounded covered need member).2)
      inputPresent (by
        intro need member selected chosen
        exact Valuation.atomize_closed (fun _ => row.bodyFootprint.localNeeds ++ extra)
          0 need member selected chosen) tail.projectionRows

namespace ProjectionDomainRow

/-- Replay one literal domain using its original declaration child. The
source certificate is at the frozen anchors, whereas the returned prefix
compares the actual argument substitutions at the declaration's own types. -/
theorem align
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {A x y : VExpr} {key : Key n}
    (row : ProjectionDomainRow env U registry target locals seed available A key)
    {level : VLevel}
    (original : OriginalTypePayload sourceEnv env U registry source A (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    (argument : Admitted env U registry target key x y)
    (needs : List Need)
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    Nonempty (PiRowCertificate.FamilyArgumentAlignment env U registry target locals left available A key x y) ∧
    FamilyPrefixAlignment env U registry (A :: source) target (Locals.push locals)
      (seed.cons key.anchor) (left.cons x) (right.cons y)
      (Valuation.push needs available) := by
  have formedA := original.1.defeq.mono hle
  have seedTransfer : GradedTransfer env U registry target locals seed left available A A (.sort level) :=
    (original.2 target locals seed left available closed hTarget
      initial.seedSubstitutions initial.seedFits).1
  have pairTransfer : GradedTransfer env U registry target locals left right available A A (.sort level) :=
    (original.2 target locals left right available closed hTarget
      initial.substitutions initial.fits).1
  obtain ⟨leftDomain⟩ := row.certificate.transfer_graded henv hscoped hTarget closed
    seedTransfer row.resources
  obtain ⟨rawAnchor, rawPair, _, _, _, _, anchorRelated, pairRelated⟩ :=
    row.alignment.admission henv argument
  have seedAnchor := Related.retag henv row.typed
    leftDomain.related.left_diagonal anchorRelated
  have leftPair := Related.convert henv row.typed leftDomain.related pairRelated
  have prefixPath : TypeConversion env U target (A.subst seed) (A.subst left) :=
    .single (formedA.substDF henv initial.seedSubstitutions.wf hTarget initial.seedSubstitutions)
  have actualPair := prefixPath.cast rawPair
  exact ⟨⟨{
    support := row.support
    footprint := leftDomain.footprint
    domain := leftDomain.certificate
    resources := leftDomain.available
    typed := row.typed
    path := row.alignment.path.trans prefixPath
    raw := actualPair
    related := leftPair }⟩, {
    seedSubstitutions := .cons initial.seedSubstitutions formedA rawAnchor
    seedFits := initial.seedFits.pushGraded henv hscoped hTarget closed seedTransfer
      row.certificate row.resources row.typed seedAnchor needs bounded covered
    substitutions := .cons initial.substitutions formedA actualPair
    fits := initial.fits.pushGraded henv hscoped hTarget closed pairTransfer
      leftDomain.certificate leftDomain.available row.typed leftPair needs bounded covered }⟩

end ProjectionDomainRow

/-- The only semantic decoration is the original formation tree, an input
to interpretation rather than a field of the finite source plan. -/
theorem ProjectionRows.alignExact
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target source : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : ProjectionRows env U registry target required locals seed available expression domains keys)
    (formation : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) source expression)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    {xs ys : List VExpr} (arguments : FamilyArguments env U registry target keys xs ys) :
    FamilyAlignedArguments env U registry target left domains keys xs ys ∧
    rows.terminalValuation.AtomClosed ∧ required.Available rows.terminalValuation ∧
    FamilyPrefixAlignment env U registry (domains.reverse ++ source) target rows.terminalLocals
      (familySubst seed (keys.map (·.key.anchor)))
      (familySubst left xs) (familySubst right ys) rows.terminalValuation := by
  induction rows generalizing source left right xs ys with
  | nil resources =>
    cases arguments
    exact ⟨.nil, closed, resources, initial⟩
  | cons row admission needs bounded covered inputPresent singletons tail ih =>
    cases arguments with
    | cons argument rest =>
      obtain ⟨_, original⟩ := formation.domain.1
      obtain ⟨⟨aligned⟩, advanced⟩ := row.align henv hscoped hle
        original closed hTarget initial argument.toAdmission needs bounded covered
      obtain ⟨alignedTail, finalClosed, resources, final⟩ :=
        ih formation.codomain.2 (pushedClosed closed singletons) advanced rest
      refine ⟨.cons aligned.raw aligned.typed aligned.related alignedTail, finalClosed, resources, ?_⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_cons, familySubst, List.foldl_cons, terminalLocals, terminalValuation] using final

/-- Select the original declaration child at an exact row position. This
is recursion on retained literal Pi syntax, not adequacy of a reconstructed
formation derivation. -/
theorem ProjectionRows.originalDomain
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target source : List VExpr} {locals : List Nat} {seed : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : ProjectionRows env U registry target required locals seed available expression domains keys)
    {P : List VExpr → VExpr → VExpr → Prop}
    (formation : SourcePiFormation P source expression)
    (position : Nat) {domain : VExpr} (selected : domains[position]? = some domain) :
    (∃ level, P ((domains.take position).reverse ++ source) domain (.sort level)) ∧
      SourcePiFormation P ((domains.take position).reverse ++ source) domain := by
  induction rows generalizing source position with
  | nil => simp at selected
  | cons row admission needs bounded covered inputPresent singletons tail ih =>
    cases position with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      subst domain
      exact formation.domain
    | succ position =>
      have original := ih formation.codomain.2 position selected
      simpa only [List.take_succ_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using original

/-- Replay a selected domain/template after its dependency prefix. Both
transfers consume the genuine earlier declaration child supplied by the
caller; no formation proof synthesized from a projection is reinterpreted. -/
theorem ProjectionRows.transferTerminalCode
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target source : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : ProjectionRows env U registry target required locals seed available expression domains keys)
    (formation : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) source expression)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    {xs ys : List VExpr} (arguments : FamilyArguments env U registry target keys xs ys)
    {fieldType : VExpr} {level : VLevel} {support : Profile n}
    (original : OriginalTypePayload sourceEnv env U registry
      (domains.reverse ++ source) fieldType (.sort level))
    (certificate : CodeCert env U registry target rows.terminalLocals
      (familySubst seed (keys.map (·.key.anchor))) fieldType support required) :
    Nonempty (CodeTransferResult env U registry target rows.terminalLocals
      (familySubst left xs) (familySubst right ys) rows.terminalValuation
      fieldType fieldType support) := by
  obtain ⟨_, finalClosed, resources, final⟩ :=
    rows.alignExact henv hscoped hle formation closed hTarget initial arguments
  obtain ⟨atLeft⟩ := certificate.transfer_graded henv hscoped hTarget finalClosed
    (original.2 target rows.terminalLocals _ _ rows.terminalValuation finalClosed hTarget
      final.seedSubstitutions final.seedFits).1 resources
  exact atLeft.certificate.transfer_graded henv hscoped hTarget finalClosed
    (original.2 target rows.terminalLocals _ _ rows.terminalValuation finalClosed hTarget
      final.substitutions final.fits).1 atLeft.available

/-- An exact slice obtains its type child from the original full declaration
formation. The caller supplies only actual prefix admissions, not a semantic
capability for a synthesized projection or selected type. -/
theorem ProjectionRowSlice.transfer
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target source : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint} {position : Nat}
    (rows : ProjectionRows env U registry target required locals seed available expression domains keys)
    (slice : ProjectionRowSlice env U registry target locals seed available expression domains keys position)
    (formation : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) source expression)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    {xs ys : List VExpr}
    (arguments : FamilyArguments env U registry target (keys.take position) xs ys) :
    Nonempty (CodeTransferResult env U registry target slice.rows.terminalLocals
      (familySubst left xs) (familySubst right ys) slice.rows.terminalValuation
      slice.domain slice.domain slice.support) := by
  obtain ⟨⟨_, original⟩, _⟩ := rows.originalDomain formation position slice.domainAt
  exact slice.rows.transferTerminalCode henv hscoped hle formation closed hTarget
    initial arguments original slice.certificate

end Lean4Lean.AnchoredSource.Adapted
