import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFamilyPlanRows

/-! Fixed family requests are aligned against the original declaration
through exact source tails. The anchor seed and both actual prefixes retain
one finite ledger, including every requested later field leaf. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

namespace SortablePiRowCertificate
structure FamilyArgumentAlignment
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (left : Subst) (available : Valuation)
    (A : VExpr) (key : Key n) (x y : VExpr) where
  support : Profile n
  footprint : Footprint
  domain : SortableCert env U registry target locals left A true support footprint
  resources : footprint.Available available
  typed : key.input.HasType support
  path : TypeConversion env U target key.domain (A.subst left)
  raw : env.IsDefEq U target x y (A.subst left)
  related : Related env U registry target x y (A.subst left) key.input support

end SortablePiRowCertificate

structure OriginalSortableFamilyPrefixAlignment
    (headerEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat)
    (seed left right : Subst) (available : Valuation) where
  context : ContextDerivation headerEnv U source
  seedSubstitutions : Ctx.SubstEq env U target seed left source
  seedFits : SortableTailPairedFits env registry target context locals seed left available
  substitutions : Ctx.SubstEq env U target left right source
  fits : SortableTailPairedFits env registry target context locals left right available

noncomputable def OriginalSortableFamilyPrefixAlignment.reorigin
    (initial : OriginalSortableFamilyPrefixAlignment headerEnv env U registry source target locals seed left right available)
    (context : ContextDerivation headerEnv U source) :
    OriginalSortableFamilyPrefixAlignment headerEnv env U registry source target locals seed left right available where
  context := context
  seedSubstitutions := initial.seedSubstitutions
  seedFits := ⟨initial.seedFits.forward.reorigin context, initial.seedFits.backward.reorigin context,
    initial.seedFits.forward.reorigin_contextDerivation context,
    initial.seedFits.backward.reorigin_contextDerivation context⟩
  substitutions := initial.substitutions
  fits := ⟨initial.fits.forward.reorigin context, initial.fits.backward.reorigin context,
    initial.fits.forward.reorigin_contextDerivation context,
    initial.fits.backward.reorigin_contextDerivation context⟩

theorem SortablePiRowCertificate.alignFamilyArgumentOriginal
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {A B x y : VExpr} {key : Key n} {result : Profile n}
    (row : SortablePiRowCertificate env U registry target locals seed available true A B key result)
    {level : VLevel} (context : ContextDerivation headerEnv U source)
    (original : EndpointRef headerEnv U source A (.sort level))
    (domainIH : StateSortableFundamental env registry context (.ref original))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : OriginalSortableFamilyPrefixAlignment headerEnv env U registry source target locals seed left right available)
    (argument : Admitted env U registry target key x y)
    (extra : List Need)
    (bounded : ∀ need ∈ extra, need.rank ≤ n)
    (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    Nonempty (SortablePiRowCertificate.FamilyArgumentAlignment env U registry target locals left available A key x y) ∧
    Nonempty (OriginalSortableFamilyPrefixAlignment headerEnv env U registry (A :: source) target (Locals.push locals)
      (seed.cons key.anchor) (left.cons x) (right.cons y)
      (Valuation.push (row.seedNeeds extra) available)) := by
  let initial := initial.reorigin context
  have formedA := original.sound.defeq.mono below
  have seedTransfer : SortableTransfer env U registry target locals seed left available A A (.sort level) :=
    (domainIH target locals seed left available closed hTarget
      initial.seedSubstitutions initial.seedFits)
  have pairTransfer : SortableTransfer env U registry target locals left right available A A (.sort level) :=
    (domainIH target locals left right available closed hTarget
      initial.substitutions initial.fits)
  obtain ⟨leftDomain⟩ := seedTransfer row.domain row.domainAvailable
  obtain ⟨rawAnchor, rawPair, _, _, _, _, anchorRelated, pairRelated⟩ :=
    row.alignment.admission henv argument
  have seedAnchor := Related.retag henv row.inputTyped
    leftDomain.related.left_diagonal anchorRelated
  have leftPair := Related.convert henv row.inputTyped leftDomain.related pairRelated
  have prefixPath : TypeConversion env U target (A.subst seed) (A.subst left) :=
    .single (formedA.substDF henv initial.seedSubstitutions.wf hTarget initial.seedSubstitutions)
  have actualPair := prefixPath.cast rawPair
  have coverage := row.seedCoverage extra bounded covered
  obtain ⟨seedFits⟩ := initial.seedFits.pushSortableOriginal henv original seedTransfer
    row.domain row.domainAvailable row.inputTyped seedAnchor (row.seedNeeds extra)
    (fun need hm => (coverage need hm).1) (fun need hm => (coverage need hm).2)
  obtain ⟨fits⟩ := initial.fits.pushSortableOriginal henv original pairTransfer
    leftDomain.certificate leftDomain.available row.inputTyped leftPair (row.seedNeeds extra)
    (fun need hm => (coverage need hm).1) (fun need hm => (coverage need hm).2)
  exact ⟨⟨{
    support := row.domainSupport
    footprint := leftDomain.footprint
    domain := leftDomain.certificate
    resources := leftDomain.available
    typed := row.inputTyped
    path := row.alignment.path.trans prefixPath
    raw := actualPair
    related := leftPair }⟩, ⟨{
    context := .cons context original
    seedSubstitutions := .cons initial.seedSubstitutions formedA rawAnchor
    seedFits := seedFits
    substitutions := .cons initial.substitutions formedA actualPair
    fits := fits }⟩⟩

/-- Consume the exact frozen request tuple. Every domain call is the stored
original header location, and the final valuation is literally the one that
retains the consumer's original field certificate. -/
theorem OriginalSortableFamilyCodeRows.alignExact
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {headerType : VExpr} {header : OriginalFamilyHeader headerEnv U headerType}
    (calls : header.SortableFundamentals env registry)
    {target source : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : OriginalSortableFamilyCodeRows header env registry target required source locals seed available
      expression domains keys)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : OriginalSortableFamilyPrefixAlignment headerEnv env U registry source target locals seed left right available)
    {xs ys : List VExpr} (arguments : FamilyArguments env U registry target keys xs ys) :
    FamilyAlignedArguments env U registry target left domains keys xs ys ∧
    rows.terminalValuation.AtomClosed ∧ required.Available rows.terminalValuation ∧
    Nonempty (OriginalSortableFamilyPrefixAlignment headerEnv env U registry (domains.reverse ++ source) target rows.terminalLocals
      (familySubst seed (keys.map (·.key.anchor)))
      (familySubst left xs) (familySubst right ys) rows.terminalValuation) := by
  induction rows generalizing left right xs ys with
  | nil resources =>
    cases arguments
    exact ⟨.nil, closed, resources, ⟨initial⟩⟩
  | @cons source A level locals seed available B n key result domains keys
      original location row support admission extra bounded covered inputPresent tail ih =>
    cases arguments with
    | @cons _ x y _ xs ys argument rest =>
      obtain ⟨⟨aligned⟩, ⟨advanced⟩⟩ := row.alignFamilyArgumentOriginal henv hscoped below
        (location.contextDerivation .nil) original (calls location) closed hTarget initial
        argument.toAdmission extra bounded covered
      obtain ⟨alignedTail, finalClosed, resources, final⟩ :=
        ih (row.seedClosed extra closed) advanced rest
      refine ⟨.cons aligned.raw aligned.typed aligned.related alignedTail, finalClosed, resources, ?_⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_cons, familySubst, List.foldl_cons, OriginalSortableFamilyCodeRows.terminalLocals,
        OriginalSortableFamilyCodeRows.terminalValuation] using final

end Lean4Lean.AnchoredSource.Adapted
