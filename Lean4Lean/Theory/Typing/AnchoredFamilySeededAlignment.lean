import Lean4Lean.Theory.Typing.AnchoredFamilyCodeAlignment
import Lean4Lean.Theory.Typing.AnchoredNativeSeededRegistered

/-! Family alignment retains the finite requests subsequently needed by
constructor fields. The final paired substitution supports the actual requested
footprint, in addition to the intermediate family header's own certificates. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem PiRowCertificate.alignFamilyArgumentSeeded
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {A B x y : VExpr} {key : Key n} {result : Profile n}
    (row : PiRowCertificate env U registry target locals seed available A B key result)
    {level : VLevel}
    (originalDomain : OriginalTypePayload sourceEnv env U registry source A (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    (argument : Admitted env U registry target key x y)
    (extra : List Need)
    (extraBound : ∀ need ∈ extra, need.rank ≤ n)
    (extraCovered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    Nonempty (PiRowCertificate.FamilyArgumentAlignment env U registry target locals left available A key x y) ∧
    FamilyPrefixAlignment env U registry (A :: source) target (Locals.push locals)
      (seed.cons key.anchor) (left.cons x) (right.cons y)
      (Valuation.push (row.seedNeeds extra) available) := by
  have formedA := originalDomain.1.defeq.mono hle
  have seedTransfer : GradedTransfer env U registry target locals seed left available A A (.sort level) :=
    (originalDomain.2 target locals seed left available closed hTarget
    initial.seedSubstitutions initial.seedFits).1
  have pairTransfer : GradedTransfer env U registry target locals left right available A A (.sort level) :=
    (originalDomain.2 target locals left right available closed hTarget
    initial.substitutions initial.fits).1
  obtain ⟨leftDomain⟩ := row.domain.transfer_graded henv hscoped hTarget closed
    seedTransfer row.domainAvailable
  obtain ⟨rawAnchor, rawPair, _, _, _, _, anchorRelated, pairRelated⟩ :=
    row.alignment.admission henv argument
  have seedAnchor := Related.retag henv row.inputTyped
    leftDomain.related.left_diagonal anchorRelated
  have leftPair := Related.convert henv row.inputTyped leftDomain.related pairRelated
  have prefixPath : TypeConversion env U target (A.subst seed) (A.subst left) :=
    .single (formedA.substDF henv initial.seedSubstitutions.wf hTarget initial.seedSubstitutions)
  have actualPair := prefixPath.cast rawPair
  have coverage := row.seedCoverage extra extraBound extraCovered
  exact ⟨⟨{
    support := row.domainSupport
    footprint := leftDomain.footprint
    domain := leftDomain.certificate
    resources := leftDomain.available
    typed := row.inputTyped
    path := row.alignment.path.trans prefixPath
    raw := actualPair
    related := leftPair }⟩, {
    seedSubstitutions := .cons initial.seedSubstitutions formedA rawAnchor
    seedFits := initial.seedFits.pushGraded henv hscoped hTarget closed seedTransfer
      row.domain row.domainAvailable row.inputTyped seedAnchor (row.seedNeeds extra)
      (fun need hm => (coverage need hm).1) (fun need hm => (coverage need hm).2)
    substitutions := .cons initial.substitutions formedA actualPair
    fits := initial.fits.pushGraded henv hscoped hTarget closed pairTransfer
      leftDomain.certificate leftDomain.available row.inputTyped leftPair (row.seedNeeds extra)
      (fun need hm => (coverage need hm).1) (fun need hm => (coverage need hm).2) }⟩

/-- A finite stored telescope carries only original declaration payloads,
actual source rows, and finite coverage checks. The terminal footprint may be
any actual later field certificate's footprint in the completed context. -/
inductive FamilySeededCodeRows (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (required : Footprint) :
    (source : List VExpr) → (locals : List Nat) → (seed : Subst) →
    (available : Valuation) → VExpr → List VExpr → List FamilyKey → Type where
  | nil (resources : required.Available available) :
      FamilySeededCodeRows sourceEnv env U registry target required source locals seed available
        expression [] []
  | cons
      (original : OriginalTypePayload sourceEnv env U registry source A (.sort level))
      (row : PiRowCertificate env U registry target locals seed available A B (key : Key n) result)
      {support : Profile n}
      (admission : RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨key, support⟩ : DataRequest (Profile n)) key.anchor key.anchor)
      (extra : List Need)
      (bounded : ∀ need ∈ extra, need.rank ≤ n)
      (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
      (inputPresent : (⟨n, key.input⟩ : Need) ∈ row.seedNeeds extra)
      (tail : FamilySeededCodeRows sourceEnv env U registry target required (A :: source)
        (Locals.push locals) (seed.cons key.anchor) (Valuation.push (row.seedNeeds extra) available)
        B domains keys) :
      FamilySeededCodeRows sourceEnv env U registry target required source locals seed available
        (.forallE A B) (A :: domains) (⟨n, key, support⟩ :: keys)

/-- Every requested leaf survives the complete dependent alignment. Thus
subsequent original field-type transfers can actually use the resulting Fits. -/
theorem FamilySeededCodeRows.align
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target source : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required source locals seed available
      expression domains keys)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    {xs ys : List VExpr} (arguments : FamilyArguments env U registry target keys xs ys) :
    FamilyAlignedArguments env U registry target left domains keys xs ys ∧
    ∃ finalLocals finalAvailable,
      finalAvailable.AtomClosed ∧ required.Available finalAvailable ∧
      FamilyPrefixAlignment env U registry (domains.reverse ++ source) target finalLocals
        (familySubst seed (keys.map (·.key.anchor)))
        (familySubst left xs) (familySubst right ys) finalAvailable := by
  induction rows generalizing left right xs ys with
  | nil resources =>
    cases arguments
    exact ⟨.nil, _, _, closed, resources, initial⟩
  | @cons source A level locals seed available B n key result domains keys
      original row support admission extra bounded covered inputPresent tail ih =>
    cases arguments with
    | @cons _ x y _ xs ys argument rest =>
      obtain ⟨⟨aligned⟩, advanced⟩ := row.alignFamilyArgumentSeeded henv hscoped hle
        original closed hTarget initial argument.toAdmission extra bounded covered
      obtain ⟨alignedTail, finalLocals, finalAvailable, finalClosed, resources, final⟩ :=
        ih (row.seedClosed extra closed) advanced rest
      refine ⟨.cons aligned.raw aligned.typed aligned.related alignedTail,
        finalLocals, finalAvailable, finalClosed, resources, ?_⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_cons, familySubst, List.foldl_cons] using final

def FamilySeededCodeRows.terminalLocals
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source locals seed available expression domains keys) : List Nat :=
  match rows with
  | .nil _ => locals
  | .cons _ _ _ _ _ _ _ tail => tail.terminalLocals

def FamilySeededCodeRows.terminalValuation
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source locals seed available expression domains keys) : Valuation :=
  match rows with
  | .nil _ => available
  | .cons _ _ _ _ _ _ _ tail => tail.terminalValuation

/-- The exact terminal world is computable from the stored rows. Keeping it
literal lets a consumer retain an existing field certificate at that world. -/
theorem FamilySeededCodeRows.alignExact
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target source : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required source locals seed available
      expression domains keys)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    {xs ys : List VExpr} (arguments : FamilyArguments env U registry target keys xs ys) :
    FamilyAlignedArguments env U registry target left domains keys xs ys ∧
    rows.terminalValuation.AtomClosed ∧ required.Available rows.terminalValuation ∧
    FamilyPrefixAlignment env U registry (domains.reverse ++ source) target rows.terminalLocals
      (familySubst seed (keys.map (·.key.anchor)))
      (familySubst left xs) (familySubst right ys) rows.terminalValuation := by
  induction rows generalizing left right xs ys with
  | nil resources =>
    cases arguments
    exact ⟨.nil, closed, resources, initial⟩
  | @cons source A level locals seed available B n key result domains keys
      original row support admission extra bounded covered inputPresent tail ih =>
    cases arguments with
    | @cons _ x y _ xs ys argument rest =>
      obtain ⟨⟨aligned⟩, advanced⟩ := row.alignFamilyArgumentSeeded henv hscoped hle
        original closed hTarget initial argument.toAdmission extra bounded covered
      obtain ⟨alignedTail, finalClosed, resources, final⟩ :=
        ih (row.seedClosed extra closed) advanced rest
      refine ⟨.cons aligned.raw aligned.typed aligned.related alignedTail, finalClosed, resources, ?_⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_cons, familySubst, List.foldl_cons, terminalLocals, terminalValuation] using final

/-- Interpret an actual retained field/type certificate at both aligned
argument tuples. The resulting comparison uses the original declaration child
and the exact final finite ledger, never adequacy of a synthesized typing. -/
theorem FamilySeededCodeRows.transferTerminalCode
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target source : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required source locals seed available
      expression domains keys)
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
    rows.alignExact henv hscoped hle closed hTarget initial arguments
  obtain ⟨atLeft⟩ := certificate.transfer_graded henv hscoped hTarget finalClosed
    (original.2 target rows.terminalLocals _ _ rows.terminalValuation finalClosed hTarget
      final.seedSubstitutions final.seedFits).1 resources
  exact atLeft.certificate.transfer_graded henv hscoped hTarget finalClosed
    (original.2 target rows.terminalLocals _ _ rows.terminalValuation finalClosed hTarget
      final.substitutions final.fits).1 atLeft.available

end Lean4Lean.AnchoredSource.Adapted
