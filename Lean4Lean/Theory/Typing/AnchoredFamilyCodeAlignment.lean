import Lean4Lean.Theory.Typing.AnchoredNativeCodeRow
import Lean4Lean.Theory.Typing.AnchoredFamilyArguments

/-! Declaration-directed alignment of finite family argument observations.

Frozen argument keys need not use the declaration's dependent domains. Actual
header rows retain the finite domain conversions, and original formation
children transport those domains along the already aligned parameter initial.
Thus the argument relation demanded by an iota consumer is derived at the
actual left parameter/index prefix, without raw datatype injectivity.
-/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Keep both paths: source rows live at the frozen seed prefix, whereas a
computation pairs the two actual prefixes. These paths share one finite ledger. -/
structure FamilyPrefixAlignment (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (seed left right : Subst) (available : Valuation) : Prop where
  seedSubstitutions : Ctx.SubstEq env U target seed left source
  seedFits : PairedFits env U registry source target locals seed left available
  substitutions : Ctx.SubstEq env U target left right source
  fits : PairedFits env U registry source target locals left right available

namespace PiRowCertificate

/-- The current family argument at its actual declared domain. In particular,
`related` is at `A[left-prefix]`, not at the frozen key's arbitrary raw domain. -/
structure FamilyArgumentAlignment
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (left : Subst) (available : Valuation)
    (A : VExpr) (key : Key n) (x y : VExpr) where
  support : Profile n
  footprint : Footprint
  domain : CodeCert env U registry target locals left A support footprint
  resources : footprint.Available available
  typed : key.input.HasType support
  path : TypeConversion env U target key.domain (A.subst left)
  raw : env.IsDefEq U target x y (A.subst left)
  related : Related env U registry target x y (A.subst left) key.input support

/-- Consume one actual declaration row and one lower-rank family argument
admission. Original domain formation transfers its code across the aligned
prefix; no equality or observation of a newly generated domain is assumed. -/
theorem alignFamilyArgument
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {A B x y : VExpr} {key : Key n} {result : Profile n}
    (row : PiRowCertificate env U registry target locals seed available A B key result)
    {level : VLevel}
    (originalDomain : OriginalTypePayload sourceEnv env U registry source A (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    (argument : Admitted env U registry target key x y) :
    Nonempty (FamilyArgumentAlignment env U registry target locals left available A key x y) ∧
    FamilyPrefixAlignment env U registry (A :: source) target (Locals.push locals)
      (seed.cons key.anchor) (left.cons x) (right.cons y)
      (Valuation.push row.codeNeeds available) := by
  have formedA := originalDomain.1.defeq.mono hle
  have seedTransfer : GradedTransfer env U registry target locals seed left available A A (.sort level) :=
    (originalDomain.2 target locals seed left available closed hTarget
    initial.seedSubstitutions initial.seedFits).1
  have pairTransfer : GradedTransfer env U registry target locals left right available A A (.sort level) :=
    (originalDomain.2 target locals left right available closed hTarget
    initial.substitutions initial.fits).1
  obtain ⟨leftDomain⟩ := row.domain.transfer_graded henv hscoped hTarget closed
    seedTransfer row.domainAvailable
  have aligned := row.alignment.admission henv argument
  obtain ⟨rawAnchor, rawPair, _, _, _, _, anchorRelated, pairRelated⟩ := aligned
  have seedAnchor := Related.retag henv row.inputTyped
    leftDomain.related.left_diagonal anchorRelated
  have leftPair := Related.convert henv row.inputTyped leftDomain.related pairRelated
  have prefixPath : TypeConversion env U target (A.subst seed) (A.subst left) :=
    .single (formedA.substDF henv initial.seedSubstitutions.wf hTarget initial.seedSubstitutions)
  have actualPair := prefixPath.cast rawPair
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
      row.domain row.domainAvailable row.inputTyped seedAnchor row.codeNeeds
      (fun need hm => (row.codeCoverage need hm).1)
      (fun need hm => (row.codeCoverage need hm).2)
    substitutions := .cons initial.substitutions formedA actualPair
    fits := initial.fits.pushGraded henv hscoped hTarget closed pairTransfer
      leftDomain.certificate leftDomain.available row.inputTyped leftPair row.codeNeeds
      (fun need hm => (row.codeCoverage need hm).1)
      (fun need hm => (row.codeCoverage need hm).2) }⟩

end PiRowCertificate

/-- A finite sequence of actual source Pi rows, ending at the family's
declared result sort. Each child is stored in the row body's precise source
context and finite ledger. The original domain payload is a declaration child,
not a request for adequacy of an instantiated raw typing. -/
inductive FamilyCodeRows (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    (source : List VExpr) → (locals : List Nat) → (seed : Subst) →
    (available : Valuation) → VExpr → List VExpr → List FamilyKey → Type where
  | nil : FamilyCodeRows sourceEnv env U registry target source locals seed available
      (.sort level) [] []
  | cons {n : Nat} {key : Key n} {result support : Profile n}
      (original : OriginalTypePayload sourceEnv env U registry source A (.sort level))
      (row : PiRowCertificate env U registry target locals seed available A B key result)
      (tail : FamilyCodeRows sourceEnv env U registry target (A :: source)
        (Locals.push locals) (seed.cons key.anchor) (Valuation.push row.codeNeeds available)
        B domains keys) :
      FamilyCodeRows sourceEnv env U registry target source locals seed available
        (.forallE A B) (A :: domains) (⟨n, key, support⟩ :: keys)

/-- Arguments already aligned at the actual dependent declaration domains.
The support is existential, while the requested input remains literally fixed. -/
inductive FamilyAlignedArguments (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    Subst → List VExpr → List FamilyKey → List VExpr → List VExpr → Prop where
  | nil : FamilyAlignedArguments env U registry target left [] [] [] []
  | cons {key : FamilyKey} {support : Profile key.rank}
      (raw : env.IsDefEq U target x y (A.subst left))
      (typed : key.key.input.HasType support)
      (related : Related env U registry target x y (A.subst left) key.key.input support)
      (tail : FamilyAlignedArguments env U registry target (left.cons x) domains keys xs ys) :
      FamilyAlignedArguments env U registry target left (A :: domains)
        (key :: keys) (x :: xs) (y :: ys)

def familySubst (initial : Subst) (arguments : List VExpr) : Subst :=
  arguments.foldl (fun σ argument => σ.cons argument) initial

/-- A requested parameter or index is recovered at precisely its position in
the declared telescope, instantiated by the preceding actual left arguments. -/
theorem FamilyAlignedArguments.getElem?
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {left : Subst} {domains : List VExpr} {keys : List FamilyKey} {xs ys : List VExpr}
    (aligned : FamilyAlignedArguments env U registry target left domains keys xs ys)
    {index : Nat} {A : VExpr} {key : FamilyKey}
    (domain : domains[index]? = some A) (selected : keys[index]? = some key) :
    ∃ (x y : VExpr) (support : Profile key.rank), xs[index]? = some x ∧ ys[index]? = some y ∧
      key.key.input.HasType support ∧
      env.IsDefEq U target x y (A.subst (familySubst left (xs.take index))) ∧
      Related env U registry target x y (A.subst (familySubst left (xs.take index)))
        key.key.input support := by
  induction aligned generalizing index A key with
  | nil => simp at domain
  | cons raw typed related tail ih =>
    cases index with
    | zero =>
      cases Option.some.inj domain
      cases Option.some.inj selected
      exact ⟨_, _, _, rfl, rfl, typed, raw, related⟩
    | succ index =>
      simpa only [List.getElem?_cons_succ, List.take_succ_cons,
        familySubst, List.foldl_cons] using ih domain selected

/-- The finite rows are a literal decomposition of the supplied family
header, so unrelated dependent argument domains cannot be substituted. -/
theorem FamilyCodeRows.header
    (rows : FamilyCodeRows sourceEnv env U registry target source locals seed available
      expression domains keys) : ∃ level, expression = wrapForalls domains (.sort level) := by
  induction rows with
  | nil => exact ⟨_, rfl⟩
  | cons _ _ _ ih =>
    obtain ⟨level, same⟩ := ih
    exact ⟨level, congrArg (VExpr.forallE _) same⟩

theorem FamilyCodeRows.length
    (rows : FamilyCodeRows sourceEnv env U registry target source locals seed available
      expression domains keys) : domains.length = keys.length := by
  induction rows with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

/-- Consume the entire finite row spine. The result pairs the actual
constructor result arguments with the recursor's parameters and indices in
the exact declared telescope, retaining every lower argument request. -/
theorem FamilyCodeRows.align
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target source : List VExpr} {locals : List Nat} {seed left right : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr} {keys : List FamilyKey}
    (rows : FamilyCodeRows sourceEnv env U registry target source locals seed available
      expression domains keys)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (initial : FamilyPrefixAlignment env U registry source target locals seed left right available)
    {xs ys : List VExpr} (arguments : FamilyArguments env U registry target keys xs ys) :
    FamilyAlignedArguments env U registry target left domains keys xs ys ∧
    ∃ finalLocals finalAvailable,
      FamilyPrefixAlignment env U registry (domains.reverse ++ source) target finalLocals
        (familySubst seed (keys.map (·.key.anchor)))
        (familySubst left xs) (familySubst right ys) finalAvailable := by
  induction rows generalizing left right xs ys with
  | nil =>
    cases arguments
    exact ⟨.nil, _, _, initial⟩
  | @cons source locals seed available A level B n key result support domains keys original row tail ih =>
    cases arguments with
    | @cons _ x y _ xs ys argument rest =>
      obtain ⟨⟨aligned⟩, advanced⟩ := row.alignFamilyArgument henv hscoped hle
        original closed hTarget initial argument.toAdmission
      obtain ⟨alignedTail, finalLocals, finalAvailable, final⟩ :=
        ih (row.codeClosed closed) advanced rest
      refine ⟨.cons aligned.raw aligned.typed aligned.related alignedTail,
        finalLocals, finalAvailable, ?_⟩
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.map_cons, familySubst, List.foldl_cons] using final

/-- The family header's raw dependent argument equality is a consequence of
the binary finite observation, after declaration rows have been consumed. -/
theorem FamilyCodeRows.substitutions
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} {expression : VExpr} {domains : List VExpr} {keys : List FamilyKey}
    (rows : FamilyCodeRows sourceEnv env U registry target [] locals seed available
      expression domains keys)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    {xs ys : List VExpr} (arguments : FamilyArguments env U registry target keys xs ys) :
    Ctx.SubstEq env U target (familySubst left xs) (familySubst right ys) domains.reverse := by
  obtain ⟨_, _, _, final⟩ := rows.align henv hscoped hle closed hTarget
    ⟨.nil, .nil, .nil, .nil⟩ arguments
  simpa only [List.append_nil] using final.substitutions

end Lean4Lean.AnchoredSource.Adapted
