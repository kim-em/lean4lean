import Lean4Lean.Theory.Typing.AnchoredFamilyArgumentRequest
import Lean4Lean.Theory.Typing.AnchoredConstantCodePath
import Lean4Lean.Theory.Typing.AnchoredFamilyArguments

/-! Actual requested family arguments are carried backwards through the
original Strong application and conversion tree. The resulting closed header
certificate has finite grade and retains every concrete argument request.
-/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem _root_.Lean4Lean.AnchoredSource.LambdaGuard.familyAdmission
    {key : Key n} {support : Profile n}
    (henv : env.Ordered)
    (guard : LambdaGuard env U registry target σ A key support) :
    RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨key, support⟩ : DataRequest (Profile n)) key.anchor key.anchor := by
  obtain ⟨anchor, pair, _, _, _, _, first, last⟩ := guard.anchor
  exact ⟨anchor, pair, guard.inputTyped, guard.formed, guard.domains.left_diagonal,
    Related.retag henv guard.inputTyped guard.domains.left_diagonal first,
    Related.retag henv guard.inputTyped guard.domains.left_diagonal last⟩

/-- A finite list of source observations, rather than a semantic supplier
for arbitrary frozen keys. -/
inductive FamilyArgumentRequests (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) : List VExpr → Type where
  | nil : FamilyArgumentRequests env U registry target locals σ available []
  | cons (request : FamilyArgumentRequest env U registry target locals σ available a)
      (tail : FamilyArgumentRequests env U registry target locals σ available as) :
      FamilyArgumentRequests env U registry target locals σ available (a :: as)

theorem FamilyArgumentRequests.split
    (requests : FamilyArgumentRequests env U registry target locals σ available (before ++ after)) :
    Nonempty (FamilyArgumentRequests env U registry target locals σ available before) ∧
    Nonempty (FamilyArgumentRequests env U registry target locals σ available after) := by
  induction before with
  | nil => exact ⟨⟨.nil⟩, ⟨requests⟩⟩
  | cons head tail ih =>
    cases requests with
    | cons request rest =>
      obtain ⟨⟨first⟩, last⟩ := ih rest
      exact ⟨⟨.cons request first⟩, last⟩

theorem FamilyArgumentRequests.splitLast
    (requests : FamilyArgumentRequests env U registry target locals σ available (before ++ [a])) :
    Nonempty (FamilyArgumentRequests env U registry target locals σ available before) ∧
    Nonempty (FamilyArgumentRequest env U registry target locals σ available a) := by
  obtain ⟨first, ⟨last⟩⟩ := requests.split
  cases last with
  | cons request rest => exact ⟨first, ⟨request⟩⟩

inductive FamilySpineCertificate (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    (expression assigned : VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | constant {info : VConstant}
      (lookup : sourceEnv.constants name = some info)
      (formation : SourcePiFormation (OriginalTypePayload sourceEnv env U registry)
        source (info.type.instL levels))
      (certificate : CodeCert env U registry target locals σ (info.type.instL levels) profile footprint)
      (resources : footprint.Available available) :
      FamilySpineCertificate sourceEnv env U registry source target locals σ available name levels
        (.const name levels) (info.type.instL levels) profile footprint
  | application
      (frame : FamilyApplicationInput env U registry target locals σ available A B a result before request)
      (function : FamilySpineCertificate sourceEnv env U registry source target locals σ available name levels
        f (.forallE A B) frame.profile frame.footprint) :
      FamilySpineCertificate sourceEnv env U registry source target locals σ available name levels
        (.app f a) (B.inst a) result before
  | conversion
      {original : sourceEnv.IsDefEqStrong U source A B (.sort level)}
      (edge : OriginalPayload sourceEnv env U registry original)
      (certificate : CodeCert env U registry target locals σ B profile footprint)
      (transfer : CodeTransferResult env U registry target locals σ σ available B A profile)
      (term : FamilySpineCertificate sourceEnv env U registry source target locals σ available name levels
        expression A profile transfer.footprint) :
      FamilySpineCertificate sourceEnv env U registry source target locals σ available name levels
        expression B profile footprint

/-- Produce the whole-header request from the actual finite argument
observations. Conversion transports the constructed code using the ORIGINAL
equality child; no family or Pi injectivity is used. -/
theorem HasTypeStrong.familySpineCertificate
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {expression assigned : VExpr} {structural : Bool} {name : Name} {levels : List VLevel}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (requests : FamilyArgumentRequests env U registry target locals σ available expression.getAppFnArgs.2)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (FamilySpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) := by
  induction original generalizing n footprint with
  | const lookup hw hl hu closedType type ihClosed ihType =>
    simp only [VExpr.getAppFnArgs_const] at head
    cases head
    exact ⟨.constant lookup (earlier type.refl).leftFormation certificate resources⟩
  | app hu hv domain codomain whole function argument result ihD ihC ihW ihF ihA ihR =>
    simp only [VExpr.getAppFnArgs_app] at requests
    obtain ⟨⟨requests⟩, ⟨request⟩⟩ := requests.splitLast
    obtain ⟨frame⟩ := certificate.familyApplicationInput henv hscoped hle
      ⟨argument.refl, (earlier argument.refl).joint⟩ closed hTarget substitutions fits request resources
    obtain ⟨tail⟩ := ihF substitutions fits (by simpa only [VExpr.getAppFnArgs_app] using head)
      requests frame.certificate frame.resources
    exact ⟨.application frame tail⟩
  | base _ ih => exact ih substitutions fits head requests certificate resources
  | defeq hu conversion leftType rightType term ihL ihR ih =>
    obtain ⟨transfer⟩ := certificate.transfer_graded henv hscoped hTarget closed
      ((earlier conversion).joint.symm target locals σ σ available closed hTarget substitutions fits).1 resources
    obtain ⟨tail⟩ := ih substitutions fits head requests transfer.certificate transfer.available
    exact ⟨.conversion (earlier conversion) certificate transfer tail⟩
  | bvar | sort' | elim | proj | lam | forallE =>
    simp only [VExpr.getAppFnArgs] at head
    contradiction

inductive FamilyCodePath (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation) :
    List VExpr → {n : Nat} → Profile n → {N : Nat} → Profile N → Type where
  | nil : FamilyCodePath env U registry target locals σ available [] profile profile
  | snoc
      (frame : FamilyApplicationInput env U registry target locals σ available A B a result before request)
      (prior : FamilyCodePath env U registry target locals σ available arguments frame.profile root) :
      FamilyCodePath env U registry target locals σ available (arguments ++ [a]) result root

noncomputable def FamilyCodePath.keys
    (path : FamilyCodePath env U registry target locals σ available arguments profile root) :
    List FamilyKey := by
  induction path with
  | nil => exact []
  | snoc frame prior keys => exact keys ++ [⟨frame.rank, frame.key, frame.support⟩]

/-- Each Pi application consumes one finite grade. Extra source cuts can
increase that grade, but the produced whole-header grade bounds every key. -/
theorem FamilyCodePath.gradeBound
    {profile : Profile n} {root : Profile N}
    (path : FamilyCodePath env U registry target locals σ available arguments profile root) :
    n + arguments.length ≤ N := by
  induction path with
  | nil => simp
  | snoc frame prior ih =>
    have bound := frame.outputBound
    simp only [List.length_append, List.length_singleton]
    omega

theorem FamilyCodePath.keyBound
    {profile : Profile n} {root : Profile N}
    (path : FamilyCodePath env U registry target locals σ available arguments profile root)
    (member : key ∈ path.keys) : key.rank < N := by
  induction path with
  | nil => cases member
  | snoc frame prior ih =>
    rcases List.mem_append.mp member with earlier | current
    · exact ih earlier
    · cases List.mem_singleton.mp current
      have bound := prior.gradeBound
      change frame.rank < _
      omega

structure FamilyCodeRoot (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr) (profile : Profile n) where
  info : VConstant
  lookup : sourceEnv.constants name = some info
  rank : Nat
  support : Profile rank
  footprint : Footprint
  certificate : CodeCert env U registry target locals σ (info.type.instL levels) support footprint
  resources : footprint.Available available
  path : FamilyCodePath env U registry target locals σ available arguments profile support

noncomputable def FamilySpineCertificate.codeRoot
    (spine : FamilySpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) :
    FamilyCodeRoot sourceEnv env U registry target locals σ available name levels
      expression.getAppFnArgs.2 profile := by
  induction spine with
  | constant lookup formation certificate resources =>
    exact ⟨_, lookup, _, _, _, certificate, resources, .nil⟩
  | application frame function ih =>
    exact ⟨ih.info, ih.lookup, ih.rank, ih.support, ih.footprint, ih.certificate,
      ih.resources, by simpa only [getAppFnArgs_app] using FamilyCodePath.snoc frame ih.path⟩
  | conversion edge certificate transfer term ih => exact ih

end Lean4Lean.AnchoredSource.Adapted
