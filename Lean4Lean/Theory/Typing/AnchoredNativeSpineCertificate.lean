import Lean4Lean.Theory.Typing.AnchoredNativeConvertedSpine
import Lean4Lean.Theory.Typing.AnchoredNativeTypeCertificate

/-! Backward finite certificate construction along an ORIGINAL constant
application spine. Each application collects its actual argument cuts before
choosing its input grade. Conversion nodes reuse their original child theorem;
no casted argument is interpreted by a new adequacy call. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure ApplicationCodeInput (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B a : VExpr) (result : Profile n) (before : Footprint) where
  residual : CodeCert env U registry target locals σ (B.inst a) result before
  required : Footprint
  cuts : InstFootprint env U registry target locals σ a 0 before required
  input : FactoredArguments env U registry target locals σ available a required n
  support : Profile input.rank
  domainFootprint : Footprint
  domain : CodeCert env U registry target locals σ A support domainFootprint
  domainAvailable : domainFootprint.Available available
  guard : LambdaGuard env U registry target σ A ⟨A.subst σ, a.subst σ, input.input⟩ support
  body : CodeCert env U registry target (Locals.push locals) (σ.cons (a.subst σ)) B
    (raiseProfile input.rank input.bound result) required

namespace ApplicationCodeInput
variable (frame : ApplicationCodeInput env U registry target locals σ available A B a result before)

def key : Key frame.input.rank := ⟨A.subst σ, a.subst σ, frame.input.input⟩
def profile : Profile (frame.input.rank + 1) :=
  .pi (A.subst σ) (B.subst σ.lift) frame.support
    [(frame.key, raiseProfile frame.input.rank frame.input.bound result)]
def footprint : Footprint := frame.domainFootprint ++ frame.input.outside

def certificate : CodeCert env U registry target locals σ (.forallE A B) frame.profile frame.footprint := by
  have bodies : PiRows env U registry target locals σ A B frame.support
      [(frame.key, raiseProfile frame.input.rank frame.input.bound result)] frame.input.outside := by
    simpa only [List.append_nil, key] using PiRows.cons frame.guard frame.body frame.input.pack
      (fun _ h => h) PiRows.nil
  refine .seed (.pi frame.domain PiGuard.literal bodies) (Profile.HasType.pi_iff.mpr ⟨?_, ?_⟩)
  · refine Profile.WF.pi_iff.mpr ⟨frame.domain.formed, ?_⟩
    intro key output member
    cases List.mem_singleton.mp member
    exact ⟨frame.guard.inputTyped, frame.body.formed.wf_value⟩
  · intro key output member
    cases List.mem_singleton.mp member
    exact frame.body.formed

theorem resources : frame.footprint.Available available := by
  intro i need member
  exact (List.mem_append.mp member).elim (frame.domainAvailable i need) (frame.input.outsideAvailable i need)

end ApplicationCodeInput

private theorem one_comp (a : VExpr) (σ : Subst) :
    (Subst.one a).comp σ = σ.cons (a.subst σ) := by
  funext i; cases i <;> rfl

/-- One genuine backward application step. A larger argument grade raises the
already factored body certificate; it does not request new body observations. -/
theorem CodeCert.applicationInput
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B a : VExpr}
    (argument : OriginalTypePayload sourceEnv env U registry source a A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {result : Profile n} {before : Footprint}
    (certificate : CodeCert env U registry target locals σ (B.inst a) result before)
    (resources : before.Available available) :
    Nonempty (ApplicationCodeInput env U registry target locals σ available A B a result before) := by
  obtain ⟨required, ⟨body⟩, ⟨cuts⟩⟩ := certificate.factorInst B a 0 rfl σ rfl locals (Locals.push locals)
  simp only [Subst.liftN, one_comp] at body
  obtain ⟨packed⟩ := cuts.arguments available resources n
  obtain ⟨value⟩ := (argument.2 target locals σ σ available closed hTarget substitutions fits).1
    packed.observation packed.argumentAvailable
  have raw := (argument.1.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  have related := value.requestedRelated henv hTarget
  have domain := value.requestedCertificate
  have code := TypeRelated.lower henv value.bound value.typeCode
  exact ⟨{
    residual := certificate
    required := required
    cuts := cuts
    input := packed
    support := lowerProfile packed.rank value.bound value.support
    domainFootprint := value.typeFootprint
    domain := domain
    domainAvailable := value.typeAvailable
    guard := ⟨value.requestedTyped, domain.formed, .refl, code,
      ⟨raw, raw, _, value.requestedTyped, domain.formed, code, related, related⟩⟩
    body := body.raise packed.bound }⟩

/-- A finite backward derivation ending at the literal registered constant
type. The constructor records retain all argument cuts and every original
conversion payload; this is not a semantic oracle for a generated type. -/
inductive NativeSpineCertificate (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    (expression assigned : VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | constant {info : VConstant}
      (lookup : sourceEnv.constants name = some info)
      (formation : SourcePiFormation (OriginalTypePayload sourceEnv env U registry)
        source (info.type.instL levels))
      (certificate : CodeCert env U registry target locals σ (info.type.instL levels) profile footprint)
      (resources : footprint.Available available) :
      NativeSpineCertificate sourceEnv env U registry source target locals σ available name levels
        (.const name levels) (info.type.instL levels) profile footprint
  | application
      (frame : ApplicationCodeInput env U registry target locals σ available A B a result before)
      (function : NativeSpineCertificate sourceEnv env U registry source target locals σ available name levels
        f (.forallE A B) frame.profile frame.footprint) :
      NativeSpineCertificate sourceEnv env U registry source target locals σ available name levels
        (.app f a) (B.inst a) result before
  | conversion
      {original : sourceEnv.IsDefEqStrong U source A B (.sort level)}
      (edge : OriginalPayload sourceEnv env U registry original)
      (certificate : CodeCert env U registry target locals σ B profile footprint)
      (transfer : CodeTransferResult env U registry target locals σ σ available B A profile)
      (term : NativeSpineCertificate sourceEnv env U registry source target locals σ available name levels
        expression A profile transfer.footprint) :
      NativeSpineCertificate sourceEnv env U registry source target locals σ available name levels
        expression B profile footprint

/-- Recursive extraction is on the ORIGINAL typing tree. Each `earlier`
request is literally a formation, argument, or conversion child of that tree;
the constant node never asks for semantics of the constant itself. -/
theorem HasTypeStrong.spineCertificate
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
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (NativeSpineCertificate sourceEnv env U registry source target locals σ available name levels
      expression assigned profile footprint) := by
  induction original generalizing n footprint with
  | const lookup hw hl hu closedType type ihClosed ihType =>
    simp only [VExpr.getAppFnArgs_const] at head
    cases head
    exact ⟨.constant lookup (earlier type.refl).leftFormation certificate resources⟩
  | app hu hv domain codomain whole function argument result ihD ihC ihW ihF ihA ihR =>
    obtain ⟨frame⟩ := certificate.applicationInput henv hscoped hle
      ⟨argument.refl, (earlier argument.refl).joint⟩ closed hTarget substitutions fits resources
    obtain ⟨tail⟩ := ihF substitutions fits (by simpa only [VExpr.getAppFnArgs_app] using head)
      frame.certificate frame.resources
    exact ⟨.application frame tail⟩
  | base _ ih => exact ih substitutions fits head certificate resources
  | defeq hu conversion leftType rightType term ihL ihR ih =>
    obtain ⟨transfer⟩ := certificate.transfer_graded henv hscoped hTarget closed
      ((earlier conversion).joint.symm target locals σ σ available closed hTarget substitutions fits).1 resources
    obtain ⟨tail⟩ := ih substitutions fits head transfer.certificate transfer.available
    exact ⟨.conversion (earlier conversion) certificate transfer tail⟩
  | bvar | sort' | elim | proj | lam | forallE =>
    simp only [VExpr.getAppFnArgs] at head
    contradiction

/-- The produced whole-header certificate is actual source syntax with the
same ambient resource valuation. Application and conversion steps retain the
finite provenance above it in `NativeSpineCertificate`. -/
theorem NativeSpineCertificate.rootCode
    (spine : NativeSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) :
    ∃ info, sourceEnv.constants name = some info ∧
      SourcePiFormation (OriginalTypePayload sourceEnv env U registry) source (info.type.instL levels) ∧
      ∃ rank, ∃ support : Profile rank, ∃ required,
        Nonempty (CodeCert env U registry target locals σ (info.type.instL levels) support required) ∧
        required.Available available := by
  induction spine with
  | constant lookup formation certificate resources => exact ⟨_, lookup, formation, _, _, _, ⟨certificate⟩, resources⟩
  | application frame function ih => exact ih
  | conversion edge certificate transfer term ih => exact ih

/-- At an actual closed registered header the resulting resource ledger is
empty. Scope is a syntactic fact about that header, not a domain-alignment
assumption. The entire backward cut derivation remains in `spine`. -/
theorem NativeSpineCertificate.closedRootCode
    (spine : NativeSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint)
    {info : VConstant} (lookup : sourceEnv.constants name = some info)
    (closed : (info.type.instL levels).Closed) :
    ∃ rank, ∃ support : Profile rank,
      Nonempty (CodeCert env U registry target [] σ (info.type.instL levels) support []) := by
  obtain ⟨actual, found, formation, rank, support, required, ⟨certificate⟩, resources⟩ := spine.rootCode
  have equal : actual = info := Option.some.inj (found.symm.trans lookup)
  cases equal
  have empty : required = [] := by
    cases required with
    | nil => rfl
    | cons head tail =>
      obtain ⟨i, need⟩ := head
      have impossible := certificate.scoped closed i need List.mem_cons_self
      omega
  subst required
  exact ⟨rank, support, ⟨certificate.closedSource closed [] σ⟩⟩

end Lean4Lean.AnchoredSource.Adapted
