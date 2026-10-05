import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalSeededSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalPiReanchor
import Lean4Lean.Theory.Typing.AnchoredFamilySeededProducer

/-! Forward declaration replay follows the actual earlier closed header.
Each row keeps its original domain location and the complete fixed request;
source arguments are never assumed typed at the declaration's domains. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive OriginalFamilyRowHistory
    (header : OriginalFamilyHeader headerEnv U declaredType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) :
    List VExpr → List Nat → Subst → Valuation → VExpr →
      List VExpr → List FamilyKey → Type where
  | nil : OriginalFamilyRowHistory header env registry target [] [] (nativeCaptureSubst [])
      (fun _ => []) declaredType [] []
  | snoc
      (history : OriginalFamilyRowHistory header env registry target
        source locals seed available (.forallE A B) domains keys)
      (original : EndpointRef headerEnv U source A (.sort level))
      (location : Located header.reference (.ref original))
      (row : PiRowCertificate env U registry target locals seed available A B (key : Key n) result)
      {support : Profile n}
      (admission : RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨key, support⟩ : DataRequest (Profile n)) key.anchor key.anchor)
      (extra : List Need)
      (bounded : ∀ need ∈ extra, need.rank ≤ n)
      (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
      (inputPresent : (⟨n, key.input⟩ : Need) ∈ row.seedNeeds extra) :
      OriginalFamilyRowHistory header env registry target (A :: source) (Locals.push locals)
        (seed.cons key.anchor) (Valuation.push (row.seedNeeds extra) available) B
        (domains ++ [A]) (keys ++ [⟨n, key, support⟩])

structure OriginalFamilyDeclaredPrefix
    (header : OriginalFamilyHeader headerEnv U declaredType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (σ : Subst) (signature : ConstantTelescope declaredType)
    (arguments : List VExpr) (assigned : VExpr) (support : Profile n)
    (required : Footprint) (keys : List FamilyKey) where
  cursor : OriginalFamilyPrefix header signature arguments.length
  valuation : Valuation
  closed : valuation.AtomClosed
  substitutions : Ctx.SubstEq env U target
    (nativeCaptureSubst (arguments.map (·.subst σ)))
    (nativeCaptureSubst (arguments.map (·.subst σ)))
    (signature.domains.take arguments.length).reverse
  fitted : TailPairedFits env registry target (cursor.location.contextDerivation .nil)
    (List.range arguments.length) (nativeCaptureSubst (arguments.map (·.subst σ)))
    (nativeCaptureSubst (arguments.map (·.subst σ))) valuation
  footprint : Footprint
  certificate : CodeCert env U registry target (List.range arguments.length)
    (nativeCaptureSubst (arguments.map (·.subst σ)))
    (wrapForalls (signature.domains.drop arguments.length) signature.result) support footprint
  resources : footprint.Available valuation
  seedAvailable : required.Available valuation
  related : TypeRelated env U registry target
    ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst
      (nativeCaptureSubst (arguments.map (·.subst σ)))) (assigned.subst σ) support
  history : OriginalFamilyRowHistory header env registry target
    (signature.domains.take arguments.length).reverse (List.range arguments.length)
    (nativeCaptureSubst (arguments.map (·.subst σ))) valuation
    (wrapForalls (signature.domains.drop arguments.length) signature.result)
    (signature.domains.take arguments.length) keys

/-- The original argument anchors remain the exact terminal source seed. -/
theorem OriginalFamilyRowHistory.seed_eq
    (history : OriginalFamilyRowHistory header env registry target
      source locals seed available expression domains keys) :
    familySubst (nativeCaptureSubst []) (keys.map (·.key.anchor)) = seed := by
  induction history with
  | nil => rfl
  | snoc history original location row admission extra bounded covered inputPresent ih =>
    simp only [List.map_append, List.map_singleton, familySubst, List.foldl_append,
      List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih]

theorem OriginalFamilyDeclaredPrefix.seed_eq
    (declared : OriginalFamilyDeclaredPrefix header env registry target σ signature
      arguments assigned profile required keys) :
    familySubst (nativeCaptureSubst []) (keys.map (·.key.anchor)) =
      nativeCaptureSubst (arguments.map (·.subst σ)) := declared.history.seed_eq

/-- A selected row is accompanied by the actual domain endpoint in the
closed original header, not by a reified derived domain typing. -/
structure OriginalFamilyRowSelection
    (header : OriginalFamilyHeader headerEnv U declaredType)
    (signature : ConstantTelescope declaredType) (count : Nat)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (seed : Subst) (available : Valuation)
    (domain : VExpr) (key : Key n) (result : Profile n) where
  level : VLevel
  original : EndpointRef headerEnv U (signature.domains.take count).reverse domain (.sort level)
  location : Located header.reference (.ref original)
  row : PiRowCertificate env U registry target locals seed available domain
    (wrapForalls (signature.domains.drop (count + 1)) signature.result) key result
  next : OriginalFamilyPrefix header signature (count + 1)

private def castSource (same : source = source')
    (node : EndpointState sourceEnv U source expression assigned) :
    EndpointState sourceEnv U source' expression assigned := same ▸ node

private def locatedCastSource (same : source = source')
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) : Located root (castSource same node) := by
  cases same
  exact location

theorem OriginalFamilyPrefix.selectRow
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {declaredType : VExpr} {header : OriginalFamilyHeader headerEnv U declaredType}
    (calls : header.Fundamentals env registry)
    {signature : ConstantTelescope declaredType} {count : Nat}
    (cursor : OriginalFamilyPrefix header signature count)
    {domain : VExpr} (domainAt : signature.domains[count]? = some domain)
    {target : List VExpr} {locals : List Nat} {seed : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target seed seed (signature.domains.take count).reverse)
    (fits : TailFits headerEnv env U registry target (signature.domains.take count).reverse
      locals seed seed available)
    {profile : Profile (n+1)} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals seed
      (wrapForalls (signature.domains.drop count) signature.result) profile footprint)
    (resources : footprint.Available available)
    {protoDomain protoBody : VExpr} {support : Profile n} {rows : List (Key n × Profile n)}
    (piMember : (.pi protoDomain protoBody support rows : Atom (n+1)) ∈ profile.atoms)
    {key : Key n} {result : Profile n} (rowMember : (key, result) ∈ rows) :
    Nonempty (OriginalFamilyRowSelection header signature count env registry target
      locals seed available domain key result) := by
  have literal := signature.prefixResidual_cons domainAt
  let head := piPrefix (cursor.location.castExpression literal)
  let original := Classical.choose head.view.location.originalDomains.1
  have originalEq : head.view.domain = .ref original :=
    Classical.choose_spec head.view.location.originalDomains.1
  have domainIH : EndpointFundamental env registry
      (head.view.location.contextDerivation .nil) original := by
    have child := calls (.piDomain head.view.location)
    change StateFundamental env registry (head.view.location.contextDerivation .nil) head.view.domain at child
    simpa only [originalEq] using child
  have bodyIH : StateFundamental env registry
      (.cons (head.view.location.contextDerivation .nil) original) head.view.body :=
    calls (.piBody head.view.location)
  have code := certificate
  rw [literal] at code
  have origins := code.piOriginsOriginal henv hscoped below hTarget closed
    (head.view.location.contextDerivation .nil) original head.view.body
    substitutions fits domainIH bodyIH resources
  obtain ⟨row⟩ := origins _ piMember key result rowMember
  have contextEq := signature.prefixContext_cons domainAt
  exact ⟨{
    level := head.view.domainLevel
    original := original
    location := originalEq ▸ Located.piDomain head.view.location
    row := row
    next := ⟨_, castSource contextEq.symm head.view.body,
      locatedCastSource contextEq.symm (Located.piBody head.view.location)⟩ }⟩

theorem PiRowCertificate.pushSeedOriginal
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {seed : Subst} {available : Valuation}
    {A B : VExpr} {n : Nat} {key : Key n} {result : Profile n} {level : VLevel}
    (context : ContextDerivation headerEnv U source)
    (original : EndpointRef headerEnv U source A (.sort level))
    (domainIH : EndpointFundamental env registry context original)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target seed seed source)
    (fits : TailFits headerEnv env U registry target source locals seed seed available)
    (row : PiRowCertificate env U registry target locals seed available A B key result)
    (extra : List Need)
    (bounded : ∀ need ∈ extra, need.rank ≤ n)
    (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    Ctx.SubstEq env U target (seed.cons key.anchor) (seed.cons key.anchor) (A :: source) ∧
    Nonempty (TailPairedFits env registry target (.cons context original) (Locals.push locals)
      (seed.cons key.anchor) (seed.cons key.anchor) (Valuation.push (row.seedNeeds extra) available)) := by
  let frame := TailPairedFits.diagonal context fits
  have domainChild : GradedTransfer env U registry target locals seed seed available A A (.sort level) :=
    (domainIH target locals seed seed available closed hTarget substitutions frame).1
  obtain ⟨domain⟩ := row.domain.transfer_graded henv hscoped hTarget closed domainChild row.domainAvailable
  obtain ⟨_, anchorTyped, _, _, _, _, anchorRelated, _⟩ := row.alignment.admission henv row.anchor
  have related := Related.retag henv row.inputTyped domain.related anchorRelated
  have coverage := row.seedCoverage extra bounded covered
  exact ⟨.cons substitutions (original.sound.defeq.mono below) anchorTyped,
    ⟨frame.pushCertificates original row.domain row.domain row.domainAvailable row.domainAvailable
      row.inputTyped row.inputTyped related related (row.seedNeeds extra)
      (fun need hm => (coverage need hm).1) (fun need hm => (coverage need hm).2)⟩⟩

/-- The forward pass consumes only the concrete frozen request and its
actual seed admission. Both legacy and typed projection argument frames
provide these fields after their genuine source child has been queried. -/
structure OriginalDeclaredApplication (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (σ : Subst)
    (A B argument : VExpr) (result : Profile n) where
  rank : Nat
  bound : n ≤ rank
  key : Key rank
  support : Profile rank
  anchor : key.anchor = argument.subst σ
  admission : RankedData.RequestAdmission env U (relations env U registry rank) target
    (⟨key, support⟩ : DataRequest (Profile rank)) key.anchor key.anchor

def OriginalDeclaredApplication.profile
    (frame : OriginalDeclaredApplication env U registry target σ A B argument result) :
    Profile (frame.rank + 1) :=
  .pi (A.subst σ) (B.subst σ.lift) frame.support
    [(frame.key, raiseProfile frame.rank frame.bound result)]

def SeededApplicationCodeInput.declaredApplication
    (henv : env.Ordered)
    (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before) :
    OriginalDeclaredApplication env U registry target σ A B a result :=
  ⟨frame.collected.rank, Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound,
    frame.key, frame.support, rfl, frame.guard.familyAdmission henv⟩

private theorem mem_externalArguments {index : Nat} {need : Need} {required : Footprint} :
    (index, need) ∈ externalArguments required ↔ (index + 1, need) ∈ required := by
  induction required with
  | nil => simp [externalArguments]
  | cons entry rest ih =>
    obtain ⟨i, original⟩ := entry
    cases i <;> simp [externalArguments, ih]

private theorem lower_raised {n N : Nat} (bound : n ≤ N) (profile : Profile n) :
    lowerProfile n bound (raiseProfile N bound profile) = profile := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simp only [raiseProfile_self, lowerProfile_self]
    · have low : n ≤ N := by omega
      rw [lowerProfile_step low, raiseProfile_step low, Profile.down_pad]
      exact ih low

/-- Extend the actual declaration tail by one frozen request. The returned
finite needs also drive the caller's own source observation ledger; no
observer is synthesized or retagged by this step. -/
theorem OriginalFamilyDeclaredPrefix.advance
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {declaredType : VExpr} {header : OriginalFamilyHeader headerEnv U declaredType}
    (calls : header.Fundamentals env registry)
    {target : List VExpr} {σ : Subst} (hTarget : OnCtx target (env.IsType U))
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {A B a : VExpr} {result : Profile n}
    (frame : OriginalDeclaredApplication env U registry target σ A B a result)
    {required : Footprint} {keys : List FamilyKey}
    (previous : OriginalFamilyDeclaredPrefix header env registry target σ signature arguments
      (.forallE A B) frame.profile (externalArguments required) keys)
    (bound : arguments.length < signature.domains.length)
    (requestBound : ∀ need ∈ argumentNeeds required 0, need.rank ≤ frame.rank)
    (requestCovered : ∀ need ∈ argumentNeeds required 0,
      ∀ atom ∈ (need.atGrade frame.rank).atoms, atom ∈ frame.key.input.atoms) :
    ∃ next : OriginalFamilyDeclaredPrefix header env registry target σ signature (arguments ++ [a])
        (B.inst a) result required (keys ++ [⟨frame.rank, frame.key, frame.support⟩]),
      ∃ needs : List Need,
        next.valuation = Valuation.push needs previous.valuation ∧
        (∀ need ∈ needs, need.rank ≤ frame.rank) ∧
        (∀ need ∈ needs, ∀ atom ∈ (need.atGrade frame.rank).atoms, atom ∈ frame.key.input.atoms) := by
  have origin : signature.domains[arguments.length]? = some signature.domains[arguments.length] :=
    List.getElem?_eq_getElem bound
  have literal := signature.prefixResidual_cons origin
  obtain ⟨selected⟩ := previous.cursor.selectRow henv hscoped below calls origin
    previous.closed hTarget previous.substitutions previous.fitted.forward previous.certificate
    previous.resources (List.mem_singleton_self _) (List.mem_singleton_self _)
  let row := selected.row
  let extra : List Need := argumentNeeds required 0 ++ [⟨frame.rank, frame.key.input⟩]
  have extraBound : ∀ need ∈ extra, need.rank ≤ frame.rank := by
    intro need member
    rcases List.mem_append.mp member with member | member
    · exact requestBound need member
    · cases List.mem_singleton.mp member; exact Nat.le_refl _
  have extraCovered : ∀ need ∈ extra,
      ∀ atom ∈ (need.atGrade frame.rank).atoms, atom ∈ frame.key.input.atoms := by
    intro need member
    rcases List.mem_append.mp member with member | member
    · exact requestCovered need member
    · cases List.mem_singleton.mp member
      simpa only [Need.atGrade, dif_pos (Nat.le_refl _), raiseProfile_self] using
        (fun atom (member : atom ∈ frame.key.input.atoms) => member)
  have inputPresent : (⟨frame.rank, frame.key.input⟩ : Need) ∈ row.seedNeeds extra :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
  obtain ⟨raw, ⟨localFits⟩⟩ := row.pushSeedOriginal henv hscoped below
    (selected.location.contextDerivation .nil) selected.original (calls selected.location)
    previous.closed hTarget previous.substitutions previous.fitted.forward extra extraBound extraCovered
  have contextEq := signature.prefixContext_cons origin
  have localsEq : List.range (arguments ++ [a]).length = Locals.push (List.range arguments.length) := by
    simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
  have lengthEq : (arguments ++ [a]).length = arguments.length + 1 := by simp
  have realized : nativeCaptureSubst ((arguments ++ [a]).map (·.subst σ)) =
      (nativeCaptureSubst (arguments.map (·.subst σ))).cons frame.key.anchor := by
    rw [List.map_append, List.map_singleton, nativeCaptureSubst_append, frame.anchor]
  let cursor : OriginalFamilyPrefix header signature (arguments ++ [a]).length := by
    rw [lengthEq]
    exact selected.next
  let desired := cursor.location.contextDerivation .nil
  have tail : TailFits headerEnv env U registry target
      (signature.domains.take (arguments ++ [a]).length).reverse (List.range (arguments ++ [a]).length)
      (nativeCaptureSubst ((arguments ++ [a]).map (·.subst σ)))
      (nativeCaptureSubst ((arguments ++ [a]).map (·.subst σ)))
      (Valuation.push (row.seedNeeds extra) previous.valuation) := by
    simpa only [lengthEq, contextEq, localsEq, realized, List.range_succ_eq_map, Locals.push] using
      localFits.forward
  have pair := previous.related
  rw [literal] at pair
  change TypeRelated env U registry target
    (.forallE ((signature.domains[arguments.length]).subst
        (nativeCaptureSubst (arguments.map (·.subst σ))))
      ((wrapForalls (signature.domains.drop (arguments.length + 1)) signature.result).subst
        (nativeCaptureSubst (arguments.map (·.subst σ))).lift))
    (.forallE (A.subst σ) (B.subst σ.lift)) frame.profile at pair
  have bodies := pair.literalPiBody_pair henv hscoped hTarget
    (List.mem_singleton_self _) frame.admission.toAdmission
  have lowered := TypeRelated.lower henv frame.bound bodies.2
  rw [lower_raised] at lowered
  let next : OriginalFamilyDeclaredPrefix header env registry target σ signature (arguments ++ [a])
      (B.inst a) result required (keys ++ [⟨frame.rank, frame.key, frame.support⟩]) := {
    cursor := cursor
    valuation := Valuation.push (row.seedNeeds extra) previous.valuation
    closed := row.seedClosed _ previous.closed
    substitutions := by simpa only [lengthEq, contextEq, realized] using raw
    fitted := TailPairedFits.diagonal desired tail
    footprint := row.bodyFootprint
    certificate := by
      simpa only [lengthEq, realized, localsEq, List.range_succ_eq_map, Locals.push] using
        row.body.lowerRaised frame.bound
    resources := row.seedBodyAvailable _
    seedAvailable := by
      intro index need member
      cases index with
      | zero => exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_append_left _ (mem_argumentNeeds.mpr member)))
      | succ index => exact previous.seedAvailable index need (mem_externalArguments.mpr member)
    related := by
      simpa only [lengthEq, realized, inst_lift_cons, subst_inst, frame.anchor] using lowered
    history := by
      have taken : signature.domains.take (arguments.length + 1) =
          signature.domains.take arguments.length ++ [signature.domains[arguments.length]] := by
        rw [List.take_add_one, origin]
        rfl
      have history := previous.history
      rw [literal] at history
      simpa only [lengthEq, contextEq, realized, localsEq, taken,
        List.range_succ_eq_map, Locals.push, List.reverse_append, List.reverse_singleton,
        List.singleton_append] using
        OriginalFamilyRowHistory.snoc history selected.original selected.location row frame.admission
          extra extraBound extraCovered inputPresent }
  exact ⟨next, row.seedNeeds extra, rfl,
    fun need member => (row.seedCoverage extra extraBound extraCovered need member).1,
    fun need member => (row.seedCoverage extra extraBound extraCovered need member).2⟩

noncomputable def OriginalEndpointFactor.OriginalSeededSpine.familyKeys
    (spine : OriginalSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) : List FamilyKey := by
  induction spine with
  | constant => exact []
  | application frame function keys => exact keys ++ [⟨frame.collected.rank, frame.key, frame.support⟩]
  | conversion plan certificate transfer term keys => exact keys

/-- The complete forward pass consumes the backward producer's concrete
frames. Its only original semantic calls are locations in the earlier
closed declaration header, with reconstructed exact source tails. -/
theorem OriginalEndpointFactor.OriginalSeededSpine.familyDeclared
    {sourceEnv headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {expected : VConstant}
    (lookup : sourceEnv.constants name = some expected)
    (signature : ConstantTelescope (expected.type.instL levels))
    (typeClosed : (expected.type.instL levels).Closed)
    (header : OriginalFamilyHeader headerEnv U (expected.type.instL levels))
    (calls : header.Fundamentals env registry)
    {expression assigned : VExpr} {profile : Profile n} {footprint required : Footprint}
    (spine : OriginalSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint)
    (coverage : NativeSpineSeedCoverage spine.seeds required)
    (bound : expression.getAppFnArgs.2.length ≤ signature.domains.length) :
    ∃ declared : OriginalFamilyDeclaredPrefix header env registry target σ signature
        expression.getAppFnArgs.2 assigned profile required spine.familyKeys,
      NativeObservedValuation env U registry target locals σ available
        expression.getAppFnArgs.2 declared.valuation := by
  induction spine generalizing required with
  | @constant assigned n profile footprint replay =>
    cases coverage
    have typeEq : replay.info.type.instL levels = expected.type.instL levels := congrArg
      (fun info : VConstant => info.type.instL levels)
      (Option.some.inj (replay.lookup.symm.trans lookup))
    have empty : replay.transfer.footprint = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      rintro ⟨index, need⟩ member
      have scope : (replay.info.type.instL levels).Closed := by rw [typeEq]; exact typeClosed
      have impossible := replay.transfer.certificate.scoped scope index need member
      omega
    have code : CodeCert env U registry target locals σ (expected.type.instL levels) profile [] := by
      rw [← typeEq, ← empty]
      exact replay.transfer.certificate
    have actual := code.closedSource typeClosed [] (nativeCaptureSubst [])
    have pair := replay.transfer.related.symm henv code.formed.wf_value
    rw [typeEq, typeClosed.subst_eq Subst.Fixes.zero] at pair
    let cursor := OriginalFamilyPrefix.initial header signature
    let declared : OriginalFamilyDeclaredPrefix header env registry target σ signature
        [] assigned profile [] [] := {
      cursor := cursor
      valuation := fun _ => []
      closed := by intro _ _ member; cases member
      substitutions := .nil
      fitted := TailPairedFits.diagonal (cursor.location.contextDerivation .nil) .nil
      footprint := []
      certificate := by simpa only [List.length_nil, List.drop_zero, List.range_zero,
        List.map_nil, ← signature.type_eq] using actual
      resources := fun _ _ member => nomatch member
      seedAvailable := fun _ _ member => nomatch member
      related := by simpa only [List.length_nil, List.drop_zero, ← signature.type_eq,
        typeClosed.subst_eq Subst.Fixes.zero] using pair
      history := by simpa only [List.length_nil, List.take_zero, List.reverse_nil,
        List.range_zero, List.map_nil, List.drop_zero, signature.type_eq] using
        (OriginalFamilyRowHistory.nil (header := header) (env := env) (registry := registry)
          (target := target)) }
    exact ⟨declared, NativeObservedValuation.empty⟩
  | @application A B a n result before f frame function ih =>
    cases coverage with
    | app previousCoverage seedBound seedCovered =>
      have beforeBound : f.getAppFnArgs.2.length < signature.domains.length := by
        simp only [getAppFnArgs_app, List.length_append, List.length_singleton] at bound
        omega
      obtain ⟨previous, observed⟩ := ih previousCoverage (by omega)
      have raisedSeed := Nat.le_trans (Nat.le_max_right n frame.seed.rank) frame.collected.bound
      have requestBound : ∀ need ∈ argumentNeeds required 0, need.rank ≤ frame.collected.rank := by
        intro need member
        exact Nat.le_trans (seedBound need (mem_argumentNeeds.mp member)) raisedSeed
      have requestCovered : ∀ need ∈ argumentNeeds required 0,
          ∀ atom ∈ (need.atGrade frame.collected.rank).atoms, atom ∈ frame.key.input.atoms := by
        intro need member atom ha
        rw [need.atGrade_raise raisedSeed (seedBound need (mem_argumentNeeds.mp member))] at ha
        exact frame.seedCovered atom (raiseProfile_subset raisedSeed
          (seedCovered need (mem_argumentNeeds.mp member)) atom ha)
      obtain ⟨next, needs, same, bounded, covered⟩ := previous.advance henv hscoped below calls
        hTarget (frame.declaredApplication henv) beforeBound requestBound requestCovered
      have observedNext : NativeObservedValuation env U registry target locals σ available
          (f.getAppFnArgs.2 ++ [a]) next.valuation := by
        rw [same]
        exact observed.push closed frame.argumentObservation frame.argumentResources bounded covered
      have done : ∃ declared : OriginalFamilyDeclaredPrefix header env registry target σ signature
          (f.getAppFnArgs.2 ++ [a]) (B.inst a) result required
          (function.familyKeys ++ [⟨frame.collected.rank, frame.key, frame.support⟩]),
          NativeObservedValuation env U registry target locals σ available
            (f.getAppFnArgs.2 ++ [a]) declared.valuation := ⟨next, observedNext⟩
      change ∃ declared : OriginalFamilyDeclaredPrefix header env registry target σ signature
          (f.app a).getAppFnArgs.2 (B.inst a) result required
          (function.familyKeys ++ [⟨frame.collected.rank, frame.key, frame.support⟩]),
          NativeObservedValuation env U registry target locals σ available
            (f.app a).getAppFnArgs.2 declared.valuation
      rw [show (f.app a).getAppFnArgs.2 = f.getAppFnArgs.2 ++ [a] from by simp]
      exact done
  | conversion plan certificate transfer term ih =>
    obtain ⟨previous, observed⟩ := ih coverage bound
    exact ⟨{ previous with related := (previous.related.trans henv
      (transfer.related.symm henv certificate.formed.wf_value)) }, observed⟩

end Lean4Lean.AnchoredSource.Adapted
