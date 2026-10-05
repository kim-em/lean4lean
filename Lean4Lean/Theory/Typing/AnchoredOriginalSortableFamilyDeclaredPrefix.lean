import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFamilyRows
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyDeclaredPrefix

/-! The rich forward declaration pass selects concrete original Pi rows
and keeps every fixed request input available at the terminal. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive OriginalSortableFamilyRowHistory
    (header : OriginalFamilyHeader headerEnv U declaredType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) :
    List VExpr → List Nat → Subst → Valuation → VExpr →
      List VExpr → List FamilyKey → Type where
  | nil : OriginalSortableFamilyRowHistory header env registry target [] [] (nativeCaptureSubst [])
      (fun _ => []) declaredType [] []
  | snoc
      (history : OriginalSortableFamilyRowHistory header env registry target
        source locals seed available (.forallE A B) domains keys)
      (original : EndpointRef headerEnv U source A (.sort level))
      (location : Located header.reference (.ref original))
      (row : SortablePiRowCertificate env U registry target locals seed available true A B (key : Key n) result)
      {support : Profile n}
      (admission : RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨key, support⟩ : DataRequest (Profile n)) key.anchor key.anchor)
      (extra : List Need)
      (bounded : ∀ need ∈ extra, need.rank ≤ n)
      (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
      (inputPresent : (⟨n, key.input⟩ : Need) ∈ row.seedNeeds extra) :
      OriginalSortableFamilyRowHistory header env registry target (A :: source) (Locals.push locals)
        (seed.cons key.anchor) (Valuation.push (row.seedNeeds extra) available) B
        (domains ++ [A]) (keys ++ [⟨n, key, support⟩])

structure OriginalSortableFamilyDeclaredPrefix
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
  fitted : SortableTailPairedFits env registry target (cursor.location.contextDerivation .nil)
    (List.range arguments.length) (nativeCaptureSubst (arguments.map (·.subst σ)))
    (nativeCaptureSubst (arguments.map (·.subst σ))) valuation
  footprint : Footprint
  certificate : SortableCert env U registry target (List.range arguments.length)
    (nativeCaptureSubst (arguments.map (·.subst σ)))
    (wrapForalls (signature.domains.drop arguments.length) signature.result) true support footprint
  resources : footprint.Available valuation
  seedAvailable : required.Available valuation
  related : TypeRelated env U registry target
    ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst
      (nativeCaptureSubst (arguments.map (·.subst σ)))) (assigned.subst σ) support
  history : OriginalSortableFamilyRowHistory header env registry target
    (signature.domains.take arguments.length).reverse (List.range arguments.length)
    (nativeCaptureSubst (arguments.map (·.subst σ))) valuation
    (wrapForalls (signature.domains.drop arguments.length) signature.result)
    (signature.domains.take arguments.length) keys

/-- The original argument anchors remain the exact terminal source seed. -/
theorem OriginalSortableFamilyRowHistory.seed_eq
    (history : OriginalSortableFamilyRowHistory header env registry target
      source locals seed available expression domains keys) :
    familySubst (nativeCaptureSubst []) (keys.map (·.key.anchor)) = seed := by
  induction history with
  | nil => rfl
  | snoc history original location row admission extra bounded covered inputPresent ih =>
    simp only [List.map_append, List.map_singleton, familySubst, List.foldl_append,
      List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [ih]

theorem OriginalSortableFamilyDeclaredPrefix.seed_eq
    (declared : OriginalSortableFamilyDeclaredPrefix header env registry target σ signature
      arguments assigned profile required keys) :
    familySubst (nativeCaptureSubst []) (keys.map (·.key.anchor)) =
      nativeCaptureSubst (arguments.map (·.subst σ)) := declared.history.seed_eq

/-- A selected row is accompanied by the actual domain endpoint in the
closed original header, not by a reified derived domain typing. -/
structure OriginalSortableFamilyRowSelection
    (header : OriginalFamilyHeader headerEnv U declaredType)
    (signature : ConstantTelescope declaredType) (count : Nat)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (seed : Subst) (available : Valuation)
    (domain : VExpr) (key : Key n) (result : Profile n) where
  level : VLevel
  original : EndpointRef headerEnv U (signature.domains.take count).reverse domain (.sort level)
  location : Located header.reference (.ref original)
  row : SortablePiRowCertificate env U registry target locals seed available true domain
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

theorem OriginalFamilyPrefix.selectSortableRow
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {declaredType : VExpr} {header : OriginalFamilyHeader headerEnv U declaredType}
    (calls : header.SortableFundamentals env registry)
    {signature : ConstantTelescope declaredType} {count : Nat}
    (cursor : OriginalFamilyPrefix header signature count)
    {domain : VExpr} (domainAt : signature.domains[count]? = some domain)
    {target : List VExpr} {locals : List Nat} {seed : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target seed seed (signature.domains.take count).reverse)
    (fits : SortableTailFits headerEnv env U registry target (signature.domains.take count).reverse
      locals seed seed available)
    {profile : Profile (n+1)} {footprint : Footprint}
    (certificate : SortableCert env U registry target locals seed
      (wrapForalls (signature.domains.drop count) signature.result) true profile footprint)
    (resources : footprint.Available available)
    {protoDomain protoBody : VExpr} {support : Profile n} {rows : List (Key n × Profile n)}
    (piMember : (.pi protoDomain protoBody support rows : Atom (n+1)) ∈ profile.atoms)
    {key : Key n} {result : Profile n} (rowMember : (key, result) ∈ rows) :
    Nonempty (OriginalSortableFamilyRowSelection header signature count env registry target
      locals seed available domain key result) := by
  have literal := signature.prefixResidual_cons domainAt
  let head := piPrefix (cursor.location.castExpression literal)
  let original := Classical.choose head.view.location.originalDomains.1
  have originalEq : head.view.domain = .ref original :=
    Classical.choose_spec head.view.location.originalDomains.1
  have domainIH : StateSortableFundamental env registry
      (head.view.location.contextDerivation .nil) (.ref original) := by
    have child := calls (.piDomain head.view.location)
    change StateSortableFundamental env registry (head.view.location.contextDerivation .nil) head.view.domain at child
    simpa only [originalEq] using child
  have bodyIH : StateSortableFundamental env registry
      (.cons (head.view.location.contextDerivation .nil) original) head.view.body :=
    calls (.piBody head.view.location)
  have code := certificate
  rw [literal] at code
  have origins := code.piOriginsOriginal henv hscoped below hTarget closed
    (head.view.location.contextDerivation .nil) original head.view.body
    substitutions fits domainIH bodyIH resources
  obtain ⟨row⟩ := code.piRowOfOrigins origins piMember rowMember
  have contextEq := signature.prefixContext_cons domainAt
  exact ⟨{
    level := head.view.domainLevel
    original := original
    location := originalEq ▸ Located.piDomain head.view.location
    row := row
    next := ⟨_, castSource contextEq.symm head.view.body,
      locatedCastSource contextEq.symm (Located.piBody head.view.location)⟩ }⟩

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
theorem OriginalSortableFamilyDeclaredPrefix.advance
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {declaredType : VExpr} {header : OriginalFamilyHeader headerEnv U declaredType}
    (calls : header.SortableFundamentals env registry)
    {target : List VExpr} {σ : Subst} (hTarget : OnCtx target (env.IsType U))
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {A B a : VExpr} {result : Profile n}
    (frame : OriginalDeclaredApplication env U registry target σ A B a result)
    {required : Footprint} {keys : List FamilyKey}
    (previous : OriginalSortableFamilyDeclaredPrefix header env registry target σ signature arguments
      (.forallE A B) frame.profile (externalArguments required) keys)
    (bound : arguments.length < signature.domains.length)
    (requestBound : ∀ need ∈ argumentNeeds required 0, need.rank ≤ frame.rank)
    (requestCovered : ∀ need ∈ argumentNeeds required 0,
      ∀ atom ∈ (need.atGrade frame.rank).atoms, atom ∈ frame.key.input.atoms) :
    ∃ next : OriginalSortableFamilyDeclaredPrefix header env registry target σ signature (arguments ++ [a])
        (B.inst a) result required (keys ++ [⟨frame.rank, frame.key, frame.support⟩]),
      ∃ needs : List Need,
        next.valuation = Valuation.push needs previous.valuation ∧
        (∀ need ∈ needs, need.rank ≤ frame.rank) ∧
        (∀ need ∈ needs, ∀ atom ∈ (need.atGrade frame.rank).atoms, atom ∈ frame.key.input.atoms) := by
  have origin : signature.domains[arguments.length]? = some signature.domains[arguments.length] :=
    List.getElem?_eq_getElem bound
  have literal := signature.prefixResidual_cons origin
  obtain ⟨selected⟩ := previous.cursor.selectSortableRow henv hscoped below calls origin
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
  have tail : SortableTailFits headerEnv env U registry target
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
  let next : OriginalSortableFamilyDeclaredPrefix header env registry target σ signature (arguments ++ [a])
      (B.inst a) result required (keys ++ [⟨frame.rank, frame.key, frame.support⟩]) := {
    cursor := cursor
    valuation := Valuation.push (row.seedNeeds extra) previous.valuation
    closed := row.seedClosed _ previous.closed
    substitutions := by simpa only [lengthEq, contextEq, realized] using raw
    fitted := SortableTailPairedFits.diagonal desired tail
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
        OriginalSortableFamilyRowHistory.snoc history selected.original selected.location row frame.admission
          extra extraBound extraCovered inputPresent }
  exact ⟨next, row.seedNeeds extra, rfl,
    fun need member => (row.seedCoverage extra extraBound extraCovered need member).1,
    fun need member => (row.seedCoverage extra extraBound extraCovered need member).2⟩


theorem OriginalSortableFamilyRowHistory.closeExact
    {headerEnv : VEnv} {U : Nat} {declaredType : VExpr}
    {header : OriginalFamilyHeader headerEnv U declaredType}
    (history : OriginalSortableFamilyRowHistory header env registry target source locals seed available expression domains keys)
    (tail : OriginalSortableFamilyCodeRows header env registry target required source locals seed available
      expression remaining remainingKeys) :
    ∃ rows : OriginalSortableFamilyCodeRows header env registry target required [] [] (nativeCaptureSubst []) (fun _ => []) declaredType (domains ++ remaining) (keys ++ remainingKeys),
      rows.terminalLocals = tail.terminalLocals ∧ rows.terminalValuation = tail.terminalValuation := by
  induction history generalizing remaining remainingKeys with
  | nil => exact ⟨tail, rfl, rfl⟩
  | snoc history original location row admission extra bounded covered inputPresent ih =>
    rw [List.append_assoc, List.singleton_append, List.append_assoc, List.singleton_append]
    exact ih (OriginalSortableFamilyCodeRows.cons original location row admission extra bounded covered inputPresent tail)

theorem OriginalSortableFamilyDeclaredPrefix.anyRows
    {headerEnv : VEnv} {U : Nat} {declaredType : VExpr}
    {header : OriginalFamilyHeader headerEnv U declaredType} {signature : ConstantTelescope declaredType}
    (declared : OriginalSortableFamilyDeclaredPrefix header env registry target σ
      signature arguments assigned profile required keys)
    (saturated : arguments.length = signature.domains.length) :
    ∃ rows : OriginalSortableFamilyCodeRows header env registry target required [] []
        (nativeCaptureSubst []) (fun _ => []) declaredType signature.domains keys,
      rows.terminalLocals = List.range arguments.length ∧
      rows.terminalValuation = declared.valuation := by
  have history := declared.history
  simp only [saturated, List.take_length, List.drop_length, wrapForalls] at history
  have result := history.closeExact (OriginalSortableFamilyCodeRows.nil declared.seedAvailable)
  rw [List.append_nil, List.append_nil] at result
  simpa only [OriginalSortableFamilyCodeRows.terminalLocals, OriginalSortableFamilyCodeRows.terminalValuation,
    saturated] using result

end Lean4Lean.AnchoredSource.Adapted
