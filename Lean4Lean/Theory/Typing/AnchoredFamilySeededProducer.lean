import Lean4Lean.Theory.Typing.AnchoredFamilyDeclaredRows

/-! Seeded declared family rows preserve both actual requested field footprints
and the binary code from the declared residual to the original assigned type.
Every conversion edge comes from the original Strong source derivation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

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

noncomputable def NativeSeededSpineCertificate.familyKeys
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) : List FamilyKey := by
  induction spine with
  | constant => exact []
  | application frame function keys => exact keys ++ [⟨frame.collected.rank, frame.key, frame.support⟩]
  | conversion edge certificate transfer term keys => exact keys

structure FamilySeededDeclaredPrefix (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ : Subst) (available : Valuation) (signature : ConstantTelescope declaredType)
    (arguments : List VExpr) (assigned : VExpr) (support : Profile n)
    (required : Footprint) (keys : List FamilyKey)
    extends ConstantCodePrefix env U registry target locals σ available signature arguments support where
  seedAvailable : required.Available valuation
  related : TypeRelated env U registry target
    ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst
      (nativeCaptureSubst (arguments.map (·.subst σ)))) (assigned.subst σ) support
  history : FamilyRowHistory sourceEnv env U registry target [] [] (nativeCaptureSubst [])
    (fun _ => []) declaredType (signature.domains.take arguments.length).reverse
    (List.range arguments.length) (nativeCaptureSubst (arguments.map (·.subst σ))) valuation
    (wrapForalls (signature.domains.drop arguments.length) signature.result)
    (signature.domains.take arguments.length) keys

theorem NativeSeededSpineCertificate.familyDeclared
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {expected : VConstant}
    (lookupDeclared : sourceEnv.constants name = some expected)
    (signature : ConstantTelescope (expected.type.instL levels))
    (typeClosed : (expected.type.instL levels).Closed)
    (formation : OriginalTypePayload sourceEnv env U registry [] (expected.type.instL levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) [] (expected.type.instL levels))
    {expression assigned : VExpr} {profile : Profile n} {footprint required : Footprint}
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint)
    (coverage : NativeSpineSeedCoverage spine.seeds required)
    (bound : expression.getAppFnArgs.2.length ≤ signature.domains.length) :
    Nonempty (FamilySeededDeclaredPrefix sourceEnv env U registry target locals σ available signature
      expression.getAppFnArgs.2 assigned profile required spine.familyKeys) := by
  induction spine generalizing required with
  | @constant n profile footprint info lookup originalFormation certificate resources =>
    cases coverage
    have typeEq : info.type.instL levels = expected.type.instL levels := congrArg
      (fun info : VConstant => info.type.instL levels) (Option.some.inj (lookup.symm.trans lookupDeclared))
    have empty : footprint = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      rintro ⟨index, need⟩ member
      have scope : (info.type.instL levels).Closed := by rw [typeEq]; exact typeClosed
      have impossible := certificate.scoped scope index need member
      omega
    subst footprint
    have actual : CodeCert env U registry target [] (nativeCaptureSubst [])
        (expected.type.instL levels) profile [] := by
      rw [typeEq] at certificate
      exact certificate.closedSource typeClosed [] (nativeCaptureSubst [])
    have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ h; cases h
    obtain ⟨interpreted⟩ := actual.transfer_graded henv hscoped hTarget emptyClosed
      (formation.2 target [] (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => [])
        emptyClosed hTarget .nil .nil).1 (fun _ _ h => nomatch h)
    refine ⟨{
      valuation := fun _ => []
      closed := emptyClosed
      substitutions := .nil
      fits := .nil
      footprint := []
      certificate := ?_
      resources := fun _ _ h => nomatch h
      observed := NativeObservedValuation.empty
      seedAvailable := fun _ _ h => nomatch h
      related := ?_
      history := ?_ }⟩
    · simpa only [getAppFnArgs_const, List.length_nil, List.drop_zero, List.range_zero,
        List.map_nil, ← signature.type_eq] using actual
    · simpa only [getAppFnArgs_const, List.length_nil, List.drop_zero,
        ← signature.type_eq, typeEq, typeClosed.subst_eq Subst.Fixes.zero] using interpreted.related
    · simpa only [getAppFnArgs_const, List.length_nil, List.take_zero, List.reverse_nil,
        List.range_zero, List.map_nil, List.drop_zero, signature.type_eq,
        NativeSeededSpineCertificate.familyKeys] using
        (FamilyRowHistory.nil (sourceEnv := sourceEnv) (env := env) (U := U) (registry := registry)
          (target := target) (source₀ := []) (locals₀ := []) (seed₀ := nativeCaptureSubst [])
          (available₀ := fun _ => []) (expression₀ := expected.type.instL levels))
  | @application A B a n result before f frame function ih =>
    cases coverage with
    | app previousCoverage seedBound seedCovered =>
      have beforeBound : f.getAppFnArgs.2.length < signature.domains.length := by
        simp only [getAppFnArgs_app, List.length_append, List.length_singleton] at bound
        omega
      obtain ⟨previous⟩ := ih previousCoverage (by omega)
      let args := f.getAppFnArgs.2
      have origin : signature.domains[args.length]? = some signature.domains[args.length] :=
        List.getElem?_eq_getElem beforeBound
      have literal := signature.prefixResidual_cons origin
      have tree := (signature.prefixPayload ⟨level, formation⟩ header args.length).1.2
      have certificate := previous.certificate
      have history := previous.history
      rw [literal] at tree certificate history
      obtain ⟨domainLevel, rawDomain, originalDomain⟩ := tree.domain.1
      obtain ⟨bodyLevel, rawBody, originalBody⟩ := tree.codomain.1
      have origins := certificate.piOrigins henv hscoped hTarget previous.closed
        (rawDomain.defeq.mono hle) (rawBody.defeq.mono hle) previous.substitutions previous.fits
        originalDomain originalBody previous.resources
      have resultBound := Nat.le_trans (Nat.le_max_left n frame.seed.rank) frame.collected.bound
      have raisedSeed := Nat.le_trans (Nat.le_max_right n frame.seed.rank) frame.collected.bound
      obtain ⟨row⟩ := origins _ (List.mem_singleton_self _) frame.key
        (raiseProfile frame.collected.rank resultBound result) (List.mem_singleton_self _)
      have requestBound : ∀ need ∈ argumentNeeds required 0, need.rank ≤ frame.collected.rank := by
        intro need member
        exact Nat.le_trans (seedBound need (mem_argumentNeeds.mp member)) raisedSeed
      have requestCovered : ∀ need ∈ argumentNeeds required 0,
          ∀ atom ∈ (need.atGrade frame.collected.rank).atoms, atom ∈ frame.key.input.atoms := by
        intro need member atom ha
        rw [need.atGrade_raise raisedSeed (seedBound need (mem_argumentNeeds.mp member))] at ha
        exact frame.seedCovered atom (raiseProfile_subset raisedSeed
          (seedCovered need (mem_argumentNeeds.mp member)) atom ha)
      let extra : List Need := argumentNeeds required 0 ++ [⟨frame.collected.rank, frame.key.input⟩]
      have extraBound : ∀ need ∈ extra, need.rank ≤ frame.collected.rank := by
        intro need member
        rcases List.mem_append.mp member with member | member
        · exact requestBound need member
        · cases List.mem_singleton.mp member; exact Nat.le_refl _
      have extraCovered : ∀ need ∈ extra,
          ∀ atom ∈ (need.atGrade frame.collected.rank).atoms, atom ∈ frame.key.input.atoms := by
        intro need member
        rcases List.mem_append.mp member with member | member
        · exact requestCovered need member
        · cases List.mem_singleton.mp member
          simpa only [Need.atGrade, dif_pos (Nat.le_refl _), raiseProfile_self] using
            (fun atom (member : atom ∈ frame.key.input.atoms) => member)
      have inputPresent : (⟨frame.collected.rank, frame.key.input⟩ : Need) ∈ row.seedNeeds extra :=
        List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)))
      obtain ⟨raw, localFits⟩ := row.pushSeed henv hscoped hle ⟨rawDomain, originalDomain⟩
        previous.closed hTarget previous.substitutions previous.fits
        extra extraBound extraCovered
      have keyCoverage := row.seedCoverage extra extraBound extraCovered
      have localObserved := previous.observed.push closed frame.argumentObservation frame.argumentResources
        (fun need member => (keyCoverage need member).1) (fun need member => (keyCoverage need member).2)
      have contextEq := signature.prefixContext_cons origin
      have localsEq : List.range (args ++ [a]).length = Locals.push (List.range args.length) := by
        simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
      have lengthEq : (args ++ [a]).length = args.length + 1 := by simp
      have realized : nativeCaptureSubst ((args ++ [a]).map (·.subst σ)) =
          (nativeCaptureSubst (args.map (·.subst σ))).cons frame.key.anchor := by
        rw [List.map_append, List.map_singleton, nativeCaptureSubst_append]
        rfl
      have pair := previous.related
      rw [literal] at pair
      change TypeRelated env U registry target
        (.forallE ((signature.domains[args.length]).subst (nativeCaptureSubst (args.map (·.subst σ))))
          ((wrapForalls (signature.domains.drop (args.length + 1)) signature.result).subst
            (nativeCaptureSubst (args.map (·.subst σ))).lift))
        (.forallE (A.subst σ) (B.subst σ.lift)) frame.profile at pair
      have bodies := pair.literalPiBody_pair henv hscoped hTarget
        (List.mem_singleton_self _) frame.guard.anchor
      have lowered := TypeRelated.lower henv resultBound bodies.2
      rw [lower_raised] at lowered
      simp only [getAppFnArgs_app]
      change Nonempty (FamilySeededDeclaredPrefix sourceEnv env U registry target locals σ available
        signature (args ++ [a]) (B.inst a) result required _)
      refine ⟨{
        valuation := Valuation.push (row.seedNeeds extra) previous.valuation
        closed := row.seedClosed _ previous.closed
        substitutions := ?_
        fits := ?_
        footprint := row.bodyFootprint
        certificate := ?_
        resources := row.seedBodyAvailable _
        observed := localObserved
        seedAvailable := ?_
        related := ?_
        history := ?_ }⟩
      · simpa only [getAppFnArgs_app, lengthEq, contextEq, realized] using raw
      · simpa only [getAppFnArgs_app, lengthEq, contextEq, realized, localsEq,
          List.range_succ_eq_map, Locals.push] using localFits
      · simpa only [getAppFnArgs_app, lengthEq, realized, localsEq,
          List.range_succ_eq_map, Locals.push] using row.body.lowerRaised resultBound
      · intro index need member
        cases index with
        | zero => exact List.mem_append_left _ (List.mem_append_right _
            (List.mem_append_left _ (mem_argumentNeeds.mpr member)))
        | succ index => exact previous.seedAvailable index need (mem_externalArguments.mpr member)
      · simpa only [getAppFnArgs_app, lengthEq, realized, inst_lift_cons,
          subst_inst, SeededApplicationCodeInput.key] using lowered
      · have taken : signature.domains.take (args.length + 1) =
            signature.domains.take args.length ++ [signature.domains[args.length]] := by
          rw [List.take_add_one, origin]
          rfl
        simpa only [getAppFnArgs_app, lengthEq, contextEq, realized, localsEq, taken,
          NativeSeededSpineCertificate.familyKeys, List.range_succ_eq_map, Locals.push,
          List.reverse_append, List.reverse_singleton, List.singleton_append] using
          FamilyRowHistory.snoc history ⟨rawDomain, originalDomain⟩ row (frame.guard.familyAdmission henv)
            extra extraBound extraCovered inputPresent
  | conversion edge certificate transfer term ih =>
    obtain ⟨previous⟩ := ih coverage bound
    exact ⟨{ previous with related := (previous.related.trans henv
      (transfer.related.symm henv certificate.formed.wf_value)) }⟩



/-- Close a saturated family header with its actual requested footprint.
The exact final ledger and local names remain available to attach retained
constructor-field certificates to the binary alignment consumer. -/
theorem FamilySeededDeclaredPrefix.rows
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    (declared : FamilySeededDeclaredPrefix sourceEnv env U registry target locals σ available
      signature arguments assigned profile required keys)
    (saturated : arguments.length = signature.domains.length)
    (resultSort : signature.result = .sort resultLevel) :
    ∃ rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
        (nativeCaptureSubst []) (fun _ => []) declaredType signature.domains keys,
      rows.terminalLocals = List.range arguments.length ∧
      rows.terminalValuation = declared.valuation := by
  have history := declared.history
  simp only [saturated, List.take_length, List.drop_length, wrapForalls, resultSort] at history
  have result := history.closeExact (FamilySeededCodeRows.nil declared.seedAvailable)
  rw [List.append_nil, List.append_nil] at result
  simpa only [FamilySeededCodeRows.terminalLocals, FamilySeededCodeRows.terminalValuation,
    saturated] using result

/-- A saturated declaration prefix retains the same exact final ledger even
when its result is a family expression rather than a sort. -/
theorem FamilySeededDeclaredPrefix.anyRows
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    (declared : FamilySeededDeclaredPrefix sourceEnv env U registry target locals σ available
      signature arguments assigned profile required keys)
    (saturated : arguments.length = signature.domains.length) :
    ∃ rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
        (nativeCaptureSubst []) (fun _ => []) declaredType signature.domains keys,
      rows.terminalLocals = List.range arguments.length ∧
      rows.terminalValuation = declared.valuation := by
  have history := declared.history
  simp only [saturated, List.take_length, List.drop_length, wrapForalls] at history
  have result := history.closeExact (FamilySeededCodeRows.nil declared.seedAvailable)
  rw [List.append_nil, List.append_nil] at result
  simpa only [FamilySeededCodeRows.terminalLocals, FamilySeededCodeRows.terminalValuation,
    saturated] using result

theorem FamilySeededDeclaredPrefix.seed_eq
    (declared : FamilySeededDeclaredPrefix sourceEnv env U registry target locals σ available
      signature arguments assigned profile required keys) :
    familySubst (nativeCaptureSubst []) (keys.map (·.key.anchor)) =
      nativeCaptureSubst (arguments.map (·.subst σ)) :=
  declared.history.seed_eq

/-- The end-to-end producer uses actual finite source argument-ledger
packets. Their exact requested footprint is available after declared-row
recovery, and every original conversion remains in the binary residual code. -/
theorem HasTypeStrong.seededFamilyDeclared
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {name : Name} {levels : List VLevel} {info : VConstant}
    (lookup : sourceEnv.constants name = some info)
    (signature : ConstantTelescope (info.type.instL levels))
    (formation : sourceEnv.IsDefEqStrong U [] (info.type.instL levels)
      (info.type.instL levels) (.sort level))
    {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    {profile : Profile n} {footprint required : Footprint}
    (ledger : NativeArgumentLedger env U registry target locals σ available expression.getAppFnArgs.2 required)
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available)
    (bound : expression.getAppFnArgs.2.length ≤ signature.domains.length) :
    ∃ rank keys, (∀ key ∈ keys, key.rank < rank) ∧
      Nonempty (FamilySeededDeclaredPrefix sourceEnv env U registry target locals σ available
        signature expression.getAppFnArgs.2 assigned profile required keys) := by
  obtain ⟨seeds, coverage⟩ := ledger.spineSeeds head n
  obtain ⟨spine, same⟩ := HasTypeStrong.seededSpineCertificate henv hscoped hle earlier
    closed hTarget substitutions fits original head seeds certificate resources
  have payload := earlier formation
  refine ⟨FamilyKey.bound spine.familyKeys, spine.familyKeys,
    fun _ member => FamilyKey.lt_bound member, ?_⟩
  apply spine.familyDeclared henv hscoped hle closed hTarget lookup signature
    (formation.defeq.closedN hsource trivial) ⟨formation, payload.joint⟩ payload.leftFormation _ bound
  rw [same]
  exact coverage

end Lean4Lean.AnchoredSource.Adapted
