import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyDeclaredPrefix
import Lean4Lean.Theory.Typing.AnchoredFamilyPlanRows

/-! Close the actual earlier header rows into a bare family observation.
All semantic row calls retain original endpoint locations and exact tails. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private captureVariables_succ lookup_suffix from Lean4Lean.Theory.Typing.AnchoredFamilyCaptureObservation
set_option backward.isDefEq.respectTransparency false

inductive OriginalFamilyCodeRows (header : OriginalFamilyHeader headerEnv U declaredType) (env : VEnv)
    (registry : CanonicalHead.Registry) (target : List VExpr) (required : Footprint) :
    (source : List VExpr) → (locals : List Nat) → (seed : Subst) →
    (available : Valuation) → VExpr → List VExpr → List FamilyKey → Type where
  | nil (resources : required.Available available) :
      OriginalFamilyCodeRows header env registry target required source locals seed available
        expression [] []
  | cons
      (original : EndpointRef headerEnv U source A (.sort level))
      (location : Located header.reference (.ref original))
      (row : PiRowCertificate env U registry target locals seed available A B (key : Key n) result)
      {support : Profile n}
      (admission : RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨key, support⟩ : DataRequest (Profile n)) key.anchor key.anchor)
      (extra : List Need)
      (bounded : ∀ need ∈ extra, need.rank ≤ n)
      (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
      (inputPresent : (⟨n, key.input⟩ : Need) ∈ row.seedNeeds extra)
      (tail : OriginalFamilyCodeRows header env registry target required (A :: source)
        (Locals.push locals) (seed.cons key.anchor) (Valuation.push (row.seedNeeds extra) available)
        B domains keys) :
      OriginalFamilyCodeRows header env registry target required source locals seed available
        (.forallE A B) (A :: domains) (⟨n, key, support⟩ :: keys)

def OriginalFamilyCodeRows.terminalLocals
    (rows : OriginalFamilyCodeRows header env registry target required
      source locals seed available expression domains keys) : List Nat :=
  match rows with
  | .nil _ => locals
  | .cons _ _ _ _ _ _ _ _ tail => tail.terminalLocals

def OriginalFamilyCodeRows.terminalValuation
    (rows : OriginalFamilyCodeRows header env registry target required
      source locals seed available expression domains keys) : Valuation :=
  match rows with
  | .nil _ => available
  | .cons _ _ _ _ _ _ _ _ tail => tail.terminalValuation

theorem OriginalFamilyRowHistory.closeExact
    {headerEnv : VEnv} {U : Nat} {declaredType : VExpr}
    {header : OriginalFamilyHeader headerEnv U declaredType}
    (history : OriginalFamilyRowHistory header env registry target source locals seed available expression domains keys)
    (tail : OriginalFamilyCodeRows header env registry target required source locals seed available
      expression remaining remainingKeys) :
    ∃ rows : OriginalFamilyCodeRows header env registry target required [] [] (nativeCaptureSubst []) (fun _ => []) declaredType (domains ++ remaining) (keys ++ remainingKeys),
      rows.terminalLocals = tail.terminalLocals ∧ rows.terminalValuation = tail.terminalValuation := by
  induction history generalizing remaining remainingKeys with
  | nil => exact ⟨tail, rfl, rfl⟩
  | snoc history original location row admission extra bounded covered inputPresent ih =>
    rw [List.append_assoc, List.singleton_append, List.append_assoc, List.singleton_append]
    exact ih (OriginalFamilyCodeRows.cons original location row admission extra bounded covered inputPresent tail)

theorem OriginalFamilyDeclaredPrefix.anyRows
    {headerEnv : VEnv} {U : Nat} {declaredType : VExpr}
    {header : OriginalFamilyHeader headerEnv U declaredType} {signature : ConstantTelescope declaredType}
    (declared : OriginalFamilyDeclaredPrefix header env registry target σ
      signature arguments assigned profile required keys)
    (saturated : arguments.length = signature.domains.length) :
    ∃ rows : OriginalFamilyCodeRows header env registry target required [] []
        (nativeCaptureSubst []) (fun _ => []) declaredType signature.domains keys,
      rows.terminalLocals = List.range arguments.length ∧
      rows.terminalValuation = declared.valuation := by
  have history := declared.history
  simp only [saturated, List.take_length, List.drop_length, wrapForalls] at history
  have result := history.closeExact (OriginalFamilyCodeRows.nil declared.seedAvailable)
  rw [List.append_nil, List.append_nil] at result
  simpa only [OriginalFamilyCodeRows.terminalLocals, OriginalFamilyCodeRows.terminalValuation,
    saturated] using result

theorem OriginalFamilyCodeRows.terminal_mem
    (rows : OriginalFamilyCodeRows header env registry target required
      source locals seed available expression domains keys)
    {index : Nat} {need : Need} (member : need ∈ available index) :
    need ∈ rows.terminalValuation (keys.length + index) := by
  induction rows generalizing index with
  | nil => simpa only [OriginalFamilyCodeRows.terminalValuation, List.length_nil, Nat.zero_add] using member
  | cons original location row admission extra bounded covered inputPresent tail ih =>
    have later := ih (index := index + 1) member
    simpa only [OriginalFamilyCodeRows.terminalValuation, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later

/-- Availability covers the full argument demand, not merely whichever
atoms appeared in the terminal type certificate. -/
theorem OriginalFamilyCodeRows.captureAvailable
    (rows : OriginalFamilyCodeRows header env registry target required
      source locals seed available expression domains keys) :
    (FamilyKey.captureFootprint keys).Available rows.terminalValuation := by
  induction rows with
  | nil => intro index need member; cases member
  | cons original location row admission extra bounded covered inputPresent tail ih =>
    intro index need member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      simpa only [Nat.add_zero, OriginalFamilyCodeRows.terminalValuation] using
        tail.terminal_mem (index := 0) inputPresent
    · exact ih index need member

theorem OriginalFamilyCodeRows.terminalLocals_eq
    (rows : OriginalFamilyCodeRows header env registry target required
      source locals seed available expression domains keys)
    (count : Nat) (localNames : locals = List.range count) :
    rows.terminalLocals = List.range (count + keys.length) := by
  induction rows generalizing count with
  | nil => simpa only [OriginalFamilyCodeRows.terminalLocals, List.length_nil, Nat.add_zero] using localNames
  | cons original location row admission extra bounded covered inputPresent tail ih =>
    have names := (congrArg Locals.push localNames).trans
      (show Locals.push (List.range count) = List.range (count + 1) by
        simp only [List.range_succ_eq_map, Locals.push])
    simpa only [OriginalFamilyCodeRows.terminalLocals, List.length_cons, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (count + 1) names
theorem OriginalFamilyCodeRows.length
    (rows : OriginalFamilyCodeRows header env registry target required
      source locals seed available expression domains keys) : keys.length = domains.length := by
  induction rows with
  | nil => rfl
  | cons original location row admission extra bounded covered inputPresent tail ih => exact congrArg Nat.succ ih

/-- Construct the complete terminal capture tree from actual row origins.
The domain chain is moved along source binders syntactically, so variable
interpretation can return to its exact original frozen key domain. -/
theorem OriginalFamilyCodeRows.captures
    {headerEnv env : VEnv} {U : Nat} {declaredType : VExpr}
    {header : OriginalFamilyHeader headerEnv U declaredType} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target domains : List VExpr} {locals : List Nat} {seed : Subst}
    {available : Valuation} {required : Footprint} {expression : VExpr} {keys : List FamilyKey}
    (rows : OriginalFamilyCodeRows header env registry target required
      source locals seed available expression domains keys)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N) :
    Nonempty (FamilyCaptures env U registry target (domains.reverse ++ source) rows.terminalLocals
      (familySubst seed (keys.map (·.key.anchor))) (constantCaptureVariables keys.length)
      (FamilyKey.uniform N keys bounded) (FamilyKey.captureFootprint keys)) := by
  induction rows with
  | nil => exact ⟨.nil⟩
  | @cons source A level locals seed available B n key result domains keys
      original location row support admission extra bounds covered inputPresent tail ih =>
    have bound := bounded ⟨n, key, support⟩ List.mem_cons_self
    obtain ⟨previous⟩ := ih (fun key member => bounded key (List.mem_cons_of_mem _ member))
    let finalSeed := familySubst (seed.cons key.anchor) (keys.map (·.key.anchor))
    have lookup : Lookup (domains.reverse ++ A :: source) keys.length (A.liftN (keys.length + 1)) := by
      simpa only [List.length_reverse, ← tail.length] using lookup_suffix domains.reverse source A
    have domainEq : (A.liftN (keys.length + 1)).subst finalSeed = A.subst seed := by
      rw [show keys.length + 1 = (keys.map (·.key.anchor)).length + 1 by simp]
      rw [show A.liftN ((keys.map (·.key.anchor)).length + 1) =
        A.lift.liftN (keys.map (·.key.anchor)).length by
          rw [liftN_liftN]; congr 1; omega]
      rw [familySubst_liftN, lift_subst_cons]
    have valueEq : finalSeed keys.length = key.anchor := by
      simpa only [List.length_map, Nat.add_zero, Subst.cons] using
        familySubst_drop (seed.cons key.anchor) (keys.map (·.key.anchor)) 0
    have alignment : DomainChain env U registry target (raiseKey N bound key).input
        (raiseKey N bound key).domain ((A.liftN (keys.length + 1)).subst finalSeed) := by
      rw [domainEq]
      exact row.alignment.raise henv bound
    have observation := (Obs.var (env := env) (U := U) (registry := registry) (target := target)
      tail.terminalLocals finalSeed keys.length key.input).raise bound
    have anchor : RankedData.RequestAdmission env U (relations env U registry N) target
        (raiseDataRequest N bound (⟨key, support⟩ : DataRequest (Profile n)))
        (finalSeed keys.length) (finalSeed keys.length) := by
      rw [valueEq]
      exact RankedData.RequestAdmission.raiseFamily henv bound admission
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
      captureVariables_succ, List.map_cons, familySubst, List.foldl_cons,
      FamilyKey.uniform, FamilyKey.request, FamilyKey.captureFootprint, OriginalFamilyCodeRows.terminalLocals,
      finalSeed] using
      (show Nonempty _ from ⟨FamilyCaptures.cons lookup observation (.refl _) alignment anchor previous⟩)

theorem PiRowCertificate.familyPlanBinderOriginal
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {source target : List VExpr} {name : Name} {levels : List VLevel}
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    {arguments : List VExpr} {available : Valuation} {A B : VExpr}
    {key : Key n} {result : Profile n} {output : Atom m}
    (row : PiRowCertificate env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments) available A B key result)
    (context : ContextDerivation headerEnv U source)
    (original : EndpointRef headerEnv U source A (.sort level))
    (domainIH : EndpointFundamental env registry context original)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst arguments) source)
    (fits : TailFits headerEnv env U registry target source (List.range arguments.length)
      (nativeCaptureSubst arguments) (nativeCaptureSubst arguments) available)
    (origin : signature.domains[arguments.length]? = some A)
    (extra : List Need)
    (bounded : ∀ need ∈ extra, need.rank ≤ n)
    (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
    (child : FamilyPlanResult env U registry target name levels signature (arguments ++ [key.anchor])
      (Valuation.push (row.seedNeeds extra) available) B output) :
    Nonempty (FamilyPlanResult env U registry target name levels signature arguments available
      (.forallE A B) (n := max n m + 1) (.fn (raiseKey (max n m) (Nat.le_max_left _ _) key)
        (raiseAtom (max n m) (Nat.le_max_right _ _) output))) := by
  obtain ⟨domain⟩ := row.domain.transfer_graded henv hscoped hTarget closed
    (domainIH target (List.range arguments.length) _ _ available closed hTarget substitutions
      (TailPairedFits.diagonal context fits)).1
    row.domainAvailable
  have guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) A
      (domainKey key (A.subst (nativeCaptureSubst arguments))) row.domainSupport :=
    ⟨row.inputTyped, row.domain.formed, .refl, domain.related, row.alignment.admission henv row.anchor⟩
  let raised := child.raise (Nat.le_max_right n m)
  have domainCode := row.domain.raise (Nat.le_max_left n m)
  have raisedGuard := guard.raise henv (Nat.le_max_left n m)
  have coverage := row.seedCoverageRaised extra bounded covered (Nat.le_max_left n m)
  obtain ⟨packed, outside, pack, included, outsideAvailable⟩ :=
    Footprint.pack_available raised.resources
      (fun need member => (coverage need member).1) (fun need member => (coverage need member).2)
  obtain ⟨typePacked, typeOutside, typePack, typeIncluded, typeOutsideAvailable⟩ :=
    Footprint.pack_available raised.typeResources
      (fun need member => (coverage need member).1) (fun need member => (coverage need member).2)
  let actualKey := raiseKey (max n m) (Nat.le_max_left n m)
    (domainKey key (A.subst (nativeCaptureSubst arguments)))
  have code : CodeCert env U registry target (Locals.push (List.range arguments.length))
      ((nativeCaptureSubst arguments).cons key.anchor) B raised.support raised.typeFootprint := by
    simpa only [List.length_append, List.length_singleton, List.range_succ_eq_map,
      Locals.push, nativeCaptureSubst_append] using raised.certificate
  let assembled : FamilyPlanResult env U registry target name levels signature arguments available
      (.forallE A B) (n := max n m + 1) (.fn actualKey (raiseAtom (max n m) (Nat.le_max_right n m) output)) := {
    footprint := row.domainFootprint ++ outside
    plan := .binder origin domainCode raisedGuard raised.plan pack included
    resources := fun i need member => (List.mem_append.mp member).elim
      (row.domainAvailable i need) (outsideAvailable i need)
    support := .pi (A.subst (nativeCaptureSubst arguments))
      (B.subst (nativeCaptureSubst arguments).lift)
      (raiseProfile (max n m) (Nat.le_max_left n m) row.domainSupport)
      [(actualKey, raised.support)]
    typeFootprint := row.domainFootprint ++ typeOutside
    certificate := by
      apply CodeCert.piLiteral domainCode
      simpa only [List.append_nil] using
        PiRows.cons raisedGuard code typePack typeIncluded PiRows.nil
    typeResources := fun i need member => (List.mem_append.mp member).elim
      (row.domainAvailable i need) (typeOutsideAvailable i need)
    typed := by
      apply Profile.HasType.fn _ (List.mem_singleton_self _) raised.typed
      refine Profile.WF.pi_iff.mpr ⟨domainCode.formed, ?_⟩
      intro k r member
      cases List.mem_singleton.mp member
      exact ⟨raisedGuard.inputTyped, raised.typed.wf_type⟩ }
  have chain := row.alignment.raise henv (Nat.le_max_left n m)
  have forward := chain.view key.anchor (raiseAtom (max n m) (Nat.le_max_right n m) output)
  exact ⟨assembled.view (forward.inverse henv)⟩

theorem OriginalFamilyCodeRows.closePlan
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {headerType : VExpr} {header : OriginalFamilyHeader headerEnv U headerType}
    (calls : header.Fundamentals env registry)
    {source target : List VExpr} {locals : List Nat} {seed : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : OriginalFamilyCodeRows header env registry target required
      source locals seed available expression domains keys)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    (localNames : locals = List.range arguments.length)
    (realization : seed = nativeCaptureSubst arguments)
    (remaining : domains = signature.domains.drop arguments.length)
    (residual : expression = wrapForalls domains signature.result)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target seed seed source)
    (fits : TailFits headerEnv env U registry target source locals seed seed available)
    {atom : Atom m}
    (terminal : FamilyPlanResult env U registry target name levels signature
      (arguments ++ keys.map (·.key.anchor)) rows.terminalValuation signature.result atom) :
    Nonempty (FamilyPlanResult env U registry target name levels signature arguments available
      expression (FamilyKey.replayAtom keys atom)) := by
  induction rows generalizing arguments with
  | nil resources =>
    simp only [wrapForalls] at residual
    have finish := Nonempty.intro terminal
    simpa only [List.map_nil, List.append_nil, OriginalFamilyCodeRows.terminalValuation,
      FamilyKey.replayAtom, residual, List.foldr_nil] using finish
  | @cons source A level locals seed available B n key result domains keys
      original location row support admission extra bounded covered inputPresent tail ih =>
    subst locals seed
    have origin : signature.domains[arguments.length]? = some A := by
      have head : (signature.domains.drop arguments.length)[0]? = some A := by
        rw [← remaining]
        rfl
      simpa only [List.getElem?_drop, Nat.add_zero] using head
    have nextRemaining : domains = signature.domains.drop (arguments ++ [key.anchor]).length := by
      simp only [List.length_append, List.length_singleton, List.drop_add_one_eq_tail_drop,
        ← remaining, List.tail_cons]
    have nextResidual : B = wrapForalls domains signature.result :=
      (VExpr.forallE.inj residual).2
    obtain ⟨raw, ⟨localFits⟩⟩ := row.pushSeedOriginal henv hscoped below
      (location.contextDerivation .nil) original (calls location) closed hTarget
      substitutions fits extra bounded covered
    have nextLocals : Locals.push (List.range arguments.length) =
        List.range (arguments ++ [key.anchor]).length := by
      simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
    have nextSeed : (nativeCaptureSubst arguments).cons key.anchor =
        nativeCaptureSubst (arguments ++ [key.anchor]) := (nativeCaptureSubst_append arguments key.anchor).symm
    have terminal' : FamilyPlanResult env U registry target name levels signature
        ((arguments ++ [key.anchor]) ++ keys.map (·.key.anchor)) tail.terminalValuation
        signature.result atom := by
      simpa only [List.map_cons, List.append_assoc, List.singleton_append,
        OriginalFamilyCodeRows.terminalValuation] using terminal
    obtain ⟨child⟩ := ih nextLocals nextSeed nextRemaining nextResidual
      (row.seedClosed extra closed) raw localFits.forward terminal'
    exact row.familyPlanBinderOriginal henv hscoped below (location.contextDerivation .nil)
      original (calls location) closed hTarget substitutions fits
      origin extra bounded covered child

/-- The initial empty source context closes every actual plan and code
leaf. The resulting bare-family demand replays the same frozen row keys. -/
theorem OriginalFamilyCodeRows.barePlan
    {headerEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    {headerType : VExpr} {header : OriginalFamilyHeader headerEnv U headerType}
    (calls : header.Fundamentals env registry)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {keys : List FamilyKey} {required : Footprint}
    (rows : OriginalFamilyCodeRows header env registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) declaredType signature.domains keys)
    (resultSort : signature.result = .sort level) (relevance : Relevant level relevant)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N) :
    Nonempty (FamilyPlanResult env U registry target name levels signature [] (fun _ => []) declaredType
      (FamilyKey.replayAtom (n := N + 1) keys (.family ⟨name, levels, relevant, FamilyKey.uniform N keys bounded⟩))) := by
  obtain ⟨captures⟩ := rows.captures henv N bounded
  have localNames := rows.terminalLocals_eq 0 rfl
  have captures' : FamilyCaptures env U registry target signature.domains.reverse
      (List.range (keys.map (·.key.anchor)).length)
      (nativeCaptureSubst (keys.map (·.key.anchor)))
      (constantCaptureVariables (keys.map (·.key.anchor)).length)
      (FamilyKey.uniform N keys bounded) (FamilyKey.captureFootprint keys) := by
    simpa only [List.append_nil, familySubst_native, List.nil_append, List.length_map,
      localNames, Nat.zero_add] using captures
  let terminal := FamilyPlanResult.terminal (name := name) (levels := levels)
    (by simpa only [List.length_map] using rows.length) resultSort relevance captures' rows.captureAvailable
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  exact rows.closePlan henv hscoped below calls rfl rfl (by simp) signature.type_eq
    emptyClosed hTarget .nil .nil terminal


end Lean4Lean.AnchoredSource.Adapted
