import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureObservation
import Lean4Lean.Theory.Typing.AnchoredNativeRetelescopeContext

/-! A finite family telescope is closed from its actual terminal captures.
Each binder packs the new computational and type footprints separately;
its declared domain certificate and domain chain are retained from the row.
The maximum grade is computed from the already frozen key sequence. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false
open private checks AtomWF FamilyWF RequestWF KeyWF AtomTyped from Lean4Lean.Theory.Typing.AnchoredProfiles

theorem FamilyCaptures.inputsWF
    (captures : FamilyCaptures env U registry target source locals seed expressions keys footprint) :
    ∀ key ∈ keys, key.input.WF ∧ key.support.WF := by
  match captures with
  | .nil => intro key member; cases member
  | .cons lookup value adapter alignment anchor tail =>
    intro key member
    rcases List.mem_cons.mp member with equal | member
    · subst key
      obtain ⟨_, _, typed, formed, _⟩ := anchor
      exact ⟨typed.wf_value, formed.wf_value⟩
    · exact tail.inputsWF key member
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

theorem FamilyCaptures.familyTyped {name : Name} {levels : List VLevel}
    {keys : List (DataRequest (Profile n))}
    (captures : FamilyCaptures env U registry target source locals seed expressions keys footprint)
    (relevant : Bool) :
    (Profile.singleton (n := n + 1) (.family ⟨name, levels, relevant, keys⟩)).HasType (.sort relevant) := by
  refine ⟨?_, Profile.WF.sort (n := n + 1) relevant, ?_⟩
  · intro atom member
    cases List.mem_singleton.mp member
    exact captures.inputsWF
  · intro atom member
    cases List.mem_singleton.mp member
    exact ⟨_, List.mem_singleton_self _, rfl⟩

def FamilyKey.replayRank : List FamilyKey → Nat → Nat
  | [], rank => rank
  | key :: keys, rank => max key.rank (FamilyKey.replayRank keys rank) + 1

def FamilyKey.replayAtom : (keys : List FamilyKey) → Atom n → Atom (FamilyKey.replayRank keys n)
  | [], atom => atom
  | key :: keys, atom =>
    .fn (raiseKey _ (Nat.le_max_left _ _) key.key)
      (raiseAtom _ (Nat.le_max_right _ _) (FamilyKey.replayAtom keys atom))

def FamilyKey.replayStep (key : FamilyKey) (demand : Sigma Atom) : Sigma Atom :=
  ⟨max key.rank demand.1 + 1,
    .fn (raiseKey _ (Nat.le_max_left _ _) key.key)
      (raiseAtom _ (Nat.le_max_right _ _) demand.2)⟩

theorem FamilyKey.replay_fold (keys : List FamilyKey) (atom : Atom n) :
    (⟨FamilyKey.replayRank keys n, FamilyKey.replayAtom keys atom⟩ : Sigma Atom) =
      keys.foldr FamilyKey.replayStep ⟨n, atom⟩ := by
  induction keys with
  | nil => rfl
  | cons key keys ih => exact congrArg (FamilyKey.replayStep key) ih

noncomputable def FamilyPlan.raise
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint)
    {N : Nat} (bound : n ≤ N) :
    FamilyPlan env U registry target name levels signature arguments (raiseProfile N bound demand) footprint := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    simpa only [raiseProfile_self] using plan
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [raiseProfile_self] using plan
    · have low : n ≤ N := by omega
      rw [raiseProfile_step low]
      exact .pad (ih low)

/-- The source type support is rebuilt along with the computational plan.
Both keep their actual footprints in the retained finite ledger. -/
structure FamilyPlanResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (name : Name) (levels : List VLevel) {declaredType : VExpr}
    (signature : ConstantTelescope declaredType) (arguments : List VExpr)
    (available : Valuation) (expression : VExpr) (atom : Atom n) where
  footprint : Footprint
  plan : FamilyPlan env U registry target name levels signature arguments (.singleton atom) footprint
  resources : footprint.Available available
  support : Profile n
  typeFootprint : Footprint
  certificate : CodeCert env U registry target (List.range arguments.length)
    (nativeCaptureSubst arguments) expression support typeFootprint
  typeResources : typeFootprint.Available available
  typed : (Profile.singleton atom).HasType support

noncomputable def FamilyPlanResult.terminal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {available : Valuation} {keys : List (DataRequest (Profile n))} {footprint : Footprint}
    (saturated : arguments.length = signature.domains.length)
    (resultSort : signature.result = .sort level) (relevance : Relevant level relevant)
    (captures : FamilyCaptures env U registry target signature.domains.reverse
      (List.range arguments.length) (nativeCaptureSubst arguments)
      (constantCaptureVariables arguments.length) keys footprint)
    (resources : footprint.Available available) :
    FamilyPlanResult env U registry target name levels signature arguments available signature.result
      (n := n + 1) (.family ⟨name, levels, relevant, keys⟩) where
  footprint := footprint
  plan := .terminal saturated resultSort relevance captures
  resources := resources
  support := .sort relevant
  typeFootprint := []
  certificate := by
    rw [resultSort]
    exact .seed (.sort relevance) (Profile.HasType.sort relevant)
  typeResources := fun _ _ member => nomatch member
  typed := captures.familyTyped relevant

noncomputable def FamilyPlanResult.raise
    {name : Name} {levels : List VLevel} {atom : Atom n}
    (result : FamilyPlanResult env U registry target name levels signature arguments available expression atom)
    {N : Nat} (bound : n ≤ N) :
    FamilyPlanResult env U registry target name levels signature arguments available expression
      (raiseAtom N bound atom) where
  footprint := result.footprint
  plan := by simpa only [raiseProfile_singleton] using result.plan.raise bound
  resources := result.resources
  support := raiseProfile N bound result.support
  typeFootprint := result.typeFootprint
  certificate := result.certificate.raise bound
  typeResources := result.typeResources
  typed := by simpa only [raiseProfile_singleton] using Profile.HasType.raise bound result.typed

noncomputable def FamilyPlanResult.view
    {name : Name} {levels : List VLevel} {atom atom' : Atom n}
    (result : FamilyPlanResult env U registry target name levels signature arguments available expression atom)
    (view : AtomView env U registry target atom atom') :
    FamilyPlanResult env U registry target name levels signature arguments available expression atom' where
  footprint := result.footprint
  plan := .view result.plan view
  resources := result.resources
  support := view.mapType result.support
  typeFootprint := result.typeFootprint
  certificate := .map view result.certificate
  typeResources := result.typeResources
  typed := view.mapType_typed result.typed

/-- The row's complete finite ledger can be packed at any larger grade.
The old request profiles remain literal source leaves. -/
theorem PiRowCertificate.seedCoverageRaised
    (row : PiRowCertificate env U registry target locals seed available A B (key : Key n) result)
    (extra : List Need)
    (bounded : ∀ need ∈ extra, need.rank ≤ n)
    (covered : ∀ need ∈ extra, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
    {N : Nat} (bound : n ≤ N) :
    ∀ need ∈ row.seedNeeds extra, need.rank ≤ N ∧
      ∀ atom ∈ (need.atGrade N).atoms, atom ∈ (raiseKey N bound key).input.atoms := by
  intro need member
  obtain ⟨low, included⟩ := row.seedCoverage extra bounded covered need member
  refine ⟨Nat.le_trans low bound, ?_⟩
  rw [need.atGrade_raise bound low]
  exact raiseProfile_subset bound included

/-- One backwards binder uses the actual declared domain certificate and
the actual new child footprints. The finite domain chain restores the
natural application key after constructing the declared-domain plan. -/
theorem PiRowCertificate.familyPlanBinder
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {name : Name} {levels : List VLevel}
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    {arguments : List VExpr} {available : Valuation} {A B : VExpr}
    {key : Key n} {result : Profile n} {output : Atom m}
    (row : PiRowCertificate env U registry target (List.range arguments.length)
      (nativeCaptureSubst arguments) available A B key result)
    (original : OriginalTypePayload sourceEnv env U registry source A (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst arguments) source)
    (fits : PairedFits env U registry source target (List.range arguments.length)
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
    (original.2 target (List.range arguments.length) _ _ available closed hTarget substitutions fits).1
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

/-- Close the retained declaration telescope around one concrete terminal
packet. The recursion consumes only stored rows and the original declaration
children. In particular, no step requests a new argument observation. -/
theorem FamilySeededCodeRows.closePlan
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {seed : Subst}
    {available : Valuation} {expression : VExpr} {domains : List VExpr}
    {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required
      source locals seed available expression domains keys)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    (localNames : locals = List.range arguments.length)
    (realization : seed = nativeCaptureSubst arguments)
    (remaining : domains = signature.domains.drop arguments.length)
    (residual : expression = wrapForalls domains signature.result)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target seed seed source)
    (fits : PairedFits env U registry source target locals seed seed available)
    {atom : Atom m}
    (terminal : FamilyPlanResult env U registry target name levels signature
      (arguments ++ keys.map (·.key.anchor)) rows.terminalValuation signature.result atom) :
    Nonempty (FamilyPlanResult env U registry target name levels signature arguments available
      expression (FamilyKey.replayAtom keys atom)) := by
  induction rows generalizing arguments with
  | nil resources =>
    simp only [wrapForalls] at residual
    have finish := Nonempty.intro terminal
    simpa only [List.map_nil, List.append_nil, FamilySeededCodeRows.terminalValuation,
      FamilyKey.replayAtom, residual, List.foldr_nil] using finish
  | @cons source A level locals seed available B n key result domains keys
      original row support admission extra bounded covered inputPresent tail ih =>
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
    obtain ⟨raw, localFits⟩ := row.pushSeed henv hscoped hle original closed hTarget
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
        FamilySeededCodeRows.terminalValuation] using terminal
    obtain ⟨child⟩ := ih nextLocals nextSeed nextRemaining nextResidual
      (row.seedClosed extra closed) raw localFits terminal'
    exact row.familyPlanBinder henv hscoped hle original closed hTarget substitutions fits
      origin extra bounded covered child

/-- The initial empty source context closes every actual plan and code
leaf. The resulting bare-family demand replays the same frozen row keys. -/
theorem FamilySeededCodeRows.barePlan
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
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
  exact rows.closePlan henv hscoped hle rfl rfl (by simp) signature.type_eq
    emptyClosed hTarget .nil .nil terminal

theorem FamilyPlanResult.bareObservation
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {seed : Subst}
    {name : Name} {levels : List VLevel} {info : VConstant}
    {signature : ConstantTelescope (info.type.instL levels)} {atom : Atom n}
    (result : FamilyPlanResult env U registry target name levels signature [] (fun _ => [])
      (info.type.instL levels) atom)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (levelsWF : ∀ level ∈ levels, level.WF U) (length : levels.length = info.uvars)
    (typeClosed : info.type.Closed) :
    Nonempty (Obs env U registry target locals seed (.const name levels) (.singleton atom) []) := by
  have footprintEmpty : result.footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    exact nomatch result.resources index need member
  have typeEmpty : result.typeFootprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    exact nomatch result.typeResources index need member
  have levelsSelf : ∀ ls : List VLevel, List.Forall₂ (· ≈ ·) ls ls := by
    intro ls
    induction ls with
    | nil => exact .nil
    | cons level levels ih => exact .cons rfl ih
  exact ⟨.family lookup notDefinition notNative notQuotient levelsWF length levelsWF (levelsSelf levels)
    signature typeClosed (by simpa only [List.length_nil, List.range_zero, typeEmpty] using result.certificate)
    result.typed (by simpa only [footprintEmpty] using result.plan)⟩

end Lean4Lean.AnchoredSource.Adapted
