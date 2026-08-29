import Lean4Lean.ProjectionCertificate
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.TypeChecker.Inner

open Lean hiding Environment Exception

/-- Soundness of the executable candidate-scope gate.  This is the direct
source of the free-variable premise used by checked candidate inference; it
does not trust any corresponding claim made by the candidate generator. -/
theorem projectionCandidateScopeValid_sound
    (H : projectionCandidateScopeValid lctx expression = true) :
    FVarsIn (fun fvarId => ∃ declaration, lctx.find? fvarId = some declaration)
      expression := by
  induction expression <;>
    simp_all [projectionCandidateScopeValid, FVarsIn,
      Option.isSome_iff_exists]

/-- At a verified checker boundary the executable local-context membership
test is exactly membership in the abstract local-variable context. -/
theorem projectionCandidateScopeValid_fvarsIn
    (c : VContext)
    (H : projectionCandidateScopeValid c.lctx expression = true) :
    FVarsIn (· ∈ c.vlctx.fvars) expression := by
  have Hscope := projectionCandidateScopeValid_sound H
  apply Hscope.mono
  intro fvarId
  rintro ⟨declaration, hfind⟩
  have hfind' : c.lctx'.find? fvarId = some declaration := by
    simpa only [c.lctx_eq] using hfind
  exact c.trlctx.find?_eq_some.mp ⟨declaration, hfind'⟩

/-- Pattern abstraction only removes concrete subexpressions or rearranges
bound variables; it never introduces a free variable or universe metavariable.
This is the source-side coverage fact needed when the generated projection
candidate is checked with `inferOnly := false`. -/
theorem abstractProjectionPatterns_fvarsIn
    (patterns : List Expr) : ∀ (expression : Expr) (depth : Nat),
    FVarsIn predicate expression →
      FVarsIn predicate
        (abstractProjectionPatterns patterns expression depth)
  | expression, depth => by
      intro Hexpression
      unfold abstractProjectionPatterns
      split
      · trivial
      · cases expression <;>
          simp_all [FVarsIn, abstractProjectionPatterns_fvarsIn]

/-- Wrapping a generated telescope preserves free-variable coverage when
every generated domain and the final body have that coverage. -/
theorem wrapProjectionLambdas_fvarsIn
    (hdomains : ∀ binder ∈ binders, FVarsIn predicate binder.domain)
    (hbody : FVarsIn predicate body) :
    FVarsIn predicate (wrapProjectionLambdas binders body) := by
  induction binders with
  | nil => simpa [wrapProjectionLambdas] using hbody
  | cons binder binders ih =>
      simp only [wrapProjectionLambdas, List.foldr_cons, FVarsIn]
      exact ⟨hdomains binder (by simp), ih
        (fun current hcurrent => hdomains current (by simp [hcurrent]))⟩

/-- The synthetic de Bruijn index spine contains no free variables. -/
theorem projectionBoundVars_fvarsIn
    (count : Nat) :
    ∀ expression ∈ projectionBoundVars count,
      FVarsIn predicate expression := by
  intro expression hexpression
  simp [projectionBoundVars] at hexpression
  rcases hexpression with ⟨index, _, rfl⟩
  trivial

/-- Independent structural meaning of a parsed lambda telescope.  Binder
names and annotations are retained existentially by the derivation, while
the ordered domains and final body are fixed. -/
inductive LambdaTelescope : List Expr → Expr → Expr → Prop
  | nil : LambdaTelescope [] body body
  | cons : LambdaTelescope domains body result →
      LambdaTelescope (domain :: domains) (.lam name domain body bi) result

/-- Strict translation evidence for a generated lambda telescope.  Unlike a
plain list of translated domains, this relation records each domain in the
context in which it is actually checked, and leaves the exact translated
body visible at the end of the telescope. -/
inductive ProjectionLambdaTranslation (env : VEnv) (Us : List Name) :
    VLCtx → List ProjectionBinder → Expr → VExpr → Prop
  | nil (Hbody : TrExprS env Us Delta body targetBody) :
      ProjectionLambdaTranslation env Us Delta [] body targetBody
  | cons
      (HdomainType : env.IsType Us.length Delta.toCtx targetDomain)
      (Hdomain : TrExprS env Us Delta binder.domain targetDomain)
      (Htail : ProjectionLambdaTranslation env Us
        ((none, .vlam targetDomain) :: Delta) binders body targetBody) :
      ProjectionLambdaTranslation env Us Delta (binder :: binders) body
        (.lam targetDomain targetBody)

/-- Peeling a strict translation of `wrapProjectionLambdas` produces the
context-indexed telescope evidence above. -/
theorem ProjectionLambdaTranslation.ofWrap
    (H : TrExprS env Us Delta
      (wrapProjectionLambdas binders body) target) :
    ProjectionLambdaTranslation env Us Delta binders body target := by
  induction binders generalizing Delta target with
  | nil => simpa [wrapProjectionLambdas] using
      (ProjectionLambdaTranslation.nil H)
  | cons binder binders ih =>
      simp only [wrapProjectionLambdas, List.foldr_cons] at H
      cases H with
      | lam HdomainType Hdomain Hbody =>
          exact .cons HdomainType Hdomain (ih Hbody)

theorem takeLambdas_sound
    (H : takeLambdas count expression = some (domains, body)) :
    LambdaTelescope domains expression body ∧ domains.length = count := by
  induction count generalizing expression domains with
  | zero =>
      simp [takeLambdas] at H
      obtain ⟨rfl, rfl⟩ := H
      exact ⟨.nil, rfl⟩
  | succ count ih =>
      cases expression <;> simp [takeLambdas] at H
      rename_i name domain expression bi
      rcases H with ⟨domains', htake, rfl⟩
      have ⟨htelescope, hlength⟩ := ih htake
      exact ⟨.cons htelescope, by simp [hlength]⟩

theorem projectionMinorDomains_sound
    (H : projectionMinorDomains? numFields index minor = some domains) :
    LambdaTelescope domains minor
        (.bvar (numFields - index - 1)) ∧
      domains.length = numFields := by
  unfold projectionMinorDomains? at H
  cases htake : takeLambdas numFields minor with
  | none => simp [htake] at H
  | some pair =>
    rcases pair with ⟨domains', body⟩
    simp [htake] at H
    rcases H with ⟨hbody, rfl⟩
    have ⟨htelescope, hlength⟩ := takeLambdas_sound htake
    have hbody' : body = .bvar (numFields - index - 1) := by
      have heqv : body == .bvar (numFields - index - 1) ↔
          body = .bvar (numFields - index - 1) := by
        conv => lhs; simp [(· == ·)]
        cases body <;> simp [Expr.eqv']
      exact heqv.mp hbody
    subst body
    exact ⟨htelescope, hlength⟩

theorem takeLambdas_wrapProjectionLambdas
    (binders : List ProjectionBinder) (body : Expr) :
    takeLambdas binders.length (wrapProjectionLambdas binders body) =
      some (binders.map (·.domain), body) := by
  induction binders with
  | nil => rfl
  | cons binder binders ih =>
      change (do
        let (domains, result) ← takeLambdas binders.length
          (wrapProjectionLambdas binders body)
        return (binder.domain :: domains, result)) =
          some (binder.domain :: binders.map (·.domain), body)
      rw [ih]
      rfl

theorem projectionMinorDomains_wrapProjectionLambdas
    (binders : List ProjectionBinder) (index : Nat) :
    projectionMinorDomains? binders.length index
        (wrapProjectionLambdas binders
          (.bvar (binders.length - index - 1))) =
      some (binders.map (·.domain)) := by
  simp [projectionMinorDomains?, takeLambdas_wrapProjectionLambdas]

theorem parsedProjectionMinor?_exists
    (H : projectionMinorDomains? numFields index minor = some domains) :
    ∃ parsed, parsedProjectionMinor? numFields index minor = some parsed := by
  unfold parsedProjectionMinor?
  split
  · exact ⟨_, rfl⟩
  · rename_i hnone
    rw [hnone] at H
    contradiction

theorem projection_getAppFn_mkAppN
    (fn : Expr) (arguments : Array Expr) :
    (mkAppN fn arguments).getAppFn = fn.getAppFn := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  generalize arguments.toList = argumentList
  induction argumentList generalizing fn with
  | nil => rfl
  | cons argument arguments ih =>
      simpa [Expr.getAppFn] using ih (fn := .app fn argument)

theorem projection_getAppArgsList_mkAppN
    (fn : Expr) (arguments : Array Expr) :
    (mkAppN fn arguments).getAppArgsList =
      fn.getAppArgsList ++ arguments.toList := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  generalize arguments.toList = argumentList
  induction argumentList generalizing fn with
  | nil => simp
  | cons argument arguments ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Expr.getAppArgsList_app, List.append_assoc]

@[simp] theorem projection_getAppFn_mkAppN_const
    (name : Name) (levels : List Level) (arguments : Array Expr) :
    (mkAppN (.const name levels) arguments).getAppFn =
      .const name levels := projection_getAppFn_mkAppN ..

@[simp] theorem projection_getAppArgs_toList_mkAppN_const
    (name : Name) (levels : List Level) (arguments : Array Expr) :
    (mkAppN (.const name levels) arguments).getAppArgs.toList =
      arguments.toList := by
  simp only [Expr.getAppArgs_toList,
    projection_getAppArgsList_mkAppN]
  rfl

theorem projection_mkAppN_eq_mkAppList
    (fn : Expr) (arguments : Array Expr) :
    mkAppN fn arguments = fn.mkAppList arguments.toList := by
  unfold mkAppN
  rw [← Array.foldl_toList, Expr.mkAppList_eq_foldl]
  induction arguments.toList generalizing fn with
  | nil => rfl
  | cons argument arguments ih =>
      simpa using ih (fn := .app fn argument)

/-- Array application has the same free-variable coverage rule as list
application. -/
theorem FVarsIn.mkAppN
    (hfn : FVarsIn predicate fn)
    (hargs : ∀ argument ∈ arguments.toList,
      FVarsIn predicate argument) :
    FVarsIn predicate (Lean.mkAppN fn arguments) := by
  rw [projection_mkAppN_eq_mkAppList]
  exact FVarsIn.mkAppList.mpr ⟨hfn, hargs⟩

/-- Pointwise translations and ordinary argument typings retained by an
application stack.  This is exactly the evidence already present in every
strict application translation; no extra checking is performed. -/
theorem AppStack.checkedArguments
    (H : AppStack env Us Delta fn target arguments) :
    ∃ translatedArguments,
      List.Forall₂ (fun source translated =>
        TrExprS env Us Delta source translated ∧
          ∃ type, env.HasType Us.length Delta.toCtx translated type)
        arguments translatedArguments := by
  induction H with
  | head _ => exact ⟨[], .nil⟩
  | app functionType argumentType functionTranslation argumentTranslation
      tail ih =>
      rcases ih with ⟨translatedArguments, htranslated⟩
      exact ⟨_, .cons ⟨argumentTranslation, _, argumentType⟩ htranslated⟩

/-- Select the translated element immediately after an arbitrary literal
source prefix. -/
theorem forall₂_after_prefix_head
    (H : List.Forall₂ relation (sourcePrefix ++ source :: suffix) targets) :
    ∃ target, relation source target := by
  induction sourcePrefix generalizing targets with
  | nil =>
      cases H with
      | cons head _ => exact ⟨_, head⟩
  | cons prefixHead prefixTail ih =>
      cases H with
      | cons _ tail => exact ih tail

/-- A strict translation of a generated candidate contains a checked strict
translation of the exact transparent motive supplied to `.casesOn`. -/
theorem GeneratedProjectionCandidate.checkedMotive
    (generated : GeneratedProjectionCandidate projection)
    (H : TrExprS env Us Delta generated.candidate target) :
    ∃ translatedMotive motiveType,
      TrExprS env Us Delta
        (wrapProjectionLambdas
          (generated.indexBinders ++ [{
            name := `_major
            domain := mkAppN
              (.const projection.expansion.typeName
                projection.expansion.familyLevels)
              ((projection.expansion.params.map fun parameter =>
                  parameter.liftLooseBVars 0 generated.indexBinders.length) ++
                projectionBoundVars generated.indexBinders.length).toArray
            info := .default }])
          (abstractProjectionPatterns
            (projection.expansion.indices ++
              [projection.expansion.struct]) projection.type))
        translatedMotive ∧
      env.HasType Us.length Delta.toCtx translatedMotive motiveType := by
  rw [generated.exact, projection_mkAppN_eq_mkAppList] at H
  rcases AppStack.build H with ⟨translatedHead, stack⟩
  rcases Lean4Lean.TypeChecker.Inner.AppStack.checkedArguments stack with
    ⟨translatedArguments, harguments⟩
  have harguments' : List.Forall₂ (fun source translated =>
      TrExprS env Us Delta source translated ∧
        ∃ type, env.HasType Us.length Delta.toCtx translated type)
      (projection.expansion.params ++
        wrapProjectionLambdas
          (generated.indexBinders ++ [{
            name := `_major
            domain := mkAppN
              (.const projection.expansion.typeName
                projection.expansion.familyLevels)
              ((projection.expansion.params.map fun parameter =>
                  parameter.liftLooseBVars 0 generated.indexBinders.length) ++
                projectionBoundVars generated.indexBinders.length).toArray
            info := .default }])
          (abstractProjectionPatterns
            (projection.expansion.indices ++ [projection.expansion.struct])
            projection.type) ::
          (projection.expansion.indices ++ [projection.expansion.struct,
            wrapProjectionLambdas generated.fieldBinders
              (.bvar (projection.expansion.numFields -
                projection.expansion.index - 1))]))
      translatedArguments := by
    simpa [List.append_assoc] using harguments
  rcases forall₂_after_prefix_head
      (sourcePrefix := projection.expansion.params)
      (source := wrapProjectionLambdas
        (generated.indexBinders ++ [{
          name := `_major
          domain := mkAppN
            (.const projection.expansion.typeName
              projection.expansion.familyLevels)
            ((projection.expansion.params.map fun parameter =>
                parameter.liftLooseBVars 0 generated.indexBinders.length) ++
              projectionBoundVars generated.indexBinders.length).toArray
          info := .default }])
        (abstractProjectionPatterns
          (projection.expansion.indices ++ [projection.expansion.struct])
          projection.type))
      harguments' with ⟨translatedMotive, hmotive⟩
  exact ⟨translatedMotive, hmotive.2.choose, hmotive.1, hmotive.2.choose_spec⟩

/-- The accepted candidate exposes the exact translated motive body after
peeling its generated index-and-major lambda telescope.  Every binder domain
is retained in its real progressively extended checking context. -/
theorem GeneratedProjectionCandidate.checkedMotiveTelescope
    (generated : GeneratedProjectionCandidate projection)
    (H : TrExprS env Us Delta generated.candidate target) :
    ∃ translatedMotive motiveType,
      ProjectionLambdaTranslation env Us Delta
        (generated.indexBinders ++ [{
          name := `_major
          domain := mkAppN
            (.const projection.expansion.typeName
              projection.expansion.familyLevels)
            ((projection.expansion.params.map fun parameter =>
                parameter.liftLooseBVars 0 generated.indexBinders.length) ++
              projectionBoundVars generated.indexBinders.length).toArray
          info := .default }])
        (abstractProjectionPatterns
          (projection.expansion.indices ++ [projection.expansion.struct])
          projection.type)
        translatedMotive ∧
      env.HasType Us.length Delta.toCtx translatedMotive motiveType := by
  rcases generated.checkedMotive H with
    ⟨translatedMotive, motiveType, Hmotive, HmotiveType⟩
  exact ⟨translatedMotive, motiveType,
    ProjectionLambdaTranslation.ofWrap Hmotive, HmotiveType⟩

theorem GeneratedProjectionCandidate.parses
    (generated : GeneratedProjectionCandidate projection) :
    ∃ shell, projection.expansion.parseShell? generated.candidate =
      some shell := by
  have hminor : projectionMinorDomains?
      projection.expansion.numFields projection.expansion.index
        (wrapProjectionLambdas generated.fieldBinders
          (.bvar (projection.expansion.numFields -
            projection.expansion.index - 1))) =
      some (generated.fieldBinders.map (·.domain)) := by
    rw [← generated.fieldCount]
    exact projectionMinorDomains_wrapProjectionLambdas ..
  rcases parsedProjectionMinor?_exists hminor with ⟨parsed, hparsed⟩
  rw [generated.exact]
  simp [ProjectionExpansion.parseShell?, hparsed]
  omega

/-- Free-variable coverage for the exact generated candidate.  Every source
of syntax in the generator is listed explicitly; in particular the theorem
does not accept a pretranslated candidate or any projection resolver. -/
theorem GeneratedProjectionCandidate.fvarsIn
    (generated : GeneratedProjectionCandidate projection)
    (hresultLevel : generated.resultLevel.hasMVar' = false)
    (hfamilyLevels : ∀ level ∈ projection.expansion.familyLevels,
      level.hasMVar' = false)
    (hparams : ∀ parameter ∈ projection.expansion.params,
      FVarsIn predicate parameter)
    (hindices : ∀ index ∈ projection.expansion.indices,
      FVarsIn predicate index)
    (hstruct : FVarsIn predicate projection.expansion.struct)
    (htype : FVarsIn predicate projection.type)
    (hindexDomains : ∀ binder ∈ generated.indexBinders,
      FVarsIn predicate binder.domain)
    (hfieldDomains : ∀ binder ∈ generated.fieldBinders,
      FVarsIn predicate binder.domain) :
    FVarsIn predicate generated.candidate := by
  have hfamilyConst : FVarsIn predicate
      (.const projection.expansion.typeName
        projection.expansion.familyLevels) := by
    exact hfamilyLevels
  have hliftedParams : ∀ parameter ∈
      projection.expansion.params.map (fun parameter =>
        parameter.liftLooseBVars 0 generated.indexBinders.length),
      FVarsIn predicate parameter := by
    intro parameter hparameter
    simp only [List.mem_map] at hparameter
    rcases hparameter with ⟨source, hsource, rfl⟩
    rw [Expr.liftLooseBVars_eq]
    exact (hparams source hsource).liftLooseBVars
  have hmajorDomain : FVarsIn predicate
      (mkAppN
        (.const projection.expansion.typeName
          projection.expansion.familyLevels)
        ((projection.expansion.params.map fun parameter =>
            parameter.liftLooseBVars 0 generated.indexBinders.length) ++
          projectionBoundVars generated.indexBinders.length).toArray) := by
    apply FVarsIn.mkAppN hfamilyConst
    intro argument hargument
    simp only [List.toList_toArray, List.mem_append] at hargument
    rcases hargument with hargument | hargument
    · exact hliftedParams argument hargument
    · exact projectionBoundVars_fvarsIn _ argument hargument
  have hmotive : FVarsIn predicate
      (wrapProjectionLambdas
        (generated.indexBinders ++ [{
          name := `_major
          domain := mkAppN
            (.const projection.expansion.typeName
              projection.expansion.familyLevels)
            ((projection.expansion.params.map fun parameter =>
                parameter.liftLooseBVars 0 generated.indexBinders.length) ++
              projectionBoundVars generated.indexBinders.length).toArray
          info := .default }])
        (abstractProjectionPatterns
          (projection.expansion.indices ++ [projection.expansion.struct])
          projection.type)) := by
    apply wrapProjectionLambdas_fvarsIn
    · intro binder hbinder
      simp only [List.mem_append, List.mem_singleton] at hbinder
      rcases hbinder with hbinder | rfl
      · exact hindexDomains binder hbinder
      · exact hmajorDomain
    · exact abstractProjectionPatterns_fvarsIn _ _ _ htype
  have hminor : FVarsIn predicate
      (wrapProjectionLambdas generated.fieldBinders
        (.bvar (projection.expansion.numFields -
          projection.expansion.index - 1))) := by
    exact wrapProjectionLambdas_fvarsIn hfieldDomains trivial
  rw [generated.exact]
  apply FVarsIn.mkAppN
  · intro level hlevel
    simp only [List.mem_cons] at hlevel
    rcases hlevel with rfl | hlevel
    · exact hresultLevel
    · exact hfamilyLevels level hlevel
  · intro argument hargument
    simp only [List.toList_toArray, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hargument
    rcases hargument with ((hparameter | hmotiveArgument) | hindex) |
        hstructArgument | hminorArgument
    · exact hparams argument hparameter
    · simpa [hmotiveArgument] using hmotive
    · exact hindices argument hindex
    · simpa [hstructArgument] using hstruct
    · simpa [hminorArgument] using hminor

/-- Every recursive projection inserted by a dependent selected-field prefix
has a strictly smaller field index than the requested projection. -/
theorem ProjectionFieldResult.projectionPositions_lt
    (trace : ProjectionFieldResult typeName struct position remaining type) :
    ∀ inserted ∈ trace.projectionPositions,
      position ≤ inserted ∧ inserted < position + remaining := by
  induction trace with
  | nil => simp [ProjectionFieldResult.projectionPositions]
  | dependent position remaining type name domain body info tail ih =>
      intro inserted hinserted
      simp only [ProjectionFieldResult.projectionPositions,
        List.mem_cons] at hinserted
      rcases hinserted with rfl | htail
      · omega
      · have := ih inserted htail
        omega
  | independent position remaining type name domain body info tail ih =>
      intro inserted hinserted
      have := ih inserted hinserted
      omega

theorem ProjectionExpansion.projectionPositions_lt_index
    (expansion : ProjectionExpansion) :
    ∀ inserted ∈ expansion.fieldResult.projectionPositions,
      inserted < expansion.index := by
  intro inserted hinserted
  simpa using expansion.fieldResult.projectionPositions_lt inserted hinserted

/-- Reverse-instantiating above an arbitrary closed pattern spine removes
exactly the size of that spine.  The values are irrelevant until one of the
canonical pattern slots is selected. -/
theorem projection_instantiateRevList_bvar_ge
    (patterns : List Expr) (depth offset : Nat) :
    (Expr.bvar (depth + offset + patterns.length)).instantiateRevList
        patterns depth = .bvar (depth + offset) := by
  induction patterns generalizing offset with
  | nil => simp
  | cons pattern patterns ih =>
      simp only [List.length_cons, Expr.instantiateRevList]
      rw [show depth + offset + (patterns.length + 1) =
          depth + (offset + 1) + patterns.length by omega]
      rw [ih (offset + 1)]
      simp [Expr.instantiate1']

/-- Reverse-instantiating does not affect a variable below the pattern
abstraction depth. -/
theorem projection_instantiateRevList_bvar_lt
    (patterns : List Expr) (index depth : Nat) (hindex : index < depth) :
    (Expr.bvar index).instantiateRevList patterns depth = .bvar index := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns ih =>
      simp only [Expr.instantiateRevList, ih]
      simp [Expr.instantiate1', hindex]

/-- The bound-variable ordinal assigned to a closed pattern reopens to that
same pattern. -/
theorem projection_instantiateRevList_bvar_getElem
    (patterns : List Expr) (index depth : Nat)
    (hindex : index < patterns.length)
    (hclosed : ∀ pattern ∈ patterns, Closed pattern) :
    (Expr.bvar (depth + (patterns.length - 1 - index))).instantiateRevList
        patterns depth = patterns[index] := by
  induction patterns generalizing index with
  | nil => simp at hindex
  | cons pattern patterns ih =>
      cases index with
      | zero =>
          simp only [List.length_cons, Nat.sub_zero,
            Expr.instantiateRevList, List.getElem_cons_zero]
          rw [show depth + (patterns.length + 1 - 1) =
              depth + 0 + patterns.length by omega]
          rw [projection_instantiateRevList_bvar_ge]
          have hpattern := hclosed pattern (by simp)
          simp [Expr.instantiate1',
            Expr.liftLooseBVars_eq_self hpattern.looseBVarRange_le]
      | succ index =>
          have hindex' : index < patterns.length := by simpa using hindex
          simp only [List.length_cons, Expr.instantiateRevList,
            List.getElem_cons_succ]
          rw [show depth + (patterns.length + 1 - 1 - (index + 1)) =
              depth + (patterns.length - 1 - index) by omega]
          rw [ih index hindex' (fun current hcurrent =>
            hclosed current (by simp [hcurrent]))]
          have hselected : Closed patterns[index] :=
            hclosed patterns[index] (by simp [List.getElem_mem hindex'])
          have hselectedRange : patterns[index].looseBVarRange' ≤ depth := by
            have := hselected.looseBVarRange_le
            omega
          rw [Expr.instantiate1'_eq_self hselectedRange]

theorem projectionPattern_found
    (hfind : patterns.findIdx? (fun pattern => expression == pattern) =
      some index)
    (hpatterns : ∀ pattern ∈ patterns, Closed pattern) :
    (Expr.bvar (depth + (patterns.length - index - 1))).instantiateRevList
        patterns depth == expression := by
  have hdata := List.findIdx?_eq_some_iff_getElem.mp hfind
  rw [show patterns.length - index - 1 =
      patterns.length - 1 - index by omega]
  rw [projection_instantiateRevList_bvar_getElem patterns index depth
    hdata.1 hpatterns]
  exact BEq.symm hdata.2.1

/-- Reopening transparent projection-pattern abstraction with the same
closed pattern spine recovers the source expression up to Lean expression
equivalence.  This is the cancellation fact unavailable for opaque
`Expr.abstract`. -/
theorem abstractProjectionPatterns_instantiateRevList
    (hclosed : Closed expression depth)
    (hpatterns : ∀ pattern ∈ patterns, Closed pattern) :
    (abstractProjectionPatterns patterns expression depth).instantiateRevList
        patterns depth == expression := by
  induction expression generalizing depth with
  | bvar index =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth) (expression := .bvar index)
          (by assumption) hpatterns
      · rename_i hfind
        simp only
        change index < depth at hclosed
        rw [if_pos hclosed]
        rw [projection_instantiateRevList_bvar_lt patterns index depth hclosed]
        exact Expr.eqv_refl _
  | fvar id =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth) (expression := .fvar id)
          (by assumption) hpatterns
      · rw [Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])]
        exact Expr.eqv_refl _
  | mvar id => simp [Closed] at hclosed
  | sort level =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth) (expression := .sort level)
          (by assumption) hpatterns
      · rw [Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])]
        exact Expr.eqv_refl _
  | const name levels =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth)
          (expression := .const name levels) (by assumption) hpatterns
      · rw [Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])]
        exact Expr.eqv_refl _
  | lit literal =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth) (expression := .lit literal)
          (by assumption) hpatterns
      · rw [Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])]
        exact Expr.eqv_refl _
  | app fn argument ihFn ihArgument =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth)
          (expression := .app fn argument) (by assumption) hpatterns
      · simp only [Expr.instantiateRevList_app]
        exact Expr.app_eqv (ihFn hclosed.1)
          (ihArgument hclosed.2)
  | lam name domain body info ihDomain ihBody =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth)
          (expression := .lam name domain body info) (by assumption) hpatterns
      · simp only [Expr.instantiateRevList_lam]
        exact Expr.lam_eqv (ihDomain hclosed.1)
          (ihBody hclosed.2)
  | forallE name domain body info ihDomain ihBody =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth)
          (expression := .forallE name domain body info) (by assumption) hpatterns
      · simp only [Expr.instantiateRevList_forallE]
        exact Expr.forallE_eqv (ihDomain hclosed.1)
          (ihBody hclosed.2)
  | letE name type value body nondep ihType ihValue ihBody =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth)
          (expression := .letE name type value body nondep) (by assumption) hpatterns
      · simp only [Expr.instantiateRevList_letE]
        exact Expr.letE_eqv (ihType hclosed.1)
          (ihValue hclosed.2.1) (ihBody hclosed.2.2)
  | mdata data body ihBody =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth)
          (expression := .mdata data body) (by assumption) hpatterns
      · simp only [Expr.instantiateRevList_mdata]
        exact Expr.mdata_eqv data (ihBody hclosed)
  | proj name index body ihBody =>
      unfold abstractProjectionPatterns
      split
      · exact projectionPattern_found (depth := depth)
          (expression := .proj name index body) (by assumption) hpatterns
      · simp only [Expr.instantiateRevList_proj]
        exact Expr.proj_eqv (ihBody hclosed)

/-- Fully explicit structural specification of a canonical projection shell.
It contains no typing assertion: ordinary checked inference supplies that
separately after this syntax has passed the executable parser. -/
structure ProjectionShell.WF (expansion : ProjectionExpansion)
    (candidate : Expr)
    (shell : ProjectionShell expansion.numFields expansion.index) : Prop where
  head : candidate.getAppFn =
    .const (mkCasesOnName expansion.typeName)
      (shell.resultLevel :: expansion.familyLevels)
  arguments : candidate.getAppArgs.toList =
    expansion.params ++ [shell.motive] ++ expansion.indices ++
      [expansion.struct, shell.minor]
  minor : LambdaTelescope shell.fieldDomains shell.minor
    (.bvar (expansion.numFields - expansion.index - 1))
  fieldCount : shell.fieldDomains.length = expansion.numFields

/-- Structural, proof-level projection-freeness.  This is the trusted meaning
of the executable boolean gate, and contains no projection case. -/
inductive ProjectionFree : Expr → Prop
  | bvar : ProjectionFree (.bvar index)
  | fvar : ProjectionFree (.fvar fvarId)
  | mvar : ProjectionFree (.mvar mvarId)
  | sort : ProjectionFree (.sort level)
  | const : ProjectionFree (.const name levels)
  | lit : ProjectionFree (.lit literal)
  | app : ProjectionFree fn → ProjectionFree arg →
      ProjectionFree (.app fn arg)
  | lam : ProjectionFree domain → ProjectionFree body →
      ProjectionFree (.lam name domain body bi)
  | forallE : ProjectionFree domain → ProjectionFree body →
      ProjectionFree (.forallE name domain body bi)
  | letE : ProjectionFree type → ProjectionFree value →
      ProjectionFree body →
      ProjectionFree (.letE name type value body nondep)
  | mdata : ProjectionFree body → ProjectionFree (.mdata data body)

theorem projectionFree_sound
    (H : projectionFree expression = true) : ProjectionFree expression := by
  induction expression with
  | bvar => exact .bvar
  | fvar => exact .fvar
  | mvar => exact .mvar
  | sort => exact .sort
  | const => exact .const
  | lit => exact .lit
  | app fn arg ihFn ihArg =>
      simp [projectionFree] at H
      exact .app (ihFn H.1) (ihArg H.2)
  | lam name domain body bi ihDomain ihBody =>
      simp [projectionFree] at H
      exact .lam (ihDomain H.1) (ihBody H.2)
  | forallE name domain body bi ihDomain ihBody =>
      simp [projectionFree] at H
      exact .forallE (ihDomain H.1) (ihBody H.2)
  | letE name type value body nondep ihType ihValue ihBody =>
      simp [projectionFree] at H
      exact .letE (ihType H.1.1) (ihValue H.1.2) (ihBody H.2)
  | mdata data body ih =>
      exact .mdata (ih H)
  | proj => simp [projectionFree] at H

theorem ProjectionFree.check (H : ProjectionFree expression) :
    projectionFree expression = true := by
  induction H <;> simp [projectionFree, *]

theorem projectionFree_iff :
    projectionFree expression = true ↔ ProjectionFree expression :=
  ⟨projectionFree_sound, ProjectionFree.check⟩

namespace ProjectionCertificate

theorem minor (certificate : ProjectionCertificate) :
    LambdaTelescope certificate.shell.fieldDomains certificate.shell.minor
        (.bvar (certificate.projection.expansion.numFields -
          certificate.projection.expansion.index - 1)) ∧
      certificate.shell.fieldDomains.length =
        certificate.projection.expansion.numFields :=
  projectionMinorDomains_sound certificate.shell.minorRun

end ProjectionCertificate

end Lean4Lean.TypeChecker.Inner
