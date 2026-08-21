import Lean4Lean.Verify.Inductive.Recursor.RecursiveCalls

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Operational alpha/locality boundary for the higher-order field replay.
The constructor decision traces ensure that both `loopUArgs` runs inspect the
same selected ordinal of the same source telescope; simultaneous abstraction
then removes the unrelated fresh identifiers allocated by the two passes.
The resulting single equality retains the owner, higher-order arity and
normalized local telescope, abstracted motive head, and exposed index spine
needed to compare an installed induction hypothesis with its generated
recursive result. -/
def RecursorLoopUArgsReplayCompat : Prop :=
  ∀ (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (indTypes : Array InductiveType) (motives minors : Array Expr)
    (lvls : List Level)
    (root₁ root₂ current₁ current₂ originRoot :
      AddInductive.Context)
    (source terminal₁ terminal₂ : Expr)
    (all₁ recursive₁ all₂ recursive₂ : Array Expr)
    (positions₁ positions₂ : List Nat)
    (j : Nat) (hj₁ : j < recursive₁.size)
    (hj₂ : j < recursive₂.size)
    (sourceType value : Expr)
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos originRoot
      recursive₁[j]! sourceType)
    (G : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      current₂ recursive₂[j] value)
    (fieldBinders₁ fieldBinders₂ : List FVarId),
    source.FVarsIn (· ∈ root₁.lctx.fvars) →
    RecursorFieldDecisions stats root₁ source current₁ terminal₁
      all₁ recursive₁ positions₁ →
    RecursorFieldDecisions stats root₂ source current₂ terminal₂
      all₂ recursive₂ positions₂ →
    all₁ = (fieldBinders₁.map Expr.fvar).toArray →
    all₂ = (fieldBinders₂.map Expr.fvar).toArray →
    positions₁ = positions₂ →
    O.replayTrace fieldBinders₁ = G.replayTrace fieldBinders₂

/-- Rule-level abstraction turns the selected field free variable into its
outer de Bruijn index beneath the generated call's local lambda binders. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedMajor_eq_bvar
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders) :
    ∃ fieldVar,
      fieldVar < binders.length ∧
      (Expr.fvar fv).abstractList binders = .bvar fieldVar ∧
      H.outerAbstractedMajor binders =
        mkAppN (.bvar (H.localArgs.size + fieldVar))
          (H.localIndices.map Expr.bvar).toArray := by
  rcases List.mem_iff_getElem.mp hfield with ⟨i, hi, hget⟩
  let fieldVar := binders.length - 1 - i
  have hfresh : fv ∉ H.arguments_bound.fvars := by
    intro hmem
    exact H.arguments_bound.fresh fv hmem hfieldRoot
  have hfieldLocal :
      (Expr.fvar fv).abstractList H.arguments_bound.fvars = .fvar fv :=
    Expr.abstractList_fvar_of_not_mem hfresh
  have hlocalSize : H.localArgs.size = H.arguments_bound.fvars.length := by
    have := congrArg Array.size H.arguments_bound.expressions
    simpa using this
  have hfieldOuter := Expr.abstractList_fvar_getElem
    hbinders i hi (k := H.localArgs.size)
  rw [hget] at hfieldOuter
  have hfieldOuter' :
      (Expr.fvar fv).abstractList binders H.localArgs.size =
        .bvar (H.localArgs.size + fieldVar) := by
    simpa [fieldVar] using hfieldOuter
  have hfieldBase := Expr.abstractList_fvar_getElem
    hbinders i hi (k := 0)
  rw [hget] at hfieldBase
  have hfieldBase' : (Expr.fvar fv).abstractList binders =
      .bvar fieldVar := by
    simpa [fieldVar] using hfieldBase
  have hsourceArgs :
      (List.ofFn fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar (H.arguments_bound.fvars.length - 1 - i)) =
      H.localIndices.map Expr.bvar := by
    simp [BoundGeneratedRecursiveCall.localIndices,
      List.map_ofFn, Function.comp_def]
  refine ⟨fieldVar, by omega, hfieldBase', ?_⟩
  unfold BoundGeneratedRecursiveCall.outerAbstractedMajor
    BoundGeneratedRecursiveCall.abstractedMajor
  rw [Expr.abstractList_mkAppN, hfieldLocal, hfieldOuter']
  apply congrArg (mkAppN (.bvar (H.localArgs.size + fieldVar)))
  rw [hsourceArgs]
  apply Array.ext
  · simp
  · intro j hjLeft hjRight
    simp only [Array.getElem_map, List.getElem_toArray,
      List.getElem_map]
    apply Expr.abstractList_bvar_lt
    have hj : j < H.localIndices.length := by simpa using hjRight
    have hj' : j < H.arguments_bound.fvars.length := by
      simpa [BoundGeneratedRecursiveCall.localIndices] using hj
    simp only [BoundGeneratedRecursiveCall.localIndices,
      List.getElem_ofFn]
    omega

/-- Dependent array-selection wrapper for
`outerAbstractedMajor_eq_bvar`. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedMajor_eq_bvar_of_field_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldEq : field = .fvar fv)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders) :
    ∃ fieldVar,
      fieldVar < binders.length ∧
      (Expr.fvar fv).abstractList binders = .bvar fieldVar ∧
      H.outerAbstractedMajor binders =
        mkAppN (.bvar (H.localArgs.size + fieldVar))
          (H.localIndices.map Expr.bvar).toArray := by
  subst field
  exact H.outerAbstractedMajor_eq_bvar hfieldRoot hbinders hfield

/-- Positional form of `outerAbstractedMajor_eq_bvar_of_field_eq`. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedMajor_eq_bvar_at
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldEq : field = .fvar fv)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup) (hi : i < binders.length)
    (hget : binders[i] = fv) :
    H.outerAbstractedMajor binders =
      mkAppN (.bvar (H.localArgs.size + (binders.length - 1 - i)))
        (H.localIndices.map Expr.bvar).toArray := by
  have hmem : fv ∈ binders := by
    rw [← hget]
    exact List.getElem_mem hi
  rcases H.outerAbstractedMajor_eq_bvar_of_field_eq hfieldEq hfieldRoot
      hbinders hmem with
    ⟨fieldVar, _hfieldVar, habstract, houter⟩
  have hexact := Expr.abstractList_fvar_getElem hbinders i hi (k := 0)
  rw [hget] at hexact
  have hfieldVarExact : fieldVar = binders.length - 1 - i := by
    have hexact' : (Expr.fvar fv).abstractList binders =
        .bvar (binders.length - 1 - i) := by
      simpa only [Nat.zero_add] using hexact
    exact Expr.bvar.inj (habstract.symm.trans hexact')
  simpa [hfieldVarExact] using houter

theorem BoundGeneratedRecursiveCall.outerAbstractedMajorAvoids
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders) :
    (H.outerAbstractedMajor binders).AvoidsConsts names := by
  rcases H.outerAbstractedMajor_eq_bvar hfieldRoot hbinders hfield with
    ⟨fieldVar, _hfieldVar, _hfieldSource, hsource⟩
  rw [hsource]
  apply Lean.Expr.AvoidsConsts.mkAppN
  · exact .bvar _
  · intro arg harg
    rcases Array.mem_iff_getElem.mp harg with ⟨i, hi, heq⟩
    rw [← heq]
    simp only [List.getElem_toArray, List.getElem_map]
    exact .bvar _

theorem BoundGeneratedRecursiveCall.abstractedBody_eq_named
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    H.body.abstractList H.arguments_bound.fvars =
      H.abstractedRecursor.app H.abstractedMajor := by
  simpa [BoundGeneratedRecursiveCall.abstractedRecursor,
    BoundGeneratedRecursiveCall.abstractedMajor,
    BoundGeneratedRecursiveCall.recursorName] using H.abstractedBody_eq

theorem BoundGeneratedRecursiveCall.outerAbstractedBody_eq_named
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    (H.body.abstractList H.arguments_bound.fvars).abstractList
        binders H.localArgs.size =
      (H.outerAbstractedRecursor binders).app
        (H.outerAbstractedMajor binders) := by
  rw [H.abstractedBody_eq_named]
  exact Expr.abstractList_app

theorem BoundGeneratedRecursiveCall.abstractedRecursor_head
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    H.abstractedRecursor.getAppFn = .const H.recursorName lvls := by
  have getAppFn_mkAppN : ∀ (fn : Expr) (args : Array Expr),
      (mkAppN fn args).getAppFn = fn.getAppFn := by
    intro fn args
    unfold mkAppN
    rw [← Array.foldl_toList]
    generalize args.toList = list
    induction list generalizing fn with
    | nil => rfl
    | cons arg args ih =>
      simp only [List.foldl_cons]
      simpa [Expr.getAppFn] using ih (.app fn arg)
  simp only [BoundGeneratedRecursiveCall.abstractedRecursor]
  repeat' rw [getAppFn_mkAppN]
  rfl

theorem BoundGeneratedRecursiveCall.outerAbstractedRecursor_head
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value) :
    (H.outerAbstractedRecursor binders).getAppFn =
      .const H.recursorName lvls := by
  have getAppFn_mkAppN : ∀ (fn : Expr) (args : Array Expr),
      (mkAppN fn args).getAppFn = fn.getAppFn := by
    intro fn args
    unfold mkAppN
    rw [← Array.foldl_toList]
    generalize args.toList = list
    induction list generalizing fn with
    | nil => rfl
    | cons arg args ih =>
      simp only [List.foldl_cons]
      simpa [Expr.getAppFn] using ih (.app fn arg)
  simp only [BoundGeneratedRecursiveCall.outerAbstractedRecursor,
    BoundGeneratedRecursiveCall.abstractedRecursor,
    Expr.abstractList_mkAppN]
  repeat' rw [getAppFn_mkAppN]
  simp [Expr.getAppFn]

/-- Every non-head argument of the generated recursor spine predates the
recursor declaration. Parameters, motives, and minors are supplied by their
bound-variable certificates; indices are subexpressions of the retained
pre-installation exposed type. -/
theorem SemanticBoundGeneratedRecursiveCall.outerAbstractedRecursorArgsAvoids
    (H : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value)
    (hfresh : ∀ name ∈ names, R.venv.constants name = none)
    (hparams : ∀ arg ∈ stats.params, arg.AvoidsConsts names)
    (hmotives : ∀ arg ∈ motives, arg.AvoidsConsts names)
    (hminors : ∀ arg ∈ minors, arg.AvoidsConsts names)
    (binders : List FVarId) :
    ∀ arg ∈ (H.generated.outerAbstractedRecursor binders).getAppArgsList,
      arg.AvoidsConsts names := by
  have hcurrentFresh : ∀ name ∈ names,
      H.current_context.venv.constants name = none := by
    intro name hname
    rw [H.recent.venv_eq]
    exact hfresh name hname
  have hexposed : H.generated.exposedType.AvoidsConsts names :=
    checkPositivityStep.TrExprS.sourceAvoidsFresh hcurrentFresh
      H.exposed_translation
  intro arg harg
  unfold BoundGeneratedRecursiveCall.outerAbstractedRecursor at harg
  rw [Expr.getAppArgsList_abstractList H.generated.abstractedRecursor
    binders H.generated.localArgs.size] at harg
  rcases List.mem_map.mp harg with ⟨base, hbase, rfl⟩
  apply Lean.Expr.AvoidsConsts.abstractList
  unfold BoundGeneratedRecursiveCall.abstractedRecursor at hbase
  simp only [Expr.getAppArgsList_mkAppN, Expr.getAppArgsList_const,
    List.nil_append, Array.toList_map, List.append_assoc] at hbase
  rcases List.mem_append.mp hbase with hparam | hrest
  · rcases List.mem_map.mp hparam with ⟨source, hsource, rfl⟩
    exact (hparams source (Array.mem_toList_iff.mp hsource)).abstractList
      H.generated.arguments_bound.fvars
  · rcases List.mem_append.mp hrest with hmotive | hrest
    · rcases List.mem_map.mp hmotive with ⟨source, hsource, rfl⟩
      exact (hmotives source (Array.mem_toList_iff.mp hsource)).abstractList
        H.generated.arguments_bound.fvars
    · rcases List.mem_append.mp hrest with hminor | hindices
      · rcases List.mem_map.mp hminor with ⟨source, hsource, rfl⟩
        exact (hminors source (Array.mem_toList_iff.mp hsource)).abstractList
          H.generated.arguments_bound.fvars
      · rcases List.mem_map.mp hindices with ⟨source, hsource, rfl⟩
        have hsourceArray : source ∈
            (AddInductive.getIIndices stats H.generated.exposedType).2 :=
          Array.mem_toList_iff.mp hsource
        unfold AddInductive.getIIndices at hsourceArray
        change source ∈
          (H.generated.exposedType.getAppArgs.toSubarray
            stats.params.size).toArray at hsourceArray
        let sub := H.generated.exposedType.getAppArgs.toSubarray
          stats.params.size
        have hsourceSubArray : source ∈ sub.toArray := by
          simpa [sub] using hsourceArray
        have hsourceArrayList : source ∈ sub.toArray.toList :=
          Array.mem_toList_iff.mpr hsourceSubArray
        have hsub : source ∈
            (H.generated.exposedType.getAppArgs.toSubarray
              stats.params.size).toList := by
          rw [← Subarray.toList_toArray]
          simpa [sub] using hsourceArrayList
        rw [Subarray.toList_eq_drop_take,
          Array.array_toSubarray] at hsub
        have htake := List.mem_of_mem_drop hsub
        have hfull : source ∈
            H.generated.exposedType.getAppArgs.toList :=
          List.mem_of_mem_take htake
        have hfullList : source ∈
            H.generated.exposedType.getAppArgsList := by
          rw [← Expr.getAppArgs_toList]
          exact hfull
        exact (hexposed.getAppArgsList hfullList).abstractList
          H.generated.arguments_bound.fvars

/-- Exact translation of the generated major premise for a selected field
free variable. Outer translations are shifted under the generated lambdas;
the newly opened arguments translate to their canonical de Bruijn variables. -/
theorem BoundGeneratedRecursiveCall.translatedMajor_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (henv : env.Ordered)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (Hfield : TrExprS env Us Δ (.fvar fv) recursiveArg)
    (hdomains : domains.length = H.localArgs.size)
    (Hmajor : TrExprS env Us (abstractForallContext domains Δ)
      H.abstractedMajor major) :
    major = VExpr.mkApps (recursiveArg.liftN domains.length 0)
      (H.localIndices.map VExpr.bvar) := by
  have hfresh : fv ∉ H.arguments_bound.fvars := by
    intro hmem
    exact H.arguments_bound.fresh fv hmem hfieldRoot
  have hfieldAbstract :
      (Expr.fvar fv).abstractList H.arguments_bound.fvars = .fvar fv :=
    Expr.abstractList_fvar_of_not_mem hfresh
  have hlocalSize :
      H.localArgs.size = H.arguments_bound.fvars.length := by
    have := congrArg Array.size H.arguments_bound.expressions
    simpa using this
  have hindexBound : ∀ i ∈ H.localIndices, i < domains.length := by
    intro i hi
    simp only [BoundGeneratedRecursiveCall.localIndices,
      List.mem_ofFn] at hi
    rcases hi with ⟨j, rfl⟩
    omega
  have HfieldWeak : TrExprS env Us (abstractForallContext domains Δ)
      (.fvar fv) (recursiveArg.liftN domains.length 0) := by
    have Hweak := Hfield.weakBV henv
      (abstractForallContext.bvLift domains Δ)
    simpa [Expr.liftLooseBVars'] using Hweak
  have Hmajor' := Hmajor
  have hsourceArgs :
      (List.ofFn fun i : Fin H.arguments_bound.fvars.length =>
        Expr.bvar (H.arguments_bound.fvars.length - 1 - i)) =
      H.localIndices.map Expr.bvar := by
    simp [BoundGeneratedRecursiveCall.localIndices,
      List.map_ofFn, Function.comp_def]
  unfold BoundGeneratedRecursiveCall.abstractedMajor at Hmajor'
  rw [hfieldAbstract] at Hmajor'
  unfold mkAppN at Hmajor'
  rw [← Array.foldl_toList] at Hmajor'
  rw [List.toList_toArray] at Hmajor'
  rw [hsourceArgs, List.foldl_map] at Hmajor'
  change TrExprS env Us (abstractForallContext domains Δ)
    (H.localIndices.foldl (fun fn i => .app fn (.bvar i)) (.fvar fv))
      major at Hmajor'
  have heq := TrExprS.foldl_bvars_eq domains Δ H.localIndices
    hindexBound (.fvar fv) (recursiveArg.liftN domains.length 0)
    (fun out Hout => TrExprS.unique (e := (.fvar fv))
      (by trivial) Hout HfieldWeak) Hmajor'
  simpa [VExpr.mkApps, List.foldl_map] using heq

theorem BoundGeneratedRecursiveCall.translatedMajor_isField
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (henv : env.Ordered)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (Hfield : TrExprS env Us Δ (.fvar fv) recursiveArg)
    (hfield : recursiveArg.IsFieldApp fieldVars 0)
    (hdomains : domains.length = H.localArgs.size)
    (Hmajor : TrExprS env Us (abstractForallContext domains Δ)
      H.abstractedMajor major) :
    major.IsFieldApp fieldVars domains.length := by
  rw [H.translatedMajor_eq henv hfieldRoot Hfield hdomains Hmajor]
  simpa using VExpr.IsFieldApp.appendApps
    (VExpr.IsFieldApp.lift hfield domains.length)
      (H.localIndices.map VExpr.bvar)

/-- A translated major premise in a closed rule has a completely forced
target: the selected outer field variable, shifted beneath the generated
higher-order arguments, applied to their canonical de Bruijn spine.  This is
the exact-target strengthening of `translatedOuterAbstractedMajor_isField`;
it needs no typing reconstruction because that information is already
contained in the supplied strict translation. -/
theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedMajor_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders)
    (hruleDomains : ruleDomains.length = binders.length)
    (hlocalDomains : localDomains.length = H.localArgs.size)
    (Hmajor : TrExprS env Us
      (abstractForallContext localDomains
        (abstractForallContext ruleDomains Δ))
      (H.outerAbstractedMajor binders) major) :
    ∃ fieldVar,
      fieldVar < ruleDomains.length ∧
      (Expr.fvar fv).abstractList binders = .bvar fieldVar ∧
      major = VExpr.mkApps (.bvar (localDomains.length + fieldVar))
        (H.localIndices.map VExpr.bvar) := by
  rcases H.outerAbstractedMajor_eq_bvar hfieldRoot hbinders hfield with
    ⟨fieldVar, hfieldVar, hfieldSource, hsource⟩
  rw [hsource] at Hmajor
  have Hmajor' : TrExprS env Us
      (abstractForallContext (ruleDomains ++ localDomains) Δ)
      (mkAppN (.bvar (H.localArgs.size + fieldVar))
        (H.localIndices.map Expr.bvar).toArray) major := by
    simpa using Hmajor
  unfold mkAppN at Hmajor'
  rw [← Array.foldl_toList, List.toList_toArray,
    List.foldl_map] at Hmajor'
  have htotal : H.localArgs.size + fieldVar <
      (ruleDomains ++ localDomains).length := by
    simp only [List.length_append]
    omega
  have hindices : ∀ index ∈ H.localIndices,
      index < (ruleDomains ++ localDomains).length := by
    intro index hindex
    simp only [BoundGeneratedRecursiveCall.localIndices,
      List.mem_ofFn] at hindex
    rcases hindex with ⟨j, rfl⟩
    simp only [List.length_append]
    have hlocalSize : H.localArgs.size =
        H.arguments_bound.fvars.length := by
      have := congrArg Array.size H.arguments_bound.expressions
      simpa using this
    omega
  have hmajorEq := TrExprS.foldl_bvars_eq
    (ruleDomains ++ localDomains) Δ H.localIndices hindices
    (.bvar (H.localArgs.size + fieldVar))
    (.bvar (H.localArgs.size + fieldVar))
    (fun out Hout => TrExprS.bvar_eq_of_abstractForallContext
      Hout htotal) Hmajor'
  have hmajorEq' : major =
      VExpr.mkApps (.bvar (H.localArgs.size + fieldVar))
        (H.localIndices.map VExpr.bvar) := by
    simpa [VExpr.mkApps, List.foldl_map] using hmajorEq
  refine ⟨fieldVar, ?_, hfieldSource, ?_⟩
  · omega
  · simpa [hlocalDomains] using hmajorEq'

/-- Equality-parametric wrapper for array-selected fields.  Keeping the
generated-call witness at its original dependent array index avoids rewriting
the semantic payload merely to expose that the selected expression is a free
variable. -/
theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedMajor_eq_of_field_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldEq : field = .fvar fv)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders)
    (hruleDomains : ruleDomains.length = binders.length)
    (hlocalDomains : localDomains.length = H.localArgs.size)
    (Hmajor : TrExprS env Us
      (abstractForallContext localDomains
        (abstractForallContext ruleDomains Δ))
      (H.outerAbstractedMajor binders) major) :
    ∃ fieldVar,
      fieldVar < ruleDomains.length ∧
      (Expr.fvar fv).abstractList binders = .bvar fieldVar ∧
      major = VExpr.mkApps (.bvar (localDomains.length + fieldVar))
        (H.localIndices.map VExpr.bvar) := by
  subst field
  exact H.translatedOuterAbstractedMajor_eq hfieldRoot hbinders hfield
    hruleDomains hlocalDomains Hmajor

/-- The major premise in a closed rule is a designated outer field shifted
beneath exactly the generated call's local lambda domains. -/
theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedMajor_isField
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders)
    (hruleDomains : ruleDomains.length = binders.length)
    (hlocalDomains : localDomains.length = H.localArgs.size)
    (hfieldVars : ∀ fieldVar,
      (Expr.fvar fv).abstractList binders = .bvar fieldVar →
      fieldVar ∈ fieldVars)
    (Hmajor : TrExprS env Us
      (abstractForallContext localDomains
        (abstractForallContext ruleDomains Δ))
      (H.outerAbstractedMajor binders) major) :
    major.IsFieldApp fieldVars localDomains.length := by
  rcases H.outerAbstractedMajor_eq_bvar hfieldRoot hbinders hfield with
    ⟨fieldVar, hfieldVar, hfieldSource, hsource⟩
  rw [hsource] at Hmajor
  have Hmajor' : TrExprS env Us
      (abstractForallContext (ruleDomains ++ localDomains) Δ)
      (mkAppN (.bvar (H.localArgs.size + fieldVar))
        (H.localIndices.map Expr.bvar).toArray) major := by
    simpa using Hmajor
  unfold mkAppN at Hmajor'
  rw [← Array.foldl_toList, List.toList_toArray,
    List.foldl_map] at Hmajor'
  have htotal : H.localArgs.size + fieldVar <
      (ruleDomains ++ localDomains).length := by
    simp only [List.length_append]
    omega
  have hindices : ∀ index ∈ H.localIndices,
      index < (ruleDomains ++ localDomains).length := by
    intro index hindex
    simp only [BoundGeneratedRecursiveCall.localIndices,
      List.mem_ofFn] at hindex
    rcases hindex with ⟨j, rfl⟩
    simp only [List.length_append]
    have hlocalSize : H.localArgs.size =
        H.arguments_bound.fvars.length := by
      have := congrArg Array.size H.arguments_bound.expressions
      simpa using this
    omega
  have hmajorEq := TrExprS.foldl_bvars_eq
    (ruleDomains ++ localDomains) Δ H.localIndices hindices
    (.bvar (H.localArgs.size + fieldVar))
    (.bvar (H.localArgs.size + fieldVar))
    (fun out Hout => TrExprS.bvar_eq_of_abstractForallContext
      Hout htotal) Hmajor'
  have hmajorEq' : major =
      VExpr.mkApps (.bvar (H.localArgs.size + fieldVar))
        (H.localIndices.map VExpr.bvar) := by
    simpa [VExpr.mkApps, List.foldl_map] using hmajorEq
  have hbase : (VExpr.bvar fieldVar).IsFieldApp fieldVars 0 := by
    refine ⟨fieldVar, hfieldVars fieldVar hfieldSource, [], ?_⟩
    rfl
  have hlift := VExpr.IsFieldApp.lift hbase localDomains.length
  have happ := VExpr.IsFieldApp.appendApps hlift
    (H.localIndices.map VExpr.bvar)
  rw [hmajorEq']
  simpa [hlocalDomains, Nat.add_comm, VExpr.liftN, liftVar] using happ

/-- Syntax-directed translation of a generated higher-order recursive call.
The semantic guard is intentionally not assumed here: initial arguments and
the major premise remain exposed with their exact translation derivations. -/
theorem BoundGeneratedRecursiveCall.translatedCallShape
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ value result) :
    ∃ domains levels init major,
      domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains
        (VExpr.mkApps (.const H.recursorName levels) (init ++ [major])) ∧
      lvls.mapM (VLevel.ofLevel Us) = some levels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        H.abstractedRecursor.getAppArgsList init ∧
      TrExprS env Us (abstractForallContext domains Δ)
        H.abstractedMajor major := by
  rcases H.translatedLambdaShape Htr with
    ⟨domains, residual, hdomains, hresult, hresidual⟩
  rw [H.abstractedBody_eq_named] at hresidual
  cases hresidual with
  | app _ _ hfn hmajor =>
    rename_i recursorResult domain codomain majorResult
      recursorType majorType
    rcases checkPositivityStep.TrExprS.constAppSpine
        hfn H.abstractedRecursor_head with
      ⟨levels, init, hspine, hlevels, hinit⟩
    have hrebuild := VExpr.mkApps_getAppFnArgs recursorResult
    rw [hspine] at hrebuild
    refine ⟨domains, levels, init, _, hdomains, ?_, hlevels, hinit,
      hmajor⟩
    rw [hresult]
    congr 1
    rw [← hrebuild]
    simp [VExpr.mkApps, List.foldl_append]

/-- Freshness-aware generated-call translation. Unlike freshness of the
complete result (which deliberately contains the new recursor), this retains
freshness exactly for the enclosing higher-order domains. -/
theorem BoundGeneratedRecursiveCall.translatedCallShape_noFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ value result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false) :
    ∃ domains levels init major,
      domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains
        (VExpr.mkApps (.const H.recursorName levels) (init ++ [major])) ∧
      lvls.mapM (VLevel.ofLevel Us) = some levels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        H.abstractedRecursor.getAppArgsList init ∧
      TrExprS env Us (abstractForallContext domains Δ)
        H.abstractedMajor major ∧
      ∀ dom ∈ domains, dom.containsAnyConst recursors = false := by
  rcases TrExprS.lambdaTelescope_shape_with_context_noFresh
      hfresh hctx hproj H.lambdaTelescope Htr with
    ⟨domains, residual, hdomains, hresult, hresidual, hfree⟩
  rw [H.abstractedBody_eq_named] at hresidual
  cases hresidual with
  | app _ _ hfn hmajor =>
    rename_i recursorResult domain codomain majorResult
      recursorType majorType
    rcases checkPositivityStep.TrExprS.constAppSpine
        hfn H.abstractedRecursor_head with
      ⟨levels, init, hspine, hlevels, hinit⟩
    have hrebuild := VExpr.mkApps_getAppFnArgs recursorResult
    rw [hspine] at hrebuild
    refine ⟨domains, levels, init, _, hdomains, ?_, hlevels, hinit,
      hmajor, hfree⟩
    rw [hresult]
    congr 1
    rw [← hrebuild]
    simp [VExpr.mkApps, List.foldl_append]

/-- Generated-call spine inversion for the form that occurs inside a closed
rule RHS, after simultaneous abstraction over the rule binders. -/
theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedCallShape
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ (value.abstractList binders) result) :
    ∃ domains levels init major,
      domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains
        (VExpr.mkApps (.const H.recursorName levels) (init ++ [major])) ∧
      lvls.mapM (VLevel.ofLevel Us) = some levels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        (H.outerAbstractedRecursor binders).getAppArgsList init ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.outerAbstractedMajor binders) major := by
  rcases H.translatedOuterAbstractedLambdaShape Htr with
    ⟨domains, residual, hdomains, hresult, hresidual⟩
  rw [H.outerAbstractedBody_eq_named] at hresidual
  cases hresidual with
  | app _ _ hfn hmajor =>
    rename_i recursorResult domain codomain majorResult
      recursorType majorType
    rcases checkPositivityStep.TrExprS.constAppSpine
        hfn H.outerAbstractedRecursor_head with
      ⟨levels, init, hspine, hlevels, hinit⟩
    have hrebuild := VExpr.mkApps_getAppFnArgs recursorResult
    rw [hspine] at hrebuild
    refine ⟨domains, levels, init, _, hdomains, ?_, hlevels, hinit,
      hmajor⟩
    rw [hresult]
    congr 1
    rw [← hrebuild]
    simp [VExpr.mkApps, List.foldl_append]

theorem BoundGeneratedRecursiveCall.translatedOuterAbstractedCallShape_noFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false) :
    ∃ domains levels init major,
      domains.length = H.localArgs.size ∧
      result = VExpr.wrapLams domains
        (VExpr.mkApps (.const H.recursorName levels) (init ++ [major])) ∧
      lvls.mapM (VLevel.ofLevel Us) = some levels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        (H.outerAbstractedRecursor binders).getAppArgsList init ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.outerAbstractedMajor binders) major ∧
      ∀ dom ∈ domains, dom.containsAnyConst recursors = false := by
  rcases H.translatedOuterAbstractedLambdaShape_noFresh
      Htr hfresh hctx hproj with
    ⟨domains, residual, hdomains, hresult, hresidual, hfree⟩
  rw [H.outerAbstractedBody_eq_named] at hresidual
  cases hresidual with
  | app _ _ hfn hmajor =>
    rename_i recursorResult domain codomain majorResult
      recursorType majorType
    rcases checkPositivityStep.TrExprS.constAppSpine
        hfn H.outerAbstractedRecursor_head with
      ⟨levels, init, hspine, hlevels, hinit⟩
    have hrebuild := VExpr.mkApps_getAppFnArgs recursorResult
    rw [hspine] at hrebuild
    refine ⟨domains, levels, init, _, hdomains, ?_, hlevels, hinit,
      hmajor, hfree⟩
    rw [hresult]
    congr 1
    rw [← hrebuild]
    simp [VExpr.mkApps, List.foldl_append]

/-- Stage-correct call-spine inversion for a semantically retained call.
The complete translation may see the newly installed recursor, while the
lambda-domain freshness follows from the retained pre-installation source
telescope. -/
theorem SemanticBoundGeneratedRecursiveCall.translatedOuterAbstractedCallShape
    (H : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value)
    (Htr : TrExprS env Us Delta (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, R.venv.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Delta)
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false) :
    ∃ domains levels init major,
      domains.length = H.generated.localArgs.size ∧
      result = VExpr.wrapLams domains
        (VExpr.mkApps (.const H.generated.recursorName levels)
          (init ++ [major])) ∧
      lvls.mapM (VLevel.ofLevel Us) = some levels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Delta))
        (H.generated.outerAbstractedRecursor binders).getAppArgsList init ∧
      TrExprS env Us (abstractForallContext domains Delta)
        (H.generated.outerAbstractedMajor binders) major ∧
      ∀ dom ∈ domains, dom.containsAnyConst recursors = false := by
  rcases TrExprS.avoidingLambdaTelescope_shape_with_context
      (H.outerAvoidingLambdaTelescope hfresh binders) hctx hproj Htr with
    ⟨domains, residual, hdomains, hresult, hresidual, hfree⟩
  rw [H.generated.outerAbstractedBody_eq_named] at hresidual
  cases hresidual with
  | app _ _ hfn hmajor =>
    rename_i recursorResult domain codomain majorResult
      recursorType majorType
    rcases checkPositivityStep.TrExprS.constAppSpine
        hfn H.generated.outerAbstractedRecursor_head with
      ⟨levels, init, hspine, hlevels, hinit⟩
    have hrebuild := VExpr.mkApps_getAppFnArgs recursorResult
    rw [hspine] at hrebuild
    refine ⟨domains, levels, init, _, hdomains, ?_, hlevels, hinit,
      hmajor, hfree⟩
    rw [hresult]
    congr 1
    rw [← hrebuild]
    simp [VExpr.mkApps, List.foldl_append]

/-- Complete stage-correct guarded-result certificate for one semantically
retained call.  Freshness is used only in the pre-installation environment
to establish source absence; the equation itself is translated after the
recursors have been installed. -/
theorem SemanticBoundGeneratedRecursiveCall.outerAbstractedIotaResultCertificate
    {root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF root recLparams}
    (H : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors
      lvls R decl depth field value)
    (hfieldEq : field = .fvar fv)
    (Htr : TrExprS env Us (abstractForallContext ruleDomains Delta)
      (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, R.venv.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext ruleDomains Delta))
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.generated.recursorName ∈ recursors)
    (hparams : ∀ arg ∈ stats.params, arg.AvoidsConsts recursors)
    (hmotives : ∀ arg ∈ motives, arg.AvoidsConsts recursors)
    (hminors : ∀ arg ∈ minors, arg.AvoidsConsts recursors)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders)
    (hruleDomains : ruleDomains.length = binders.length)
    (hfieldVars : ∀ fieldVar,
      (Expr.fvar fv).abstractList binders = .bvar fieldVar →
      fieldVar ∈ fieldVars) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  subst field
  rcases H.translatedOuterAbstractedCallShape Htr hfresh hctx hproj with
    ⟨domains, levels, init, major, hdomains, hresult, hlevels,
      hinit, hmajor, hdomainsFree⟩
  have hctx' : VLCtx.NoIndConsts recursors
      (abstractForallContext domains
        (abstractForallContext ruleDomains Delta)) :=
    VLCtx.NoIndConsts.abstractForallContext (domains := domains) hctx
  have hsourceInit := H.outerAbstractedRecursorArgsAvoids hfresh
    hparams hmotives hminors binders
  have hinitFree : ∀ arg ∈ init,
      arg.containsAnyConst recursors = false :=
    checkPositivityStep.List.Forall₂.targets_noConstsOfSourceAvoids
      hinit hsourceInit hctx' hproj
  have hsourceMajor :
      (H.generated.outerAbstractedMajor binders).AvoidsConsts recursors :=
    H.generated.outerAbstractedMajorAvoids hfieldRoot hbinders hfield
  have hmajorFree : major.containsAnyConst recursors = false :=
    checkPositivityStep.TrExprS.noConstsOfSourceAvoids
      hsourceMajor hctx' hproj hmajor
  exact ⟨{
    domains := domains
    recursor := H.generated.recursorName
    levels := levels
    init := init
    major := major
    result_eq := hresult
    domains_recursor_free := hdomainsFree
    recursor_mem := hrecursor
    arguments_guarded := by
      intro arg harg
      rcases List.mem_append.mp harg with harg | harg
      · exact VExpr.GuardedIota.ofContainsAnyConstFalse
          (hinitFree arg harg)
      · simp only [List.mem_singleton] at harg
        subst arg
        exact VExpr.GuardedIota.ofContainsAnyConstFalse hmajorFree
    major_is_field := H.generated.translatedOuterAbstractedMajor_isField
      hfieldRoot hbinders hfield hruleDomains hdomains hfieldVars hmajor }⟩

/-- Guarded recursive-result certificate for the simultaneously abstracted
generated value that occurs in a closed rule RHS. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedIotaResultCertificate_ofFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (Htr : TrExprS env Us (abstractForallContext ruleDomains Δ)
      (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext ruleDomains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursorName ∈ recursors)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders)
    (hruleDomains : ruleDomains.length = binders.length)
    (hfieldVars : ∀ fieldVar,
      (Expr.fvar fv).abstractList binders = .bvar fieldVar →
      fieldVar ∈ fieldVars) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  rcases H.translatedOuterAbstractedCallShape_noFresh
      Htr hfresh hctx hproj with
    ⟨domains, levels, init, major, hdomains, hresult, hlevels,
      hinit, hmajor, hdomainsFree⟩
  have hctx' : VLCtx.NoIndConsts recursors
      (abstractForallContext domains
        (abstractForallContext ruleDomains Δ)) :=
    VLCtx.NoIndConsts.abstractForallContext
      (domains := domains) hctx
  have hinitFree : ∀ arg ∈ init,
      arg.containsAnyConst recursors = false :=
    checkPositivityStep.List.Forall₂.targets_noFreshConsts
      hinit hfresh hctx' hproj
  have hmajorFree : major.containsAnyConst recursors = false :=
    checkPositivityStep.TrExprS.noFreshConsts
      hfresh hctx' hproj hmajor
  exact ⟨{
    domains := domains
    recursor := H.recursorName
    levels := levels
    init := init
    major := major
    result_eq := hresult
    domains_recursor_free := hdomainsFree
    recursor_mem := hrecursor
    arguments_guarded := by
      intro arg harg
      rcases List.mem_append.mp harg with harg | harg
      · exact VExpr.GuardedIota.ofContainsAnyConstFalse
          (hinitFree arg harg)
      · simp only [List.mem_singleton] at harg
        subst arg
        exact VExpr.GuardedIota.ofContainsAnyConstFalse hmajorFree
    major_is_field := H.translatedOuterAbstractedMajor_isField
      hfieldRoot hbinders hfield hruleDomains hdomains hfieldVars hmajor }⟩

/-- Equality-oriented wrapper that keeps call-dependent evidence, notably
recursor membership, synchronized while identifying the selected field. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedIotaResultCertificate_ofFresh_eq
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (hfieldEq : field = .fvar fv)
    (Htr : TrExprS env Us (abstractForallContext ruleDomains Δ)
      (value.abstractList binders) result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext ruleDomains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursorName ∈ recursors)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup)
    (hfield : fv ∈ binders)
    (hruleDomains : ruleDomains.length = binders.length)
    (hfieldVars : ∀ fieldVar,
      (Expr.fvar fv).abstractList binders = .bvar fieldVar →
      fieldVar ∈ fieldVars) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  subst field
  exact H.outerAbstractedIotaResultCertificate_ofFresh Htr hfresh hctx
    hproj hrecursor hfieldRoot hbinders hfield hruleDomains hfieldVars

/-- Stage-correct guarded recursive-result certificate for the closed form
of a generated call.  Translation happens in the post-installation
environment, so freshness cannot be demanded of the complete call.  Instead
the semantic producer supplies exactly the three guard facts extracted from
the translated domains and call spine. -/
theorem BoundGeneratedRecursiveCall.outerAbstractedIotaResultCertificate
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us (abstractForallContext ruleDomains Delta)
      (value.abstractList binders) result)
    (hrecursor : H.recursorName ∈ recursors)
    (Hguard : ∀ (domains : List VExpr) (levels : List VLevel)
      (init : List VExpr) (major : VExpr),
      domains.length = H.localArgs.size →
      List.Forall₂
        (TrExprS env Us
          (abstractForallContext domains
            (abstractForallContext ruleDomains Delta)))
        (H.outerAbstractedRecursor binders).getAppArgsList init →
      TrExprS env Us
        (abstractForallContext domains
          (abstractForallContext ruleDomains Delta))
        (H.outerAbstractedMajor binders) major →
      (∀ dom ∈ domains, dom.containsAnyConst recursors = false) ∧
      (∀ arg ∈ init ++ [major],
        arg.GuardedIota recursors fieldVars domains.length) ∧
      major.IsFieldApp fieldVars domains.length) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  rcases H.translatedOuterAbstractedCallShape Htr with
    ⟨domains, levels, init, major, hdomains, hresult, hlevels,
      hinit, hmajor⟩
  rcases Hguard domains levels init major hdomains hinit hmajor with
    ⟨hdomainsFree, harguments, hmajorField⟩
  exact ⟨{
    domains := domains
    recursor := H.recursorName
    levels := levels
    init := init
    major := major
    result_eq := hresult
    domains_recursor_free := hdomainsFree
    recursor_mem := hrecursor
    arguments_guarded := harguments
    major_is_field := hmajorField }⟩

/-- A generated recursive result is semantically guarded whenever the new
recursor names are fresh in the translation environment and the selected
constructor field is already identified in the outer abstract context. -/
theorem BoundGeneratedRecursiveCall.iotaResultCertificate_ofFresh
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root (.fvar fv) value)
    (Htr : TrExprS env Us Δ value result)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursorName ∈ recursors)
    (henv : env.Ordered)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (Hfield : TrExprS env Us Δ (.fvar fv) recursiveArg)
    (hfield : recursiveArg.IsFieldApp fieldVars 0) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  rcases H.translatedCallShape_noFresh Htr hfresh hctx hproj with
    ⟨domains, levels, init, major, hdomains, hresult, hlevels,
      hinit, hmajor, hdomainsFree⟩
  have hctx' : VLCtx.NoIndConsts recursors
      (abstractForallContext domains Δ) :=
    VLCtx.NoIndConsts.abstractForallContext
      (domains := domains) hctx
  have hinitFree : ∀ arg ∈ init,
      arg.containsAnyConst recursors = false :=
    checkPositivityStep.List.Forall₂.targets_noFreshConsts
      hinit hfresh hctx' hproj
  have hmajorFree : major.containsAnyConst recursors = false :=
    checkPositivityStep.TrExprS.noFreshConsts
      hfresh hctx' hproj hmajor
  exact ⟨{
    domains := domains
    recursor := H.recursorName
    levels := levels
    init := init
    major := major
    result_eq := hresult
    domains_recursor_free := hdomainsFree
    recursor_mem := hrecursor
    arguments_guarded := by
      intro arg harg
      rcases List.mem_append.mp harg with harg | harg
      · exact VExpr.GuardedIota.ofContainsAnyConstFalse
          (hinitFree arg harg)
      · simp only [List.mem_singleton] at harg
        subst arg
        exact VExpr.GuardedIota.ofContainsAnyConstFalse hmajorFree
    major_is_field := H.translatedMajor_isField henv hfieldRoot Hfield
      hfield hdomains hmajor }⟩

/-- Turn the syntax-directed call translation into the semantic guarded-call
certificate. The remaining callback is precisely the guard proof; executable
syntax, lambda closure, recursor name, and translated spine are fixed here. -/
theorem BoundGeneratedRecursiveCall.iotaResultCertificate
    (H : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root field value)
    (Htr : TrExprS env Us Δ value result)
    (hrecursor : H.recursorName ∈ recursors)
    (Hguard : ∀ (domains : List VExpr) (levels : List VLevel)
      (init : List VExpr) (major : VExpr),
      domains.length = H.localArgs.size →
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        H.abstractedRecursor.getAppArgsList init →
      TrExprS env Us (abstractForallContext domains Δ)
        H.abstractedMajor major →
      (∀ dom ∈ domains, dom.containsAnyConst recursors = false) ∧
      (∀ arg ∈ init ++ [major],
        arg.GuardedIota recursors fieldVars domains.length) ∧
      major.IsFieldApp fieldVars domains.length) :
    Nonempty (IotaRecursiveResultCertificate recursors fieldVars
      recursiveArg result) := by
  rcases H.translatedCallShape Htr with
    ⟨domains, levels, init, major, hdomains, hresult, hlevels,
      hinit, hmajor⟩
  rcases Hguard domains levels init major hdomains hinit hmajor with
    ⟨hdomainsFree, harguments, hmajorField⟩
  exact ⟨{
    domains := domains
    recursor := H.recursorName
    levels := levels
    init := init
    major := major
    result_eq := hresult
    domains_recursor_free := hdomainsFree
    recursor_mem := hrecursor
    arguments_guarded := harguments
    major_is_field := hmajorField }⟩

/-- Prefix invariant for rule generation retaining both exact syntax and the
binding evidence needed to translate every higher-order recursive result. -/
structure BoundGeneratedRecursiveCalls
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (root : AddInductive.Context)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    Nonempty (BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root u[i] v[i]!)

/-- Prefix invariant for recursive-result generation with each executable
call coupled to the independent recursive-domain judgment for its exact
selected field. -/
structure SemanticBoundGeneratedRecursiveCalls
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams)
    (decl : VInductDecl) (depth : Nat) (P : FVarId → Prop)
    (u v : Array Expr) (done : Nat) : Prop where
  covered : done ≤ u.size
  size : v.size = done
  entries : ∀ i, i < done → (hi : i < u.size) →
    ∃ S : SemanticBoundGeneratedRecursiveCall indTypes stats motives
        minors lvls R decl depth u[i] v[i]!,
      S.rootScope = P

def SemanticBoundGeneratedRecursiveCalls.empty
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {root : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF root recLparams)
    (decl : VInductDecl) (depth : Nat) (P : FVarId → Prop)
    (u : Array Expr) :
    SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      R decl depth P u #[] 0 where
  covered := Nat.zero_le _
  size := rfl
  entries _ h := by omega

def SemanticBoundGeneratedRecursiveCalls.push
    (H : SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
      lvls R decl depth P u v done)
    (hdone : done < u.size)
    (Hentry : SemanticBoundGeneratedRecursiveCall indTypes stats motives
      minors lvls R decl depth u[done] value)
    (hscope : Hentry.rootScope = P) :
    SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      R decl depth P u (v.push value) (done + 1) where
  covered := by omega
  size := by simp [H.size]
  entries i hi hiu := by
    by_cases h : i = done
    · subst i
      have hpush : done < (v.push value).size := by simp [H.size]
      have hbang : (v.push value)[done]! = value := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush]
        simpa [H.size] using (@Array.getElem_push_eq Expr v value)
      rw [hbang]
      exact ⟨Hentry, hscope⟩
    · have hold : i < done := by omega
      have hv : i < v.size := by simpa [H.size] using hold
      have hpush : i < (v.push value).size := by
        simpa using Nat.lt_succ_of_lt hv
      have hbang : (v.push value)[i]! = v[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush, dif_pos hv]
        exact Array.getElem_push_lt hv
      rw [hbang]
      exact H.entries i hold hiu

theorem SemanticBoundGeneratedRecursiveCalls.bound
    {root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF root recLparams}
    (H : SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
      lvls R decl depth P u v done) :
    BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v done where
  covered := H.covered
  size := H.size
  entries i hi hiu := by
    rcases H.entries i hi hiu with ⟨Hentry, _⟩
    exact ⟨Hentry.generated⟩

/-- Repackage the array-aligned semantic calls as replacement certificates
for an earlier field-selection trace.  Only the old concrete ordinal is
retained; owner, domain, context, and recursive judgment all come from the
call-time validation of the exact field at the corresponding selected-array
position. -/
theorem SemanticBoundGeneratedRecursiveCalls.replacements
    {root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF root recLparams}
    {fields : List
      (RecursorRecursiveDomainAt R.venv decl recLparams.length)}
    (H : SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
      lvls R decl depth P u v u.size)
    (hlength : fields.length = u.size) :
    ∃ replacements : List
        (RecursorRecursiveDomainAt R.venv decl recLparams.length),
      List.Forall₂
        (fun old replacement =>
          old.fieldIndex = replacement.fieldIndex)
        fields replacements := by
  classical
  have build : ∀ (offset : Nat)
      (remaining : List
        (RecursorRecursiveDomainAt R.venv decl recLparams.length)),
      offset + remaining.length ≤ u.size →
      ∃ replacements : List
          (RecursorRecursiveDomainAt R.venv decl recLparams.length),
        List.Forall₂
          (fun old replacement =>
            old.fieldIndex = replacement.fieldIndex)
          remaining replacements := by
    intro offset remaining hroom
    induction remaining generalizing offset with
    | nil => exact ⟨[], .nil⟩
    | cons old remaining ih =>
      have hoffset : offset < u.size := by simp at hroom; omega
      let E := Classical.choose (H.entries offset hoffset hoffset)
      let replacement : RecursorRecursiveDomainAt
          R.venv decl recLparams.length := {
        fieldIndex := old.fieldIndex
        ownerIdx := E.generated.ownerIdx
        owner_lt := E.owner_lt
        ctx := R.mlctx.vlctx.toCtx
        depth := depth
        domain := E.domain
        recursive := E.recursive }
      rcases ih (offset + 1) (by simp at hroom ⊢; omega) with
        ⟨tail, Htail⟩
      exact ⟨replacement :: tail, .cons (by rfl) Htail⟩
  apply build 0 fields
  simpa [hlength]

/-- Substitute the call-time semantic domains into the exact operational
field-selection trace and specialize the result back to declaration
universes.  This produces precisely the source-level selection certificate
consumed by generated iota rules. -/
theorem SemanticBoundGeneratedRecursiveCalls.sourceSelection
    {root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF root recLparams}
    {fields : List
      (RecursorRecursiveDomainAt R.venv decl recLparams.length)}
    (H : SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
      lvls R decl depth P u v u.size)
    (Hselection : RecursorFieldSelectionsAt R.venv decl recLparams.length
      bu u fields) :
    ∃ selections : List (RecursorRecursiveDomain R.venv decl),
      RecursorFieldSelections R.venv decl bu u selections := by
  rcases H.replacements Hselection.fields_length with
    ⟨replacements, Haligned⟩
  exact ⟨replacements.map RecursorRecursiveDomainAt.toSource,
    (Hselection.replace Haligned).toSource⟩

def BoundGeneratedRecursiveCalls.empty
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (root : AddInductive.Context) (u : Array Expr) :
    BoundGeneratedRecursiveCalls indTypes stats motives minors lvls root
      u #[] 0 where
  covered := Nat.zero_le _
  size := rfl
  entries _ h := by omega

def BoundGeneratedRecursiveCalls.push
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v done)
    (hdone : done < u.size)
    (Hentry : BoundGeneratedRecursiveCall indTypes stats motives minors lvls
      root u[done] value) :
    BoundGeneratedRecursiveCalls indTypes stats motives minors lvls root
      u (v.push value) (done + 1) where
  covered := by omega
  size := by simp [H.size]
  entries i hi hiu := by
    by_cases h : i = done
    · subst i
      have hpush : done < (v.push value).size := by simp [H.size]
      have hbang : (v.push value)[done]! = value := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush]
        simpa [H.size] using (@Array.getElem_push_eq Expr v value)
      rw [hbang]
      exact ⟨Hentry⟩
    · have hold : i < done := by omega
      have hv : i < v.size := by simpa [H.size] using hold
      have hpush : i < (v.push value).size := by
        simpa using Nat.lt_succ_of_lt hv
      have hbang : (v.push value)[i]! = v[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush, dif_pos hv]
        exact Array.getElem_push_lt hv
      rw [hbang]
      exact H.entries i hold hiu

theorem BoundGeneratedRecursiveCalls.generated
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v done) :
    checkPositivityStep.GeneratedRecursiveCalls indTypes stats motives minors
      lvls u v done where
  covered := H.covered
  size := H.size
  entries i hi hiu := by
    rcases H.entries i hi hiu with ⟨Hentry⟩
    exact Hentry.generated

/-- Convert the binder-aware executable call array into the aligned semantic
recursive-result certificate. Only the genuinely pointwise call proof remains
as a premise; all array/list indexing and translation alignment are handled
here. -/
theorem BoundGeneratedRecursiveCalls.iotaResults
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (Hargs : List.Forall₂ (TrExprS env Us Δ)
      u.toList recursiveArgs)
    (Hresults : List.Forall₂ (TrExprS env Us Δ)
      v.toList recursiveResults)
    (Hpoint : ∀ i (hi : i < u.size)
      (harg : i < recursiveArgs.length)
      (hresult : i < recursiveResults.length),
      BoundGeneratedRecursiveCall indTypes stats motives minors lvls
        root u[i] v[i]! →
      TrExprS env Us Δ u[i] recursiveArgs[i] →
      TrExprS env Us Δ v[i]! recursiveResults[i] →
      Nonempty (IotaRecursiveResultCertificate recursors fieldVars
        recursiveArgs[i] recursiveResults[i])) :
    IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults := by
  have hargsLen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hargs
  have hresultsLen :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hresults
  have hargsSize : u.size = recursiveArgs.length := by
    simpa using hargsLen
  have hresultsSize : v.size = recursiveResults.length := by
    simpa using hresultsLen
  have hvSize : v.size = u.size := H.size
  refine ⟨List.forall₂_of_getElem (by omega) ?_⟩
  intro i hiArg hiResult
  have hiU : i < u.size := by
    simpa using (show i < u.toList.length by omega)
  have hiV : i < v.toList.length := by omega
  rcases H.entries i hiU hiU with ⟨Hentry⟩
  have Harg := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i (by simpa using hiU) hiArg
  have Hresult := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hresults i hiV hiResult
  apply Hpoint i hiU hiArg hiResult Hentry
  · simpa using Harg
  · have hiVSize : i < v.size := by simpa using hiV
    simpa [Array.getElem!_eq_getD, Array.getD, hiVSize] using Hresult

/-- Array-alignment lift for generated calls after simultaneous abstraction
over the surrounding rule binders. -/
theorem BoundGeneratedRecursiveCalls.abstractedIotaResults
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (Hargs : List.Forall₂ (TrExprS env Us Δ)
      (u.map fun arg => arg.abstractList binders).toList recursiveArgs)
    (Hresults : List.Forall₂ (TrExprS env Us Δ)
      (v.map fun result => result.abstractList binders).toList
      recursiveResults)
    (Hpoint : ∀ i (hi : i < u.size)
      (harg : i < recursiveArgs.length)
      (hresult : i < recursiveResults.length),
      BoundGeneratedRecursiveCall indTypes stats motives minors lvls
        root u[i] v[i]! →
      TrExprS env Us Δ (u[i].abstractList binders) recursiveArgs[i] →
      TrExprS env Us Δ (v[i]!.abstractList binders)
        recursiveResults[i] →
      Nonempty (IotaRecursiveResultCertificate recursors fieldVars
        recursiveArgs[i] recursiveResults[i])) :
    IotaRecursiveResultsCertificate recursors fieldVars
      recursiveArgs recursiveResults := by
  have hargsLen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hargs
  have hresultsLen :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hresults
  have hargsSize : u.size = recursiveArgs.length := by
    simpa using hargsLen
  have hresultsSize : v.size = recursiveResults.length := by
    simpa using hresultsLen
  have hvSize : v.size = u.size := H.size
  refine ⟨List.forall₂_of_getElem (by omega) ?_⟩
  intro i hiArg hiResult
  have hiU : i < u.size := by omega
  have hiV : i < v.size := by omega
  rcases H.entries i hiU hiU with ⟨Hentry⟩
  have Harg := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i (by simpa using hiU) hiArg
  have Hresult := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hresults i (by simpa using hiV) hiResult
  apply Hpoint i hiU hiArg hiResult Hentry
  · simpa using Harg
  · have hiVSize : i < v.size := hiV
    simpa [Array.getElem!_eq_getD, Array.getD, hiVSize] using Hresult

/-- Exact recursor-name coverage required by a generated call array. This
avoids quantifying over arbitrary exposed expressions whose computed owner
index has not been validated. -/
def BoundGeneratedRecursiveCalls.RecursorsPresent
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size) (recursors : List Name) : Prop :=
  ∀ i (hi : i < u.size)
      (Hentry : BoundGeneratedRecursiveCall indTypes stats motives minors
        lvls root u[i] v[i]!),
    Hentry.recursorName ∈ recursors

theorem BoundGeneratedRecursiveCalls.abstractedIotaResults_ofFresh
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (Hbound : BoundFVarArray root u)
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext ruleDomains Δ))
      (u.map fun arg => arg.abstractList binders).toList recursiveArgs)
    (Hresults : List.Forall₂
      (TrExprS env Us (abstractForallContext ruleDomains Δ))
      (v.map fun result => result.abstractList binders).toList
      recursiveResults)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext ruleDomains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.RecursorsPresent recursors)
    (hbinders : binders.Nodup)
    (hruleDomains : ruleDomains.length = binders.length)
    (hselected : ∀ fv ∈ Hbound.fvars, fv ∈ binders) :
    IotaRecursiveResultsCertificate recursors
      (recursiveArgs.filterMap VExpr.bvarHead?)
      recursiveArgs recursiveResults := by
  refine H.abstractedIotaResults Hargs Hresults ?_
  intro i hi hiarg hiresult Hentry Harg Hresult
  rcases Hbound.getElem_eq_fvar i hi with
    ⟨hiFvars, hsource⟩
  let fv := Hbound.fvars[i]
  have hargTr := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i (by simpa using hi) hiarg
  have hfieldRoot : fv ∈ root.lctx.fvars :=
    Hbound.members fv (List.getElem_mem hiFvars)
  have hfield : fv ∈ binders :=
    hselected fv (List.getElem_mem hiFvars)
  have hsource' : u[i] = .fvar fv := hsource
  have HArgFv : TrExprS env Us (abstractForallContext ruleDomains Δ)
      ((Expr.fvar fv).abstractList binders) recursiveArgs[i] := by
    simpa [hsource'] using hargTr
  have hrecursorMemBefore : Hentry.recursorName ∈ recursors :=
    hrecursor i hi Hentry
  apply Hentry.outerAbstractedIotaResultCertificate_ofFresh_eq hsource'
    Hresult hfresh hctx hproj hrecursorMemBefore hfieldRoot hbinders hfield
      hruleDomains
  intro fieldVar hfieldSource
  have HArg' := HArgFv
  rw [hfieldSource] at HArg'
  have hfieldBound : fieldVar < ruleDomains.length := by
    rcases List.mem_iff_getElem.mp hfield with ⟨j, hj, hget⟩
    have hcanonical := Expr.abstractList_fvar_getElem
      hbinders j hj (k := 0)
    rw [hget, hfieldSource] at hcanonical
    have : fieldVar = binders.length - 1 - j := by
      cases hcanonical
      simp
    rw [hruleDomains]
    omega
  have hargEq : recursiveArgs[i] = .bvar fieldVar :=
    TrExprS.bvar_eq_of_abstractForallContext HArg' hfieldBound
  have hhead : recursiveArgs[i].bvarHead? = some fieldVar := by
    rw [hargEq]
    rfl
  exact List.mem_filterMap.mpr
    ⟨recursiveArgs[i], List.getElem_mem hiarg, hhead⟩

/-- Stage-correct array lift using the semantic call retained at each exact
recursive-field position.  The source environment supplies freshness while
the rule equation and recursive results are translated in the later
post-installation environment. -/
theorem SemanticBoundGeneratedRecursiveCalls.abstractedIotaResults
    {root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF root recLparams}
    (H : SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
      lvls R decl depth P u v u.size)
    (Hbound : BoundFVarArray root u)
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext ruleDomains Delta))
      (u.map fun arg => arg.abstractList binders).toList recursiveArgs)
    (Hresults : List.Forall₂
      (TrExprS env Us (abstractForallContext ruleDomains Delta))
      (v.map fun result => result.abstractList binders).toList
      recursiveResults)
    (hfresh : ∀ name ∈ recursors, R.venv.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext ruleDomains Delta))
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.bound.RecursorsPresent recursors)
    (hparams : ∀ arg ∈ stats.params, arg.AvoidsConsts recursors)
    (hmotives : ∀ arg ∈ motives, arg.AvoidsConsts recursors)
    (hminors : ∀ arg ∈ minors, arg.AvoidsConsts recursors)
    (hbinders : binders.Nodup)
    (hruleDomains : ruleDomains.length = binders.length)
    (hselected : ∀ fv ∈ Hbound.fvars, fv ∈ binders) :
    IotaRecursiveResultsCertificate recursors
      (recursiveArgs.filterMap VExpr.bvarHead?)
      recursiveArgs recursiveResults := by
  refine H.bound.abstractedIotaResults Hargs Hresults ?_
  intro i hi hiarg hiresult _Hentry Harg Hresult
  rcases H.entries i hi hi with ⟨E, _⟩
  have hargTr := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i (by simpa using hi) hiarg
  have hresultTr := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hresults i (by simpa [H.size] using hi) hiresult
  rcases Hbound.getElem_eq_fvar i hi with ⟨hiFvars, hsource⟩
  let fv := Hbound.fvars[i]
  have hfieldRoot : fv ∈ root.lctx.fvars :=
    Hbound.members fv (List.getElem_mem hiFvars)
  have hfield : fv ∈ binders :=
    hselected fv (List.getElem_mem hiFvars)
  have HArgFv : TrExprS env Us
      (abstractForallContext ruleDomains Delta)
      ((Expr.fvar fv).abstractList binders) recursiveArgs[i] := by
    simpa [hsource] using hargTr
  have hiV : i < v.size := by simpa [H.size] using hi
  have hresultTr' : TrExprS env Us
      (abstractForallContext ruleDomains Delta)
      (v[i]!.abstractList binders) recursiveResults[i] := by
    simpa [Array.getElem!_eq_getD, Array.getD, hiV] using hresultTr
  have hrecursorMem : E.generated.recursorName ∈ recursors :=
    hrecursor i hi E.generated
  apply E.outerAbstractedIotaResultCertificate hsource hresultTr' hfresh hctx
    hproj hrecursorMem hparams hmotives hminors hfieldRoot hbinders hfield
      hruleDomains
  intro fieldVar hfieldSource
  have HArg' := HArgFv
  rw [hfieldSource] at HArg'
  have hfieldBound : fieldVar < ruleDomains.length := by
    rcases List.mem_iff_getElem.mp hfield with ⟨j, hj, hget⟩
    have hcanonical := Expr.abstractList_fvar_getElem
      hbinders j hj (k := 0)
    rw [hget, hfieldSource] at hcanonical
    have : fieldVar = binders.length - 1 - j := by
      cases hcanonical
      simp
    rw [hruleDomains]
    omega
  have hargEq : recursiveArgs[i] = .bvar fieldVar :=
    TrExprS.bvar_eq_of_abstractForallContext HArg' hfieldBound
  have hhead : recursiveArgs[i].bvarHead? = some fieldVar := by
    rw [hargEq]
    rfl
  exact List.mem_filterMap.mpr
    ⟨recursiveArgs[i], List.getElem_mem hiarg, hhead⟩

/-- Lift the freshness-derived pointwise result certificate across the exact
recursive-call array. The only remaining rule-local facts are recursor-name
membership and the de Bruijn head selected for each translated field. -/
theorem BoundGeneratedRecursiveCalls.iotaResults_ofFresh
    (H : BoundGeneratedRecursiveCalls indTypes stats motives minors lvls
      root u v u.size)
    (Hbound : BoundFVarArray root u)
    (Hargs : List.Forall₂ (TrExprS env Us Δ)
      u.toList recursiveArgs)
    (Hresults : List.Forall₂ (TrExprS env Us Δ)
      v.toList recursiveResults)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (henv : env.Ordered)
    (hrecursor : ∀ exposedType,
      Lean.mkRecName
        indTypes[(AddInductive.getIIndices stats exposedType).1]!.name ∈
          recursors)
    (hheads : ∀ i (hi : i < recursiveArgs.length),
      ∃ field, recursiveArgs[i].bvarHead? = some field) :
    IotaRecursiveResultsCertificate recursors
      (recursiveArgs.filterMap VExpr.bvarHead?)
      recursiveArgs recursiveResults := by
  apply H.iotaResults Hargs Hresults
  intro i hi hiarg hiresult Hentry Harg Hresult
  rcases Hbound.get_eq_fvar i hi with ⟨fv, hsource, hfieldRoot⟩
  rw [hsource] at Hentry Harg
  have hrecursorMem : Hentry.recursorName ∈ recursors := by
    simpa [BoundGeneratedRecursiveCall.recursorName] using
      hrecursor Hentry.exposedType
  rcases hheads i hiarg with ⟨field, hhead⟩
  have hfield : recursiveArgs[i].IsFieldApp
      (recursiveArgs.filterMap VExpr.bvarHead?) 0 :=
    VExpr.IsFieldApp.ofRecursiveArg
      (List.getElem_mem hiarg) hhead
  exact Hentry.iotaResultCertificate_ofFresh Hresult hfresh hctx hproj
    hrecursorMem henv hfieldRoot Harg hfield

/-- One generated iota rule retaining the constructor-field context and the
binder-aware certificate for every recursive result. -/
structure BoundGeneratedRecursorRule
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctor : Constructor) (minorIdx : Nat) (rule : RecursorRule) where
  root : AddInductive.Context
  root_wf : BindingContextWF root
  target : Expr
  allArgs : Array Expr
  recursiveArgs : Array Expr
  recursiveResults : Array Expr
  minor_valid : minorIdx < minors.size
  params_bound : BoundFVarArray root stats.params
  motives_bound : BoundFVarArray root motives
  minors_bound : BoundFVarArray root minors
  outer_binders_nodup :
    ((params_bound.fvars ++ motives_bound.fvars) ++
      minors_bound.fvars).Nodup
  all_args_bound : BoundFVarArray root allArgs
  recursive_args_bound : BoundFVarArray root recursiveArgs
  recursive_args_sublist : recursiveArgs.toList.Sublist allArgs.toList
  all_args_nodup : all_args_bound.fvars.Nodup
  recursive_args_nodup : recursive_args_bound.fvars.Nodup
  all_args_outer_fresh : ∀ fv ∈ all_args_bound.fvars,
    fv ∉ (params_bound.fvars ++ motives_bound.fvars) ++ minors_bound.fvars
  recursive_calls : BoundGeneratedRecursiveCalls indTypes stats motives
    minors lvls root recursiveArgs recursiveResults recursiveArgs.size
  ctor_eq : rule.ctor = ctor.name
  fields_eq : rule.nfields = allArgs.size
  rhs_eq : rule.rhs =
    (root.lctx.mkLambda stats.params <| root.lctx.mkLambda motives <|
     root.lctx.mkLambda minors <| root.lctx.mkLambda allArgs <|
     mkAppN (mkAppN minors[minorIdx]! allArgs) recursiveResults)

/-- Rule-local interface to the guarded recursive-result proof. Array
alignment and the fact that selected source fields are genuine retained free
variables are discharged by the binder-aware rule certificate. -/
theorem BoundGeneratedRecursorRule.iotaResults_ofFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {recursiveArgs recursiveResults : List VExpr}
    (Hargs : List.Forall₂ (TrExprS env Us Δ)
      H.recursiveArgs.toList recursiveArgs)
    (Hresults : List.Forall₂ (TrExprS env Us Δ)
      H.recursiveResults.toList recursiveResults)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (henv : env.Ordered)
    (hrecursor : ∀ exposedType,
      Lean.mkRecName
        indTypes[(AddInductive.getIIndices stats exposedType).1]!.name ∈
          recursors)
    (hheads : ∀ i (hi : i < recursiveArgs.length),
      ∃ field, recursiveArgs[i].bvarHead? = some field) :
    IotaRecursiveResultsCertificate recursors
      (recursiveArgs.filterMap VExpr.bvarHead?)
      recursiveArgs recursiveResults :=
  H.recursive_calls.iotaResults_ofFresh H.recursive_args_bound
    Hargs Hresults hfresh hctx hproj henv hrecursor hheads

/-- All source binders closed by a generated rule are globally distinct:
outer recursor binders are no-alias by construction, while constructor fields
are fresh relative to that outer context. -/
theorem BoundGeneratedRecursorRule.binders_nodup
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    (((H.params_bound.fvars ++ H.motives_bound.fvars) ++
      H.minors_bound.fvars) ++ H.all_args_bound.fvars).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨H.outer_binders_nodup, H.all_args_nodup, ?_⟩
  intro outer houter field hfield heq
  subst outer
  exact H.all_args_outer_fresh field hfield houter

def BoundGeneratedRecursorRule.binders
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : List FVarId :=
  ((H.params_bound.fvars ++ H.motives_bound.fvars) ++
    H.minors_bound.fvars) ++ H.all_args_bound.fvars

def BoundGeneratedRecursorRule.sourceRhsBody
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  mkAppN (mkAppN minors[minorIdx]! H.allArgs) H.recursiveResults

/-- Constructor application appearing as the major premise of the generated
iota left-hand side. -/
def BoundGeneratedRecursorRule.sourceConstructorMajor
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) H.allArgs

/-- Canonical source left-hand-side body determined by the residual target
returned from `loopCtorArgs`. -/
def BoundGeneratedRecursorRule.sourceLhsBody
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  let (ownerIdx, indices) := AddInductive.getIIndices stats H.target
  let recursor := .const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls
  (mkAppN
    (mkAppN (mkAppN (mkAppN recursor stats.params) motives) minors)
      indices).app H.sourceConstructorMajor

/-- Proof-side source equation LHS closed over exactly the binders used by
the production RHS. `RecursorRule` stores only the RHS; the kernel reconstructs
this matching pattern from its recursor metadata. -/
def BoundGeneratedRecursorRule.sourceLhs
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : Expr :=
  LocalContext.mkBindingList true H.root.lctx H.binders H.sourceLhsBody

def BoundGeneratedRecursorRule.all_binders_bound
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) : BoundFVarArray H.root
      (stats.params ++ motives ++ minors ++ H.allArgs) :=
  ((H.params_bound.append H.motives_bound).append H.minors_bound).append
    H.all_args_bound

/-- Simultaneously closing the complete rule-binder payload produces the
canonical de Bruijn variables in source-binder order. -/
theorem BoundGeneratedRecursorRule.abstractedBinders_eq
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    (((stats.params ++ motives ++ minors ++ H.allArgs).map
      fun arg => arg.abstractList H.binders).toList) =
      List.ofFn (fun i : Fin H.binders.length =>
        Expr.bvar (H.binders.length - 1 - i)) := by
  have hexpressions := H.all_binders_bound.expressions
  have hmapped := congrArg
    (fun args : Array Expr => args.map fun arg =>
      arg.abstractList H.binders) hexpressions
  have hfvars : H.all_binders_bound.fvars = H.binders := by
    rfl
  have hcanonical := Expr.abstractList_fvarArray
    H.binders 0 H.binders_nodup
  rw [hfvars, hcanonical] at hmapped
  simpa using congrArg Array.toList hmapped

/-- The parameter prefix of the simultaneously abstracted rule binders is
the corresponding prefix of canonical de Bruijn variables. -/
theorem BoundGeneratedRecursorRule.abstractedParams_eq
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ((stats.params.map fun arg => arg.abstractList H.binders).toList) =
      List.ofFn (fun i : Fin stats.params.size =>
        Expr.bvar (H.binders.length - 1 - i)) := by
  have h := congrArg (List.take stats.params.size) H.abstractedBinders_eq
  have hparams : H.params_bound.fvars.length = stats.params.size := by
    have := congrArg Array.size H.params_bound.expressions
    simpa using this.symm
  have hle : stats.params.size ≤ H.binders.length := by
    unfold BoundGeneratedRecursorRule.binders
    simp only [List.length_append]
    omega
  have htake :
      List.take stats.params.size
          (List.ofFn fun i : Fin H.binders.length =>
            Expr.bvar (H.binders.length - 1 - i)) =
        List.ofFn (fun i : Fin stats.params.size =>
          Expr.bvar (H.binders.length - 1 - i)) := by
    apply List.ext_getElem
    · simp [hle]
    · intro j hj₁ hj₂
      simp only [List.getElem_take, List.getElem_ofFn]
  have hprefix :
      ((stats.params.map fun arg => arg.abstractList H.binders).toList) =
        List.take stats.params.size
          (List.ofFn fun i : Fin H.binders.length =>
            Expr.bvar (H.binders.length - 1 - i)) := by
    simpa [Array.toList_append, List.take_append,
      List.take_of_length_le] using h
  exact hprefix.trans htake

/-- The complete simultaneously abstracted binder payload translates
pointwise to the equally ordered canonical abstract variables. -/
theorem BoundGeneratedRecursorRule.abstractedBindersTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = H.binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (((stats.params ++ motives ++ minors ++ H.allArgs).map
        fun arg => arg.abstractList H.binders).toList)
      (List.ofFn (fun i : Fin H.binders.length =>
        VExpr.bvar (H.binders.length - 1 - i))) := by
  rw [H.abstractedBinders_eq]
  exact TrExprS.canonicalBvars_of_abstractForallContext
    (env := env) (Us := Us) domains Δ H.binders.length (by omega)

theorem BoundGeneratedRecursorRule.abstractedParamsTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = H.binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((stats.params.map fun arg => arg.abstractList H.binders).toList)
      (List.ofFn fun i : Fin stats.params.size =>
        VExpr.bvar (H.binders.length - 1 - i)) := by
  have Htr := H.params_bound.abstractedTranslationAt
    (env := env) (Us := Us) H.binders []
      (H.motives_bound.fvars ++ H.minors_bound.fvars ++
        H.all_args_bound.fvars)
      (by simp [BoundGeneratedRecursorRule.binders, List.append_assoc])
      H.binders_nodup domains Δ hdomains
  simpa using Htr

theorem BoundGeneratedRecursorRule.abstractedMotivesTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = H.binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((motives.map fun arg => arg.abstractList H.binders).toList)
      (List.ofFn fun i : Fin motives.size =>
        VExpr.bvar (H.binders.length - 1 -
          (H.params_bound.fvars.length + i))) := by
  exact H.motives_bound.abstractedTranslationAt
    (env := env) (Us := Us) H.binders H.params_bound.fvars
      (H.minors_bound.fvars ++ H.all_args_bound.fvars)
      (by simp [BoundGeneratedRecursorRule.binders, List.append_assoc])
      H.binders_nodup domains Δ hdomains

theorem BoundGeneratedRecursorRule.abstractedMinorsTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = H.binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((minors.map fun arg => arg.abstractList H.binders).toList)
      (List.ofFn fun i : Fin minors.size =>
        VExpr.bvar (H.binders.length - 1 -
          ((H.params_bound.fvars ++ H.motives_bound.fvars).length + i))) := by
  exact H.minors_bound.abstractedTranslationAt
    (env := env) (Us := Us) H.binders
      (H.params_bound.fvars ++ H.motives_bound.fvars)
      H.all_args_bound.fvars
      (by simp [BoundGeneratedRecursorRule.binders, List.append_assoc])
      H.binders_nodup domains Δ hdomains

theorem BoundGeneratedRecursorRule.abstractedAllArgsTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = H.binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((H.allArgs.map fun arg => arg.abstractList H.binders).toList)
      (List.ofFn fun i : Fin H.allArgs.size =>
        VExpr.bvar (H.binders.length - 1 -
          (((H.params_bound.fvars ++ H.motives_bound.fvars) ++
            H.minors_bound.fvars).length + i))) := by
  exact H.all_args_bound.abstractedTranslationAt
    (env := env) (Us := Us) H.binders
      ((H.params_bound.fvars ++ H.motives_bound.fvars) ++
        H.minors_bound.fvars) []
      (by simp [BoundGeneratedRecursorRule.binders])
      H.binders_nodup domains Δ hdomains

/-- The four nested production `mkLambda` calls are one exact, globally
no-alias lambda telescope over the retained binder sequence. -/
theorem BoundGeneratedRecursorRule.rhs_eq_bindingList
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    rule.rhs = LocalContext.mkBindingList true H.root.lctx
      H.binders H.sourceRhsBody := by
  rw [H.rhs_eq]
  symm
  unfold BoundGeneratedRecursorRule.binders
    BoundGeneratedRecursorRule.sourceRhsBody
  have hdecl : ∀ fv ∈
      ((H.params_bound.fvars ++ H.motives_bound.fvars) ++
        H.minors_bound.fvars) ++ H.all_args_bound.fvars,
      ∃ decl, H.root.lctx.find? fv = some decl := by
    intro fv hfv
    have hmem : fv ∈ H.root.lctx.fvars := by
      rcases List.mem_append.mp hfv with houter | hall
      · rcases List.mem_append.mp houter with hpm | hminor
        · rcases List.mem_append.mp hpm with hparam | hmotive
          · exact H.params_bound.members fv hparam
          · exact H.motives_bound.members fv hmotive
        · exact H.minors_bound.members fv hminor
      · exact H.all_args_bound.members fv hall
    rcases H.root_wf.findCDecl fv hmem with
      ⟨index, name, type, bi, kind, hfind⟩
    exact ⟨.cdecl index fv name type bi kind, hfind⟩
  rw [LocalContext.mkBindingList_append_four hdecl H.binders_nodup]
  simp only [LocalContext.mkLambda, ← LocalContext.mkBinding_eq]
  have hp : ({ toList := H.params_bound.fvars.map Expr.fvar } :
      Array Expr) = stats.params := by
    simpa using H.params_bound.expressions.symm
  have hm : ({ toList := H.motives_bound.fvars.map Expr.fvar } :
      Array Expr) = motives := by
    simpa using H.motives_bound.expressions.symm
  have hmi : ({ toList := H.minors_bound.fvars.map Expr.fvar } :
      Array Expr) = minors := by
    simpa using H.minors_bound.expressions.symm
  have ha : ({ toList := H.all_args_bound.fvars.map Expr.fvar } :
      Array Expr) = H.allArgs := by
    simpa using H.all_args_bound.expressions.symm
  rw [hp, hm, hmi, ha]

theorem BoundGeneratedRecursorRule.rhsLambdaTelescope
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    Expr.LambdaTelescope rule.rhs H.binders.length
      (H.sourceRhsBody.abstractList H.binders) := by
  rw [H.rhs_eq_bindingList]
  exact LocalContext.mkBindingList_lambdaTelescope
    (H.all_binders_bound.toLocalForallSelection
      H.root_wf).declarations

theorem BoundGeneratedRecursorRule.lhsLambdaTelescope
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    Expr.LambdaTelescope H.sourceLhs H.binders.length
      (H.sourceLhsBody.abstractList H.binders) := by
  unfold BoundGeneratedRecursorRule.sourceLhs
  exact LocalContext.mkBindingList_lambdaTelescope
    (H.all_binders_bound.toLocalForallSelection
      H.root_wf).declarations

theorem BoundGeneratedRecursorRule.translatedLhsShape
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (Htr : TrExprS env Us Δ H.sourceLhs lhs) :
    ∃ domains lhsBody,
      domains.length = H.binders.length ∧
      lhs = VExpr.wrapLams domains lhsBody ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.sourceLhsBody.abstractList H.binders) lhsBody :=
  TrExprS.lambdaTelescope_shape_with_context H.lhsLambdaTelescope Htr

/-- Simultaneous closing preserves the canonical recursor/constructor LHS
spines and abstracts every source argument pointwise. -/
theorem BoundGeneratedRecursorRule.abstractedSourceLhs
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    let (ownerIdx, indices) := AddInductive.getIIndices stats H.target
    H.sourceLhsBody.abstractList H.binders =
      (mkAppN
        (mkAppN
          (mkAppN
            (mkAppN
              (.const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls)
              (stats.params.map fun arg => arg.abstractList H.binders))
            (motives.map fun arg => arg.abstractList H.binders))
          (minors.map fun arg => arg.abstractList H.binders))
        (indices.map fun arg => arg.abstractList H.binders)).app
      (mkAppN
        (mkAppN (.const ctor.name stats.levels)
          (stats.params.map fun arg => arg.abstractList H.binders))
        (H.allArgs.map fun arg => arg.abstractList H.binders)) := by
  rcases htarget : AddInductive.getIIndices stats H.target with
    ⟨ownerIdx, indices⟩
  simp only [BoundGeneratedRecursorRule.sourceLhsBody, htarget,
    BoundGeneratedRecursorRule.sourceConstructorMajor,
    Expr.abstractList_app, Expr.abstractList_mkAppN,
    Expr.abstractList_const]

/-- Inverting the translated canonical LHS exposes the exact recursor and
constructor constant spines used by `IotaEquationCertificate`. -/
theorem BoundGeneratedRecursorRule.translatedLhsResidual
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (htarget : AddInductive.getIIndices stats H.target =
      (ownerIdx, indices))
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceLhsBody.abstractList H.binders) lhsBody) :
    ∃ recursorLevels leadingArgs ctorLevels ctorArgs,
      lhsBody = VExpr.mkApps
        (.const (Lean.mkRecName indTypes[ownerIdx]!.name) recursorLevels)
        (leadingArgs ++
          [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs]) ∧
      lvls.mapM (VLevel.ofLevel Us) = some recursorLevels ∧
      stats.levels.mapM (VLevel.ofLevel Us) = some ctorLevels ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        ((stats.params.map fun arg => arg.abstractList H.binders).toList ++
          (motives.map fun arg => arg.abstractList H.binders).toList ++
          (minors.map fun arg => arg.abstractList H.binders).toList ++
          (indices.map fun arg => arg.abstractList H.binders).toList)
        leadingArgs ∧
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        ((stats.params.map fun arg => arg.abstractList H.binders).toList ++
          (H.allArgs.map fun arg => arg.abstractList H.binders).toList)
        ctorArgs := by
  have hsource := H.abstractedSourceLhs
  rw [htarget] at hsource
  rw [hsource] at Htr
  let leadingSource :=
    (stats.params.map fun arg => arg.abstractList H.binders).toList ++
    (motives.map fun arg => arg.abstractList H.binders).toList ++
    (minors.map fun arg => arg.abstractList H.binders).toList ++
    (indices.map fun arg => arg.abstractList H.binders).toList
  let ctorArgsSource :=
    (stats.params.map fun arg => arg.abstractList H.binders).toList ++
    (H.allArgs.map fun arg => arg.abstractList H.binders).toList
  let ctorSource :=
    mkAppN
      (mkAppN (.const ctor.name stats.levels)
        (stats.params.map fun arg => arg.abstractList H.binders))
      (H.allArgs.map fun arg => arg.abstractList H.binders)
  have hrecursorHead :
      ((mkAppN
        (mkAppN
          (mkAppN
            (mkAppN
              (.const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls)
              (stats.params.map fun arg => arg.abstractList H.binders))
            (motives.map fun arg => arg.abstractList H.binders))
          (minors.map fun arg => arg.abstractList H.binders))
        (indices.map fun arg => arg.abstractList H.binders)).app
          ctorSource).getAppFn =
        .const (Lean.mkRecName indTypes[ownerIdx]!.name) lvls := by
    simp only [Expr.getAppFn, Expr.getAppFn_mkAppN]
  rcases checkPositivityStep.TrExprS.constAppSpine Htr hrecursorHead with
    ⟨recursorLevels, translatedArgs, hrecursorSpine, hrecursorLevels,
      HtranslatedArgs⟩
  have HtranslatedArgs' : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (leadingSource ++ [ctorSource]) translatedArgs := by
    simpa only [leadingSource, ctorSource, Expr.getAppArgsList_app,
      Expr.getAppArgsList_mkAppN, Expr.getAppArgsList_const,
      List.nil_append, List.append_assoc]
      using HtranslatedArgs
  rcases checkPositivityStep.List.Forall₂.split_left HtranslatedArgs' with
    ⟨leadingArgs, translatedMajorTail, rfl, Hleading, HmajorTail⟩
  have hmajor : ∃ translatedMajor,
      translatedMajorTail = [translatedMajor] ∧
      TrExprS env Us (abstractForallContext domains Δ)
        ctorSource translatedMajor := by
    cases HmajorTail with
    | cons Hctor Hnil =>
      cases Hnil
      exact ⟨_, rfl, Hctor⟩
  rcases hmajor with ⟨translatedMajor, rfl, Hctor⟩
  have hctorHead : ctorSource.getAppFn =
      .const ctor.name stats.levels := by
    simp only [ctorSource, Expr.getAppFn_mkAppN, Expr.getAppFn]
  rcases checkPositivityStep.TrExprS.constAppSpine Hctor hctorHead with
    ⟨ctorLevels, ctorArgs, hctorSpine, hctorLevels, HctorArgs⟩
  have HctorArgs' : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ctorArgsSource ctorArgs := by
    simpa only [ctorArgsSource, ctorSource,
      Expr.getAppArgsList_mkAppN, Expr.getAppArgsList_const,
      List.nil_append,
      List.append_assoc] using HctorArgs
  have hmajorRebuild := VExpr.mkApps_getAppFnArgs translatedMajor
  rw [hctorSpine] at hmajorRebuild
  have hlhsRebuild := VExpr.mkApps_getAppFnArgs lhsBody
  rw [hrecursorSpine] at hlhsRebuild
  refine ⟨recursorLevels, leadingArgs, ctorLevels, ctorArgs, ?_,
    hrecursorLevels, hctorLevels, ?_, ?_⟩
  · rw [← hmajorRebuild] at hlhsRebuild
    exact hlhsRebuild.symm
  · simpa [leadingSource] using Hleading
  · simpa [ctorArgsSource] using HctorArgs'

/-- Proof-side construction record for the `VDefEq` corresponding to one
production `RecursorRule`. The executable record stores only its constructor,
field count, and RHS; this certificate makes the reconstructed LHS, common
telescope, and equation type an explicit refinement boundary. -/
structure BoundGeneratedRecursorRule.EquationTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (trEnv : VEnv) (Us : List Name) (Δ : VLCtx) (rule : VDefEq) where
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  domains_length : domains.length = H.binders.length
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  lhs_residual : TrExprS trEnv Us (abstractForallContext domains Δ)
    (H.sourceLhsBody.abstractList H.binders) lhsBody
  rhs_residual : TrExprS trEnv Us (abstractForallContext domains Δ)
    (H.sourceRhsBody.abstractList H.binders) rhsBody

/-- Any bound free-variable array selected by a duplicate-free closing list
becomes pointwise unique de Bruijn syntax after simultaneous abstraction. -/
theorem BoundFVarArray.abstractedUnique
    (B : BoundFVarArray root args)
    (hbinders : binders.Nodup)
    (hselected : ∀ fv ∈ B.fvars, fv ∈ binders) :
    ∀ e ∈ (args.map fun arg => arg.abstractList binders).toList,
      TrExprS.IsUnique e := by
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, heq⟩
  have hiArray : i < args.size := by simpa using hi
  rcases B.getElem_eq_fvar i hiArray with
    ⟨hiFvars, hsource⟩
  let fv := B.fvars[i]
  have hsource' : args[i] = .fvar fv := hsource
  have hmem : fv ∈ binders :=
    hselected fv (List.getElem_mem hiFvars)
  rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, hget⟩
  let index := binders.length - 1 - j
  have habstract := Expr.abstractList_fvar_getElem
    hbinders j hj (k := 0)
  rw [hget] at habstract
  have habstract' : (Expr.fvar fv).abstractList binders =
      .bvar index := by
    simpa [index] using habstract
  have hentry :
      (args.map fun arg => arg.abstractList binders).toList[i] =
        .bvar index := by
    calc
      _ = args[i].abstractList binders := by simp
      _ = (Expr.fvar fv).abstractList binders := by rw [hsource']
      _ = .bvar index := habstract'
  rw [← heq, hentry]
  trivial

/-- Common recursor parameters become closed de Bruijn variables under the
generated rule telescope, so their syntax translation is unique. -/
theorem BoundGeneratedRecursorRule.abstractedParamsUnique
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∀ e ∈ (stats.params.map fun arg =>
      arg.abstractList H.binders).toList,
      TrExprS.IsUnique e := by
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, heq⟩
  have hiArray : i < stats.params.size := by simpa using hi
  rcases H.params_bound.getElem_eq_fvar i hiArray with
    ⟨hiFvars, hsource⟩
  let fv := H.params_bound.fvars[i]
  have hsource' : stats.params[i] = .fvar fv := hsource
  have hselected : fv ∈ H.binders := by
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_left _ <| List.mem_append_left _ <|
      List.mem_append_left _ (List.getElem_mem hiFvars)
  rcases List.mem_iff_getElem.mp hselected with ⟨j, hj, hget⟩
  let paramVar := H.binders.length - 1 - j
  have habstract := Expr.abstractList_fvar_getElem
    H.binders_nodup j hj (k := 0)
  unfold BoundGeneratedRecursorRule.binders at hget
  rw [hget] at habstract
  have habstract' : (Expr.fvar fv).abstractList H.binders =
      .bvar paramVar := by
    simpa [BoundGeneratedRecursorRule.binders, paramVar,
      List.append_assoc] using habstract
  have hentry :
      (stats.params.map fun arg => arg.abstractList H.binders).toList[i] =
        .bvar paramVar := by
    calc
      _ = stats.params[i].abstractList H.binders := by simp
      _ = (Expr.fvar fv).abstractList H.binders := by rw [hsource']
      _ = .bvar paramVar := habstract'
  rw [← heq, hentry]
  trivial

theorem BoundGeneratedRecursorRule.abstractedMotivesUnique
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∀ e ∈ (motives.map fun arg => arg.abstractList H.binders).toList,
      TrExprS.IsUnique e := by
  apply H.motives_bound.abstractedUnique H.binders_nodup
  intro fv hfv
  simpa [BoundGeneratedRecursorRule.binders, List.append_assoc] using
    (List.mem_append_left H.all_args_bound.fvars <|
      List.mem_append_left H.minors_bound.fvars <|
        List.mem_append_right H.params_bound.fvars hfv)

theorem BoundGeneratedRecursorRule.abstractedMinorsUnique
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∀ e ∈ (minors.map fun arg => arg.abstractList H.binders).toList,
      TrExprS.IsUnique e := by
  apply H.minors_bound.abstractedUnique H.binders_nodup
  intro fv hfv
  simpa [BoundGeneratedRecursorRule.binders, List.append_assoc] using
    (List.mem_append_left H.all_args_bound.fvars <|
      List.mem_append_right
        (H.params_bound.fvars ++ H.motives_bound.fvars) hfv)

/-- Equation shape together with the exact translated constructor-field
suffix needed by the recursive-field and RHS certificates. -/
structure BoundGeneratedRecursorRule.IotaEquationTranslationCertificate
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (trEnv : VEnv) (Us : List Name) (Δ : VLCtx)
    (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  shape : IotaEquationCertificate decl block owner ctor rule
  domains_length : shape.domains.length = H.binders.length
  rhs_residual : TrExprS trEnv Us
    (abstractForallContext shape.domains Δ)
    (H.sourceRhsBody.abstractList H.binders) shape.rhsBody
  field_args : List.Forall₂
    (TrExprS trEnv Us (abstractForallContext shape.domains Δ))
    (H.allArgs.map fun arg => arg.abstractList H.binders).toList
    (shape.ctorArgs.drop decl.nparams)

/-- The retained source rule and its explicit `VDefEq` translation determine
the complete non-recursive iota-equation shape. Arity premises are deliberately
stated at the concrete array boundary so `RecursorCardinalityCertificate` can
discharge them without coupling this local theorem to the outer loop. -/
theorem BoundGeneratedRecursorRule.iotaEquationCertificate
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Htr : H.EquationTranslation trEnv Us Δ rule)
    (htarget : AddInductive.getIIndices stats H.target =
      (ownerIdx, indices))
    (hparams : stats.params.size = decl.nparams)
    (hmotives : motives.size = decl.types.length)
    (hminors : minors.size = decl.ownedConstructors.length)
    (hindices : indices.size = owner.numIndices)
    (hownerName : indTypes[ownerIdx]!.name = owner.name)
    (recursor : VConstVal)
    (hrecursorMem : recursor ∈ block.recursors)
    (hrecursorName : recursor.name = decl.recursorName owner)
    (hrecursorUvars : lvls.length = recursor.uvars)
    (ctor : VConstVal)
    (hctorName : sourceCtor.name = ctor.name)
    (hctorUvars : stats.levels.length = decl.uvars)
    (hruleUvars : rule.uvars = recursor.uvars) :
    Nonempty (H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule) := by
  rcases H.translatedLhsResidual htarget Htr.lhs_residual with
    ⟨recursorLevels, leadingArgs, ctorLevels, ctorArgs, hlhs,
      hrecursorLevels, hctorLevels, Hleading, HctorArgs⟩
  let paramSource :=
    (stats.params.map fun arg => arg.abstractList H.binders).toList
  let leadingTailSource :=
    (motives.map fun arg => arg.abstractList H.binders).toList ++
    (minors.map fun arg => arg.abstractList H.binders).toList ++
    (indices.map fun arg => arg.abstractList H.binders).toList
  let ctorTailSource :=
    (H.allArgs.map fun arg => arg.abstractList H.binders).toList
  have Hleading' : List.Forall₂
      (TrExprS trEnv Us (abstractForallContext Htr.domains Δ))
      (paramSource ++ leadingTailSource) leadingArgs := by
    simpa only [paramSource, leadingTailSource, List.append_assoc]
      using Hleading
  have HctorArgs' : List.Forall₂
      (TrExprS trEnv Us (abstractForallContext Htr.domains Δ))
      (paramSource ++ ctorTailSource) ctorArgs := by
    simpa only [paramSource, ctorTailSource] using HctorArgs
  rcases checkPositivityStep.List.Forall₂.split_left Hleading' with
    ⟨leadingParams, leadingTail, hleadingArgs, HleadingParams, _⟩
  rcases checkPositivityStep.List.Forall₂.split_left HctorArgs' with
    ⟨ctorParams, ctorTail, hctorArgs, HctorParams, HctorTail⟩
  have hparamTargets : leadingParams = ctorParams :=
    Lean4Lean.VerifyInductive.List.Forall₂.targets_eq_of_unique
      HleadingParams HctorParams (by
        simpa only [paramSource] using H.abstractedParamsUnique)
  have hparamSourceLength : paramSource.length = decl.nparams := by
    simp [paramSource, hparams]
  have hleadingParamsLength : leadingParams.length = decl.nparams := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      HleadingParams
    omega
  have hctorParamsLength : ctorParams.length = decl.nparams := by
    rw [← hparamTargets]
    exact hleadingParamsLength
  have hleadingLength : leadingArgs.length = decl.nparams +
      decl.types.length + decl.ownedConstructors.length + owner.numIndices := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hleading
    simpa [hparams, hmotives, hminors, hindices, Nat.add_assoc]
      using hlen.symm
  have hctorLength : ctorArgs.length = decl.nparams + H.allArgs.size := by
    have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' HctorArgs
    simpa [hparams] using hlen.symm
  have hbindersLength : H.binders.length = stats.params.size + motives.size +
      minors.size + H.allArgs.size := by
    have hp : stats.params.size = H.params_bound.fvars.length := by
      simpa using congrArg Array.size H.params_bound.expressions
    have hm : motives.size = H.motives_bound.fvars.length := by
      simpa using congrArg Array.size H.motives_bound.expressions
    have hmi : minors.size = H.minors_bound.fvars.length := by
      simpa using congrArg Array.size H.minors_bound.expressions
    have ha : H.allArgs.size = H.all_args_bound.fvars.length := by
      simpa using congrArg Array.size H.all_args_bound.expressions
    unfold BoundGeneratedRecursorRule.binders
    simp only [List.length_append]
    omega
  let Hshape : IotaEquationCertificate decl block owner ctor rule := {
    recursor := recursor
    recursor_mem := hrecursorMem
    recursor_name := hrecursorName
    rule_uvars := hruleUvars
    domains := Htr.domains
    lhsBody := Htr.lhsBody
    rhsBody := Htr.rhsBody
    typeBody := Htr.typeBody
    lhs_wrapped := Htr.lhs_wrapped
    rhs_wrapped := Htr.rhs_wrapped
    type_wrapped := Htr.type_wrapped
    recursorLevels := recursorLevels
    leadingArgs := leadingArgs
    ctorLevels := ctorLevels
    ctorArgs := ctorArgs
    lhs_pattern := by
      rw [hrecursorName, VInductDecl.recursorName_eq_mkRecName]
      simpa [hownerName, hctorName] using hlhs
    recursor_levels := by
      rw [← hrecursorUvars]
      exact (checkPositivityStep.List.mapM_some_length
        hrecursorLevels).symm
    ctor_levels := by
      rw [← hctorUvars]
      exact (checkPositivityStep.List.mapM_some_length hctorLevels).symm
    leading_arity := hleadingLength
    constructor_arity := by omega
    parameter_args := by
      rw [hleadingArgs, hctorArgs, ← hparamTargets]
      rw [← hleadingParamsLength]
      simp
    domains_arity := by
      rw [Htr.domains_length, hbindersLength, hparams, hmotives, hminors,
        hctorLength]
      omega }
  refine ⟨{
    shape := Hshape
    domains_length := Htr.domains_length
    rhs_residual := Htr.rhs_residual
    field_args := ?_ }⟩
  change List.Forall₂
    (TrExprS trEnv Us (abstractForallContext Htr.domains Δ))
    (H.allArgs.map fun arg => arg.abstractList H.binders).toList
    (ctorArgs.drop decl.nparams)
  rw [hctorArgs]
  simpa [ctorTailSource, hctorParamsLength] using HctorTail

/-- Outer-loop form of `iotaEquationCertificate`: the header statistics and
`mkRecInfos` cardinality certificates discharge every local arity premise,
while source declaration translation identifies the selected mutual owner. -/
theorem BoundGeneratedRecursorRule.iotaEquationCertificate_ofCardinality
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Htr : H.EquationTranslation trEnv Us Δ rule)
    {envTypes envCtors : VEnv}
    (Hdecl : TrInductDeclCore sourceEnv sourceParams nparams
      indTypes.toList isUnsafe decl envTypes envCtors)
    (Hstats : checkPositivityStep.ValidAppStatsWF statsEnv statsParams statsCtx
      stats decl depth)
    (Hcard : RecursorCardinalityCertificate stats recInfos decl)
    (hmotives : motives = recInfos.map (·.motive))
    (hminors : minors = recInfos.flatMap (·.minors))
    (hvalid : AddInductive.isValidIndApp? stats H.target = some ownerIdx)
    (htarget : AddInductive.getIIndices stats H.target =
      (ownerIdx, indices))
    (hownerLt : ownerIdx < decl.types.length)
    (howner : decl.types[ownerIdx]'hownerLt = owner)
    (recursor : VConstVal)
    (hrecursorMem : recursor ∈ block.recursors)
    (hrecursorName : recursor.name = decl.recursorName owner)
    (hrecursorUvars : lvls.length = recursor.uvars)
    (ctor : VConstVal)
    (hctorName : sourceCtor.name = ctor.name)
    (hruleUvars : rule.uvars = recursor.uvars) :
    Nonempty (H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule) := by
  have hdeclOwner : ownerIdx < decl.types.length := hownerLt
  have hsourceOwner : ownerIdx < indTypes.size := by
    have hlen := Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hdecl
    have hsize : indTypes.size = decl.types.length := by simpa using hlen
    rw [hsize]
    exact hdeclOwner
  have Howner := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hdecl
    ownerIdx (by simpa using hsourceOwner) hdeclOwner
  have hownerName : indTypes[ownerIdx]!.name = owner.name := by
    have htranslated : decl.types[ownerIdx].name =
        indTypes[ownerIdx].name := by
      simpa using Howner.header.name
    rw [← howner]
    simpa [Array.getElem!_eq_getD, Array.getD, hsourceOwner] using
      htranslated.symm
  have hindexArity : indices.size = owner.numIndices := by
    have h := checkPositivityStep.getIIndices.index_arity hvalid
    rw [htarget] at h
    have hlen : stats.nindices.size = decl.types.length := by
      have := congrArg List.length Hstats.indices
      simpa using this
    have hget := congrArg (fun xs => xs[ownerIdx]?) Hstats.indices
    have hn : stats.nindices[ownerIdx]! =
        decl.types[ownerIdx].numIndices := by
      simpa [Array.getElem!_eq_getD, Array.getD, hownerLt, hlen] using hget
    calc
      indices.size = stats.nindices[ownerIdx]! := h
      _ = decl.types[ownerIdx].numIndices := hn
      _ = owner.numIndices := by rw [howner]
  apply H.iotaEquationCertificate (recursor := recursor) (ctor := ctor)
    Htr htarget Hcard.params
  · rw [hmotives]
    exact Hcard.motives
  · rw [hminors]
    exact Hcard.minors
  · exact hindexArity
  · exact hownerName
  · exact hrecursorMem
  · exact hrecursorName
  · exact hrecursorUvars
  · exact hctorName
  · exact Hstats.levels
  · exact hruleUvars

/-- Simultaneous abstraction turns the selected minor free variable into one
in-scope de Bruijn variable and preserves the field/result application
spines pointwise. -/
theorem BoundGeneratedRecursorRule.abstractedSourceRhs
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∃ minorVar,
      minorVar < H.binders.length ∧
      H.sourceRhsBody.abstractList H.binders =
        mkAppN
          (mkAppN (.bvar minorVar)
            (H.allArgs.map fun arg => arg.abstractList H.binders))
          (H.recursiveResults.map fun result =>
            result.abstractList H.binders) := by
  rcases H.minors_bound.getElem_eq_fvar minorIdx H.minor_valid with
    ⟨hiFvars, hminor⟩
  let fv := H.minors_bound.fvars[minorIdx]
  have hmem : fv ∈ H.binders := by
    unfold BoundGeneratedRecursorRule.binders fv
    simp [List.getElem_mem hiFvars]
  rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, hget⟩
  let minorVar := H.binders.length - 1 - i
  refine ⟨minorVar, by omega, ?_⟩
  have habstract := Expr.abstractList_fvar_getElem
    H.binders_nodup i hi (k := 0)
  unfold BoundGeneratedRecursorRule.binders at hget
  rw [hget] at habstract
  have habstract' : (Expr.fvar fv).abstractList H.binders =
      .bvar minorVar := by
    simpa [BoundGeneratedRecursorRule.binders, minorVar] using habstract
  have hminorBang : minors[minorIdx]! = .fvar fv := by
    rw [Array.getElem!_eq_getD, Array.getD, dif_pos H.minor_valid]
    exact hminor
  unfold BoundGeneratedRecursorRule.sourceRhsBody
  rw [Expr.abstractList_mkAppN, Expr.abstractList_mkAppN,
    hminorBang, habstract']

/-- The selected minor has a canonical de Bruijn position in the closed rule
telescope: constructor fields are newer, and the remaining minors occur in
reverse order immediately behind them. -/
theorem BoundGeneratedRecursorRule.abstractedSourceRhsAtMinor
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    let minorVar := H.all_args_bound.fvars.length +
      (H.minors_bound.fvars.length - 1 - minorIdx)
    H.sourceRhsBody.abstractList H.binders =
      mkAppN
        (mkAppN (.bvar minorVar)
          (H.allArgs.map fun arg => arg.abstractList H.binders))
        (H.recursiveResults.map fun result =>
          result.abstractList H.binders) := by
  rcases H.minors_bound.getElem_eq_fvar minorIdx H.minor_valid with
    ⟨hiFvars, hminor⟩
  let fv := H.minors_bound.fvars[minorIdx]
  let outerPrefix := H.params_bound.fvars ++ H.motives_bound.fvars
  let before := outerPrefix ++ H.minors_bound.fvars.take minorIdx
  let after := H.minors_bound.fvars.drop (minorIdx + 1) ++
    H.all_args_bound.fvars
  have hminorDecomp : H.minors_bound.fvars =
      H.minors_bound.fvars.take minorIdx ++ fv ::
        H.minors_bound.fvars.drop (minorIdx + 1) := by
    calc
      H.minors_bound.fvars =
          H.minors_bound.fvars.take (minorIdx + 1) ++
            H.minors_bound.fvars.drop (minorIdx + 1) :=
        (List.take_append_drop (minorIdx + 1) _).symm
      _ = (H.minors_bound.fvars.take minorIdx ++ [fv]) ++
          H.minors_bound.fvars.drop (minorIdx + 1) := by
        rw [List.take_succ_eq_append_getElem hiFvars]
      _ = H.minors_bound.fvars.take minorIdx ++ fv ::
          H.minors_bound.fvars.drop (minorIdx + 1) := by simp
  have hbindersDecomp : H.binders = before ++ fv :: after := by
    change ((outerPrefix ++ H.minors_bound.fvars) ++
      H.all_args_bound.fvars) = before ++ fv :: after
    rw [hminorDecomp]
    dsimp only [before, after]
    simp only [List.append_assoc]
    rw [List.cons_append]
  have hnodup : (before ++ fv :: after).Nodup := by
    rw [← hbindersDecomp]
    exact H.binders_nodup
  have habstract := Expr.abstractList_fvar_getElem
    hnodup before.length (by simp) (k := 0)
  have habstract' : (Expr.fvar fv).abstractList
      (before ++ fv :: after) =
      .bvar ((before ++ fv :: after).length - 1 - before.length) := by
    simpa using habstract
  let minorVar := H.all_args_bound.fvars.length +
    (H.minors_bound.fvars.length - 1 - minorIdx)
  have hafterLength : after.length = minorVar := by
    unfold after minorVar
    simp only [List.length_append, List.length_drop]
    omega
  have habstractFinal : (Expr.fvar fv).abstractList H.binders =
      .bvar minorVar := by
    rw [hbindersDecomp]
    simpa [hafterLength] using habstract'
  have hminorBang : minors[minorIdx]! = .fvar fv := by
    rw [Array.getElem!_eq_getD, Array.getD, dif_pos H.minor_valid]
    exact hminor
  unfold BoundGeneratedRecursorRule.sourceRhsBody
  rw [Expr.abstractList_mkAppN, Expr.abstractList_mkAppN,
    hminorBang, habstractFinal]

theorem BoundGeneratedRecursorRule.abstractedSourceRhsAtMinorArray
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    let minorVar := H.allArgs.size + (minors.size - 1 - minorIdx)
    H.sourceRhsBody.abstractList H.binders =
      mkAppN
        (mkAppN (.bvar minorVar)
          (H.allArgs.map fun arg => arg.abstractList H.binders))
        (H.recursiveResults.map fun result =>
          result.abstractList H.binders) := by
  have hall : H.all_args_bound.fvars.length = H.allArgs.size := by
    have h := congrArg Array.size H.all_args_bound.expressions
    simpa using h.symm
  have hminors : H.minors_bound.fvars.length = minors.size := by
    have h := congrArg Array.size H.minors_bound.expressions
    simpa using h.symm
  simpa [hall, hminors] using H.abstractedSourceRhsAtMinor

/-- Translation of the exact production rule RHS exposes the abstract rule
telescope and leaves only the simultaneously abstracted minor application as
the residual translation obligation. -/
theorem BoundGeneratedRecursorRule.translatedRhsShape
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (Htr : TrExprS env Us Δ rule.rhs rhs) :
    ∃ domains rhsBody,
      domains.length = H.binders.length ∧
      rhs = VExpr.wrapLams domains rhsBody ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.sourceRhsBody.abstractList H.binders) rhsBody :=
  TrExprS.lambdaTelescope_shape_with_context H.rhsLambdaTelescope Htr

theorem BoundGeneratedRecursorRule.translatedRhsShape_noFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (Htr : TrExprS env Us Δ rule.rhs rhs)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false) :
    ∃ domains rhsBody,
      domains.length = H.binders.length ∧
      rhs = VExpr.wrapLams domains rhsBody ∧
      TrExprS env Us (abstractForallContext domains Δ)
        (H.sourceRhsBody.abstractList H.binders) rhsBody ∧
      ∀ dom ∈ domains, dom.containsAnyConst recursors = false :=
  TrExprS.lambdaTelescope_shape_with_context_noFresh
    hfresh hctx hproj H.rhsLambdaTelescope Htr

/-- Inverting the translated residual yields the exact abstract minor spine,
split between translated constructor fields and translated recursive
results. -/
theorem BoundGeneratedRecursorRule.translatedRhsResidual
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (hdomains : domains.length = H.binders.length)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceRhsBody.abstractList H.binders) rhsBody) :
    ∃ minorVar fieldArgs recursiveResults,
      minorVar < domains.length ∧
      List.Forall₂ (TrExprS env Us (abstractForallContext domains Δ))
        (H.allArgs.map fun arg => arg.abstractList H.binders).toList
        fieldArgs ∧
      List.Forall₂ (TrExprS env Us (abstractForallContext domains Δ))
        (H.recursiveResults.map fun result =>
          result.abstractList H.binders).toList recursiveResults ∧
      rhsBody = VExpr.mkApps (.bvar minorVar)
        (fieldArgs ++ recursiveResults) := by
  rcases H.abstractedSourceRhs with ⟨minorVar, hminor, habstract⟩
  rw [habstract] at Htr
  have Houter : TrExprS env Us (abstractForallContext domains Δ)
      (Expr.mkAppList
        (mkAppN (.bvar minorVar)
          (H.allArgs.map fun arg => arg.abstractList H.binders))
        (H.recursiveResults.map fun result =>
          result.abstractList H.binders).toList) rhsBody := by
    simpa only [mkAppN, Expr.mkAppList_eq_foldl,
      ← Array.foldl_toList, Array.toList_map,
      Expr.foldl_mkApp_eq] using Htr
  rcases checkPositivityStep.TrExprS.mkAppList_inv Houter with
    ⟨minorApp, recursiveResults, HminorApp, Hresults, hrhs⟩
  have Hinner : TrExprS env Us (abstractForallContext domains Δ)
      (Expr.mkAppList (.bvar minorVar)
        (H.allArgs.map fun arg => arg.abstractList H.binders).toList)
      minorApp := by
    simpa only [mkAppN, Expr.mkAppList_eq_foldl,
      ← Array.foldl_toList, Array.toList_map,
      Expr.foldl_mkApp_eq] using HminorApp
  rcases checkPositivityStep.TrExprS.mkAppList_inv Hinner with
    ⟨minor, fieldArgs, Hminor, Hfields, hminorApp⟩
  have hminorEq := TrExprS.bvar_eq_of_abstractForallContext Hminor
    (by omega)
  subst minor
  refine ⟨minorVar, fieldArgs, recursiveResults, by omega,
    Hfields, Hresults, ?_⟩
  rw [hrhs, hminorApp]
  simp [VExpr.mkApps, List.foldl_append]

/-- The rule certificate itself supplies the selected-field membership needed
to guard every recursively generated result after closing the rule telescope. -/
theorem BoundGeneratedRecursorRule.abstractedIotaResults_ofFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {recursiveArgs recursiveResults : List VExpr}
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (Hresults : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveResults.map fun result =>
        result.abstractList H.binders).toList recursiveResults)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursive_calls.RecursorsPresent recursors)
    (hdomains : domains.length = H.binders.length) :
    IotaRecursiveResultsCertificate recursors
      (recursiveArgs.filterMap VExpr.bvarHead?)
      recursiveArgs recursiveResults := by
  apply H.recursive_calls.abstractedIotaResults_ofFresh
    H.recursive_args_bound Hargs Hresults hfresh hctx hproj hrecursor
      H.binders_nodup hdomains
  intro fv hfv
  have hfield : fv ∈ H.all_args_bound.fvars :=
    H.recursive_args_bound.fvars_subset_of_sublist H.all_args_bound
      H.recursive_args_sublist hfv
  unfold BoundGeneratedRecursorRule.binders
  exact List.mem_append_right _ hfield

/-- Every de Bruijn head obtained from a translated selected constructor
field is in the closed rule telescope. -/
theorem BoundGeneratedRecursorRule.abstractedRecursiveHeadsInScope
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {recursiveArgs : List VExpr}
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (hdomains : domains.length = H.binders.length) :
    ∀ field ∈ recursiveArgs.filterMap VExpr.bvarHead?,
      field < domains.length := by
  intro field hfield
  rcases List.mem_filterMap.mp hfield with ⟨arg, harg, hhead⟩
  rcases List.mem_iff_getElem.mp harg with ⟨i, hiArgs, hargEq⟩
  have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hargs
  have hiSource : i <
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList.length :=
    by omega
  have hiArray : i < H.recursiveArgs.size := by simpa using hiSource
  have Harg := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i hiSource hiArgs
  rcases H.recursive_args_bound.getElem_eq_fvar i hiArray with
    ⟨hiFvars, hsource⟩
  let fv := H.recursive_args_bound.fvars[i]
  have hsource' : H.recursiveArgs[i] = .fvar fv := hsource
  have hselectedAll : fv ∈ H.all_args_bound.fvars :=
    H.recursive_args_bound.fvars_subset_of_sublist H.all_args_bound
      H.recursive_args_sublist (List.getElem_mem hiFvars)
  have hselected : fv ∈ H.binders := by
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_right _ hselectedAll
  rcases List.mem_iff_getElem.mp hselected with ⟨j, hj, hget⟩
  let fieldVar := H.binders.length - 1 - j
  have habstract := Expr.abstractList_fvar_getElem
    H.binders_nodup j hj (k := 0)
  unfold BoundGeneratedRecursorRule.binders at hget
  rw [hget] at habstract
  have habstract' : (Expr.fvar fv).abstractList H.binders =
      .bvar fieldVar := by
    simpa [BoundGeneratedRecursorRule.binders, fieldVar] using habstract
  have hsourceAbstract :
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList[i] =
        .bvar fieldVar := by
    calc
      _ = H.recursiveArgs[i].abstractList H.binders := by simp
      _ = (Expr.fvar fv).abstractList H.binders := by rw [hsource']
      _ = .bvar fieldVar := habstract'
  rw [hsourceAbstract] at Harg
  have hfieldVarBound : fieldVar < domains.length := by
    rw [hdomains]
    omega
  have htranslated := TrExprS.bvar_eq_of_abstractForallContext
    Harg hfieldVarBound
  rw [hargEq] at htranslated
  have hfieldEq : field = fieldVar := by
    rw [htranslated] at hhead
    unfold VExpr.bvarHead? at hhead
    exact (Option.some.inj hhead).symm
  rw [hfieldEq]
  exact hfieldVarBound

/-- Closing the generated rule turns every constructor-field source into a
de Bruijn variable, hence into syntax with a unique translation. -/
theorem BoundGeneratedRecursorRule.abstractedAllArgsUnique
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∀ e ∈ (H.allArgs.map fun arg => arg.abstractList H.binders).toList,
      TrExprS.IsUnique e := by
  intro e he
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, heq⟩
  have hiArray : i < H.allArgs.size := by simpa using hi
  rcases H.all_args_bound.getElem_eq_fvar i hiArray with
    ⟨hiFvars, hsource⟩
  let fv := H.all_args_bound.fvars[i]
  have hsource' : H.allArgs[i] = .fvar fv := hsource
  have hselected : fv ∈ H.binders := by
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_right _ (List.getElem_mem hiFvars)
  rcases List.mem_iff_getElem.mp hselected with ⟨j, hj, hget⟩
  let fieldVar := H.binders.length - 1 - j
  have habstract := Expr.abstractList_fvar_getElem
    H.binders_nodup j hj (k := 0)
  unfold BoundGeneratedRecursorRule.binders at hget
  rw [hget] at habstract
  have habstract' : (Expr.fvar fv).abstractList H.binders =
      .bvar fieldVar := by
    simpa [BoundGeneratedRecursorRule.binders, fieldVar] using habstract
  have hentry :
      (H.allArgs.map fun arg => arg.abstractList H.binders).toList[i] =
        .bvar fieldVar := by
    calc
      _ = H.allArgs[i].abstractList H.binders := by simp
      _ = (Expr.fvar fv).abstractList H.binders := by rw [hsource']
      _ = .bvar fieldVar := habstract'
  rw [← heq, hentry]
  trivial

/-- Every translated ordinary constructor field is a bound variable in the
closed rule telescope.  Hence it is recursor-free in any translation
environment, including the post-recursor environment used for the equation. -/
theorem BoundGeneratedRecursorRule.abstractedAllArgsNoConsts
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.allArgs.map fun arg => arg.abstractList H.binders).toList args)
    (hdomains : domains.length = H.binders.length) :
    ∀ arg ∈ args, arg.containsAnyConst names = false := by
  intro arg harg
  rcases List.mem_iff_getElem.mp harg with ⟨i, hiArgs, hargEq⟩
  have hlen := Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hargs
  have hiSource : i <
      (H.allArgs.map fun value => value.abstractList H.binders).toList.length :=
    by omega
  have hiArray : i < H.allArgs.size := by simpa using hiSource
  have Harg := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hargs i hiSource hiArgs
  rcases H.all_args_bound.getElem_eq_fvar i hiArray with
    ⟨hiFvars, hsource⟩
  let fv := H.all_args_bound.fvars[i]
  have hselected : fv ∈ H.binders := by
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_right _ (List.getElem_mem hiFvars)
  rcases List.mem_iff_getElem.mp hselected with ⟨j, hj, hget⟩
  let fieldVar := H.binders.length - 1 - j
  have habstract := Expr.abstractList_fvar_getElem
    H.binders_nodup j hj (k := 0)
  unfold BoundGeneratedRecursorRule.binders at hget
  rw [hget] at habstract
  have hsourceAbstract :
      (H.allArgs.map fun value => value.abstractList H.binders).toList[i] =
        .bvar fieldVar := by
    calc
      _ = H.allArgs[i].abstractList H.binders := by simp
      _ = (Expr.fvar fv).abstractList H.binders := by rw [hsource]
      _ = .bvar fieldVar := by
        simpa [BoundGeneratedRecursorRule.binders, fieldVar,
          List.append_assoc] using habstract
  rw [hsourceAbstract] at Harg
  have hbound : fieldVar < domains.length := by rw [hdomains]; omega
  have htranslated := TrExprS.bvar_eq_of_abstractForallContext Harg hbound
  rw [← hargEq, htranslated]
  rfl

/-- Selected recursive fields inherit translation uniqueness from the full
constructor-field array after simultaneous closing. -/
theorem BoundGeneratedRecursorRule.abstractedRecursiveArgsUnique
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule) :
    ∀ e ∈ (H.recursiveArgs.map fun arg =>
      arg.abstractList H.binders).toList,
      TrExprS.IsUnique e := by
  intro e he
  apply H.abstractedAllArgsUnique e
  have hsub := H.recursive_args_sublist.map
    (fun arg => arg.abstractList H.binders)
  exact List.Sublist.mem he (by simpa using hsub)

/-- Assemble the exact iota RHS from a post-installation translation while
keeping the two genuinely freshness-sensitive facts explicit: ordinary
constructor fields contain no recursor constants, and every generated
recursive result has the guarded call shape.  This formulation does not ask
the pre-recursor environment to translate the recursive calls themselves. -/
theorem BoundGeneratedRecursorRule.iotaRhsCertificateFor
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {fieldArgs recursiveArgs : List VExpr}
    (hdomains : domains.length = H.binders.length)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceRhsBody.abstractList H.binders) rhsBody)
    (Hfields : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.allArgs.map fun arg => arg.abstractList H.binders).toList
      fieldArgs)
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (hfieldsFree : ∀ field ∈ fieldArgs,
      field.containsAnyConst recursors = false)
    (Hresults : ∀ translatedResults,
      List.Forall₂
        (TrExprS env Us (abstractForallContext domains Δ))
        (H.recursiveResults.map fun result =>
          result.abstractList H.binders).toList translatedResults →
      IotaRecursiveResultsCertificate recursors
        (recursiveArgs.filterMap VExpr.bvarHead?) recursiveArgs
        translatedResults) :
    Nonempty (IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) := by
  rcases H.translatedRhsResidual hdomains Htr with
    ⟨minorVar, generatedFields, recursiveResults, hminor,
      HgeneratedFields, HtranslatedResults, hrhs⟩
  have hfieldsEq : generatedFields = fieldArgs :=
    Lean4Lean.VerifyInductive.List.Forall₂.targets_eq_of_unique
      HgeneratedFields Hfields H.abstractedAllArgsUnique
  subst generatedFields
  exact ⟨{
    minorVar := minorVar
    minor_in_scope := hminor
    recursiveResults := recursiveResults
    rhs_eq := hrhs
    fieldVars := recursiveArgs.filterMap VExpr.bvarHead?
    fieldVars_eq := rfl
    fields_in_scope := H.abstractedRecursiveHeadsInScope Hargs hdomains
    fields_recursor_free := hfieldsFree
    recursive_results := Hresults recursiveResults HtranslatedResults
  }⟩

/-- Assemble the abstract iota RHS certificate directly from the translated
production RHS and the independently translated selected-field spine. -/
theorem BoundGeneratedRecursorRule.iotaRhsCertificate_ofFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {recursiveArgs : List VExpr}
    (hdomains : domains.length = H.binders.length)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceRhsBody.abstractList H.binders) rhsBody)
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursive_calls.RecursorsPresent recursors) :
    ∃ fieldArgs,
      Nonempty (IotaRhsCertificate recursors domains fieldArgs recursiveArgs
        rhsBody) := by
  rcases H.translatedRhsResidual hdomains Htr with
    ⟨minorVar, fieldArgs, recursiveResults, hminor, Hfields,
      Hresults, hrhs⟩
  refine ⟨fieldArgs, ⟨{
    minorVar := minorVar
    minor_in_scope := hminor
    recursiveResults := recursiveResults
    rhs_eq := hrhs
    fieldVars := recursiveArgs.filterMap VExpr.bvarHead?
    fieldVars_eq := rfl
    fields_in_scope := H.abstractedRecursiveHeadsInScope Hargs hdomains
    fields_recursor_free :=
      checkPositivityStep.List.Forall₂.targets_noFreshConsts
        Hfields hfresh hctx hproj
    recursive_results := H.abstractedIotaResults_ofFresh
      Hargs Hresults hfresh hctx hproj hrecursor hdomains
  }⟩⟩

/-- Exact-spine form of `iotaRhsCertificate_ofFresh`. Syntactic uniqueness of
the closed constructor fields identifies the RHS inversion output with the
field spine shared by the equation and recursive-field certificates. -/
theorem BoundGeneratedRecursorRule.iotaRhsCertificateFor_ofFresh
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      ctor minorIdx rule)
    {fieldArgs recursiveArgs : List VExpr}
    (hdomains : domains.length = H.binders.length)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (H.sourceRhsBody.abstractList H.binders) rhsBody)
    (Hfields : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.allArgs.map fun arg => arg.abstractList H.binders).toList
      fieldArgs)
    (Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (hfresh : ∀ name ∈ recursors, env.constants name = none)
    (hctx : VLCtx.NoIndConsts recursors
      (abstractForallContext domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst recursors = false →
      e''.containsAnyConst recursors = false)
    (hrecursor : H.recursive_calls.RecursorsPresent recursors) :
    Nonempty (IotaRhsCertificate recursors domains fieldArgs recursiveArgs
      rhsBody) := by
  rcases H.translatedRhsResidual hdomains Htr with
    ⟨minorVar, generatedFields, recursiveResults, hminor,
      HgeneratedFields, Hresults, hrhs⟩
  have hfieldsEq : generatedFields = fieldArgs :=
    Lean4Lean.VerifyInductive.List.Forall₂.targets_eq_of_unique
      HgeneratedFields Hfields H.abstractedAllArgsUnique
  subst generatedFields
  exact ⟨{
    minorVar := minorVar
    minor_in_scope := hminor
    recursiveResults := recursiveResults
    rhs_eq := hrhs
    fieldVars := recursiveArgs.filterMap VExpr.bvarHead?
    fieldVars_eq := rfl
    fields_in_scope := H.abstractedRecursiveHeadsInScope Hargs hdomains
    fields_recursor_free :=
      checkPositivityStep.List.Forall₂.targets_noFreshConsts
        Hfields hfresh hctx hproj
    recursive_results := H.abstractedIotaResults_ofFresh
      Hargs Hresults hfresh hctx hproj hrecursor hdomains
  }⟩

/-- Final pointwise semantic bridge for a generated rule. The equation and
recursive-field certificates remain independent inputs; all executable RHS
shape and guardedness obligations are discharged here. -/
theorem BoundGeneratedRecursorRule.iotaRule_ofCertificates
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hshape : IotaEquationCertificate decl block owner ctor rule)
    {fields : List (decl.RecursiveField env)}
    {recursiveArgs : List VExpr}
    (Hfield : IotaFieldCertificate env decl
      (Hshape.ctorArgs.drop decl.nparams) fields recursiveArgs)
    (hdomains : Hshape.domains.length = H.binders.length)
    (Htr : TrExprS trEnv Us
      (abstractForallContext Hshape.domains Δ)
      (H.sourceRhsBody.abstractList H.binders) Hshape.rhsBody)
    (Hfields : List.Forall₂
      (TrExprS trEnv Us (abstractForallContext Hshape.domains Δ))
      (H.allArgs.map fun arg => arg.abstractList H.binders).toList
      (Hshape.ctorArgs.drop decl.nparams))
    (Hargs : List.Forall₂
      (TrExprS trEnv Us (abstractForallContext Hshape.domains Δ))
      (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
      recursiveArgs)
    (hfresh : ∀ name ∈ block.recursors.map (·.name),
      trEnv.constants name = none)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name))
      (abstractForallContext Hshape.domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (block.recursors.map (·.name)) = false →
      e''.containsAnyConst (block.recursors.map (·.name)) = false)
    (hrecursor : H.recursive_calls.RecursorsPresent
      (block.recursors.map (·.name))) :
    Nonempty (decl.IotaRule env block owner ctor rule) := by
  have Hrhs := H.iotaRhsCertificateFor_ofFresh hdomains Htr Hfields Hargs
    hfresh hctx hproj hrecursor
  rcases Hrhs with ⟨Hrhs⟩
  exact ⟨VInductDecl.IotaRule.ofCertificates Hshape Hfield Hrhs⟩

/-- Complete pointwise bridge from an explicitly reconstructed equation and
the executable recursive-field selection trace to the independent iota-rule
judgment. This removes `IotaEquationCertificate` and `IotaFieldCertificate`
as arbitrary external premises at the generated-rule boundary. -/
theorem BoundGeneratedRecursorRule.iotaRule_ofTranslationCertificate
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hequation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule)
    (Hselection : RecursorFieldSelections semanticEnv decl H.allArgs
      H.recursiveArgs selections)
    {recursiveArgs : List VExpr}
    (Hargs : List.Forall₂
      (TrExprS trEnv Us
        (abstractForallContext Hequation.shape.domains Δ))
      (H.recursiveArgs.map fun arg =>
        arg.abstractList H.binders).toList recursiveArgs)
    (hfresh : ∀ name ∈ block.recursors.map (·.name),
      trEnv.constants name = none)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name))
      (abstractForallContext Hequation.shape.domains Δ))
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (block.recursors.map (·.name)) = false →
      e''.containsAnyConst (block.recursors.map (·.name)) = false)
    (hrecursor : H.recursive_calls.RecursorsPresent
      (block.recursors.map (·.name))) :
    Nonempty (decl.IotaRule semanticEnv block owner ctor rule) := by
  let Hselection' := Hselection.map
    (fun arg => arg.abstractList H.binders)
  rcases Hselection'.exists_materialization Hargs with ⟨fields, Hfields⟩
  let Hfield := Hfields.iotaFieldCertificate Hselection'
    Hequation.field_args Hargs H.abstractedRecursiveArgsUnique
  exact H.iotaRule_ofCertificates Hequation.shape Hfield
    Hequation.domains_length Hequation.rhs_residual
    Hequation.field_args Hargs hfresh hctx hproj hrecursor

/-- Complete local translation payload for one generated source rule. Unlike
`IotaRule`, every field refers directly to retained executable data; global
recursor installation and freshness are supplied once for the enclosing
batch. -/
structure BoundGeneratedRecursorRule.IotaRuleTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (trEnv : VEnv) (Us : List Name) (Δ : VLCtx)
    (semanticEnv : VEnv) (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  equation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
    owner ctor rule
  selections : List (RecursorRecursiveDomain semanticEnv decl)
  selection : RecursorFieldSelections semanticEnv decl H.allArgs
    H.recursiveArgs selections
  recursiveArgs : List VExpr
  args : List.Forall₂
    (TrExprS trEnv Us
      (abstractForallContext equation.shape.domains Δ))
    (H.recursiveArgs.map fun arg => arg.abstractList H.binders).toList
    recursiveArgs
  context_free : VLCtx.NoIndConsts (block.recursors.map (·.name))
    (abstractForallContext equation.shape.domains Δ)

/-- Stage-correct local payload for a generated iota rule.  The equation and
recursive-result syntax are translated after the recursors have been
installed.  Freshness is retained only through the two consequences actually
needed by `GuardedIota`: ordinary fields are recursor-free, and translated
recursive results have the guarded call shape. -/
structure BoundGeneratedRecursorRule.StagedIotaRuleTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (trEnv : VEnv) (Us : List Name) (Δ : VLCtx)
    (semanticEnv : VEnv) (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  equation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
    owner ctor rule
  selections : List (RecursorRecursiveDomain semanticEnv decl)
  selection : RecursorFieldSelections semanticEnv decl H.allArgs
    H.recursiveArgs selections
  recursiveArgs : List VExpr
  args : List.Forall₂
    (TrExprS trEnv Us
      (abstractForallContext equation.shape.domains Δ))
    (H.recursiveArgs.map fun arg =>
      arg.abstractList H.binders).toList recursiveArgs
  fields_recursor_free : ∀ field ∈
      equation.shape.ctorArgs.drop decl.nparams,
    field.containsAnyConst (block.recursors.map (·.name)) = false
  recursive_results : ∀ translatedResults,
    List.Forall₂
      (TrExprS trEnv Us
        (abstractForallContext equation.shape.domains Δ))
      (H.recursiveResults.map fun result =>
        result.abstractList H.binders).toList translatedResults →
    IotaRecursiveResultsCertificate (block.recursors.map (·.name))
      (recursiveArgs.filterMap VExpr.bvarHead?) recursiveArgs
      translatedResults

/-- Consume the stage-correct payload without any pre-installation
translation of a generated recursive call. -/
theorem BoundGeneratedRecursorRule.iotaRule_ofStagedTranslation
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Htr : H.StagedIotaRuleTranslation trEnv Us Δ semanticEnv decl block
      owner ctor rule) :
    Nonempty (decl.IotaRule semanticEnv block owner ctor rule) := by
  let Hselection' := Htr.selection.map
    (fun arg => arg.abstractList H.binders)
  rcases Hselection'.exists_materialization Htr.args with
    ⟨fields, Hfields⟩
  let Hfield := Hfields.iotaFieldCertificate Hselection'
    Htr.equation.field_args Htr.args H.abstractedRecursiveArgsUnique
  have Hrhs := H.iotaRhsCertificateFor
    Htr.equation.domains_length Htr.equation.rhs_residual
    Htr.equation.field_args Htr.args Htr.fields_recursor_free
    Htr.recursive_results
  rcases Hrhs with ⟨Hrhs⟩
  exact ⟨VInductDecl.IotaRule.ofCertificates
    Htr.equation.shape Hfield Hrhs⟩

/-- Equation reconstruction and semantic field selection determine every
stage-correct field of the local payload except the guarded interpretation of
the generated recursive-result list. -/
theorem BoundGeneratedRecursorRule.stagedIotaRuleTranslationOfResults
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hequation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule)
    (Hselection : RecursorFieldSelections semanticEnv decl H.allArgs
      H.recursiveArgs selections)
    (Hresults : ∀ recursiveArgs,
      List.Forall₂
        (TrExprS trEnv Us
          (abstractForallContext Hequation.shape.domains Δ))
        (H.recursiveArgs.map fun arg =>
          arg.abstractList H.binders).toList recursiveArgs →
      ∀ translatedResults,
        List.Forall₂
          (TrExprS trEnv Us
            (abstractForallContext Hequation.shape.domains Δ))
          (H.recursiveResults.map fun result =>
            result.abstractList H.binders).toList translatedResults →
        IotaRecursiveResultsCertificate (block.recursors.map (·.name))
          (recursiveArgs.filterMap VExpr.bvarHead?) recursiveArgs
          translatedResults) :
    Nonempty (H.StagedIotaRuleTranslation trEnv Us Δ semanticEnv decl
      block owner ctor rule) := by
  let Hselection' := Hselection.map
    (fun arg => arg.abstractList H.binders)
  rcases Hselection'.translations_of_all Hequation.field_args with
    ⟨recursiveArgs, Hargs⟩
  exact ⟨{
    equation := Hequation
    selections := selections
    selection := Hselection
    recursiveArgs := recursiveArgs
    args := Hargs
    fields_recursor_free := H.abstractedAllArgsNoConsts
      Hequation.field_args Hequation.domains_length
    recursive_results := Hresults recursiveArgs Hargs }⟩

/-- Equation reconstruction and the executable field-selection trace already
determine the translated recursive-argument list.  This is the minimal local
producer boundary for one generated iota rule: callers no longer choose an
additional list or prove a second pointwise translation relation. -/
theorem BoundGeneratedRecursorRule.iotaRuleTranslation_ofEquationSelection
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hequation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule)
    (Hselection : RecursorFieldSelections semanticEnv decl H.allArgs
      H.recursiveArgs selections)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name))
      (abstractForallContext Hequation.shape.domains Δ)) :
    Nonempty (H.IotaRuleTranslation trEnv Us Δ semanticEnv decl block owner
      ctor rule) := by
  let Hselection' := Hselection.map
    (fun arg => arg.abstractList H.binders)
  rcases Hselection'.translations_of_all Hequation.field_args with
    ⟨recursiveArgs, Hargs⟩
  exact ⟨{
    equation := Hequation
    selections := selections
    selection := Hselection
    recursiveArgs := recursiveArgs
    args := Hargs
    context_free := hctx }⟩

/-- Base-context freshness is the only context premise needed by the local
producer: the generated rule telescope contributes bound variables, so
`abstractForallContext` preserves the no-recursor-constants invariant. -/
theorem BoundGeneratedRecursorRule.iotaRuleTranslation_ofEquationSelectionBase
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hequation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule)
    (Hselection : RecursorFieldSelections semanticEnv decl H.allArgs
      H.recursiveArgs selections)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name)) Δ) :
    Nonempty (H.IotaRuleTranslation trEnv Us Δ semanticEnv decl block owner
      ctor rule) :=
  H.iotaRuleTranslation_ofEquationSelection Hequation Hselection
    (VLCtx.NoIndConsts.abstractForallContext hctx)

/-- Pointwise semantic state retained from the actual `mkRecRules` field and
recursive-call loops.  The concrete arrays and generated results are fixed by
`H`; this record stores only the independently checked classification and
recursive-domain evidence that the operational `RecursorRule` omits. -/
structure BoundGeneratedRecursorRule.Semantics
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF semanticRoot recLparams) (decl : VInductDecl)
    (expectedOwnerIdx : Nat) where
  depth : Nat
  context : RecursorContextWF H.root recLparams
  fieldRoot : AddInductive.Context
  fieldRootContext : RecursorContextWF fieldRoot recLparams
  fieldRootExtension : RecursorContextExtension Rroot fieldRootContext
  fieldRoot_vlctx : fieldRootContext.mlctx.vlctx = Rroot.mlctx.vlctx
  fieldsRecent : RecursorRecentBoundFVarArray fieldRootContext context
    H.allArgs
  parameterTail : Expr
  parameterPrefix : RecursorParamPrefix stats 0 sourceCtor.type parameterTail
  parameterTail_fvars :
    parameterTail.FVarsIn (· ∈ ExprArrayFVarIds stats.params)
  parameterTarget : VExpr
  parameterTranslation : TrExprS fieldRootContext.venv recLparams
    fieldRootContext.mlctx.vlctx parameterTail parameterTarget
  parameterType : fieldRootContext.venv.IsType recLparams.length
    fieldRootContext.mlctx.vlctx.toCtx parameterTarget
  fieldOpening : ConstructorFieldOpening parameterTail H.target H.allArgs
  fieldParameterUp : IsFVarUpSet (fun fv =>
    fv ∈ fieldsRecent.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params) context.mlctx.vlctx
  context_venv : context.venv = Rroot.venv
  validStats : RecursorValidAppStatsWF context.venv recLparams
    context.mlctx.vlctx stats decl depth
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  expected_owner_lt : expectedOwnerIdx < decl.types.length
  expected_target_valid : AddInductive.isValidIndAppIdx stats H.target
    expectedOwnerIdx = true
  targetTarget : VExpr
  target_not_forall : H.target.isForall = false
  target_translation : TrExprS context.venv recLparams context.mlctx.vlctx
    H.target targetTarget
  target_type : context.venv.IsType recLparams.length
    context.mlctx.vlctx.toCtx targetTarget
  fieldTargetDefEq : fieldRootContext.venv.IsDefEqU recLparams.length
    fieldRootContext.mlctx.vlctx.toCtx parameterTarget
      (context.mlctx.mkForall' H.allArgs.size fieldsRecent.size_le
        targetTarget)
  constructorTarget : VExpr
  constructor_translation : TrExprS context.venv recLparams
    context.mlctx.vlctx H.sourceConstructorMajor constructorTarget
  constructor_typing : context.venv.HasType recLparams.length
    context.mlctx.vlctx.toCtx constructorTarget targetTarget
  target_valid : AddInductive.isValidIndApp? stats H.target = some ownerIdx
  validated : RecursorValidatedIndAppAt context.venv recLparams
    context.mlctx.vlctx stats decl depth H.target targetTarget ownerIdx
  fields : List
    (RecursorRecursiveDomainAt context.venv decl recLparams.length)
  selection : RecursorFieldSelectionsAt context.venv decl recLparams.length
    H.allArgs H.recursiveArgs fields
  decisionPositions : List Nat
  decisions : RecursorFieldDecisions stats fieldRoot parameterTail H.root
    H.target H.allArgs H.recursiveArgs decisionPositions
  calls : SemanticBoundGeneratedRecursiveCalls indTypes stats motives minors
    lvls context decl depth
    (fun fv => fv ∈ fieldOpening.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params)
    H.recursiveArgs H.recursiveResults
    H.recursiveArgs.size

/-- Alpha-independent mask selected by the rule-generation field traversal. -/
def BoundGeneratedRecursorRule.Semantics.recursivePositions
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) : List Nat :=
  S.decisionPositions

theorem BoundGeneratedRecursorRule.Semantics.recursivePositions_ordered
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    S.recursivePositions.Pairwise (· < ·) := by
  exact S.decisions.positions_ordered

theorem BoundGeneratedRecursorRule.Semantics.recursivePositions_lt
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    ∀ position ∈ S.recursivePositions, position < H.allArgs.size := by
  exact S.decisions.positions_lt

@[simp] theorem
    BoundGeneratedRecursorRule.Semantics.recursivePositions_length
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    S.recursivePositions.length = H.recursiveArgs.size := by
  exact S.decisions.positions_length

/-- Once the two alpha-independent masks agree, their executable recursive
arrays have the same cardinality.  This isolates the sole cross-pass fact
needed by recursive minor application from either pass's fresh identifiers. -/
theorem RecInfoMinorTraversalShape.recursiveFields_size_eq_rule
    {stats : AddInductive.InductiveStats}
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (T : RecInfoMinorTraversalShape)
    (S : H.Semantics Rroot decl expectedOwnerIdx)
    (hpositions : T.recursivePositions = S.recursivePositions) :
    T.recursiveFields.size = H.recursiveArgs.size := by
  rw [← T.recursivePositions_length, hpositions,
    S.recursivePositions_length]

/-- The generated minor introduces exactly one hypothesis per rule recursive
result as soon as its retained traversal mask is aligned with the rule mask. -/
theorem RecInfoMinorTypeShape.hypotheses_size_eq_rule
    {stats : AddInductive.InductiveStats}
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (M : RecInfoMinorTypeShape) (T : RecInfoMinorTraversalShape)
    (S : H.Semantics Rroot decl expectedOwnerIdx)
    (hrecursive : T.recursiveFields = M.recursiveFields)
    (hpositions : T.recursivePositions = S.recursivePositions) :
    M.hypotheses.size = H.recursiveArgs.size := by
  rw [M.hypotheses_size, ← hrecursive]
  exact T.recursiveFields_size_eq_rule S hpositions

/-- The exact constructor-field suffix, closed back into the semantic context
that preceded `loopCtorArgs`.  Both sides are deliberately retained: the
forall telescope types the constructor target, while the lambda telescope
types the constructor application used as the iota major premise. -/
structure BoundGeneratedRecursorRule.Semantics.FieldTelescope
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) where
  domains : List VExpr
  domains_length : domains.length = H.allArgs.size
  target_translation : TrExprS S.fieldRootContext.venv recLparams
    S.fieldRootContext.mlctx.vlctx
    (H.root.lctx.mkForall H.allArgs H.target)
    (VExpr.wrapForalls domains S.targetTarget)
  target_type : S.fieldRootContext.venv.IsType recLparams.length
    S.fieldRootContext.mlctx.vlctx.toCtx
    (VExpr.wrapForalls domains S.targetTarget)
  major_translation : TrExprS S.fieldRootContext.venv recLparams
    S.fieldRootContext.mlctx.vlctx
    (H.root.lctx.mkLambda H.allArgs H.sourceConstructorMajor)
    (VExpr.wrapLams domains S.constructorTarget)
  major_typing : S.fieldRootContext.venv.HasType recLparams.length
    S.fieldRootContext.mlctx.vlctx.toCtx
    (VExpr.wrapLams domains S.constructorTarget)
    (VExpr.wrapForalls domains S.targetTarget)

/-- The terminal constructor target mentions only the exact fields opened by
the constructor traversal and the cached inductive parameters. -/
theorem BoundGeneratedRecursorRule.Semantics.targetFVarsIn
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    H.target.FVarsIn (fun fv =>
      fv ∈ S.fieldsRecent.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params) := by
  have hscope := S.fieldOpening.currentFVarsIn S.parameterTail_fvars
  rw [S.fieldOpening.fvars_eq_bound
    S.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray] at hscope
  exact hscope

/-- Recover the typed field telescope directly from the consecutive-suffix
certificate retained by the production constructor traversal. -/
def BoundGeneratedRecursorRule.Semantics.fieldTelescope
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    S.FieldTelescope := by
  let domains := MLCtxForallDomains S.context.mlctx H.allArgs.size
    S.fieldsRecent.size_le
  have Htarget := S.fieldsRecent.mkForallExact S.target_translation
    S.target_type
  have Hmajor := S.fieldsRecent.mkLambda S.constructor_translation
    S.constructor_typing
  exact {
    domains := domains
    domains_length := by
      exact S.context.onlyLams.forallDomains_length H.allArgs.size
        S.fieldsRecent.size_le
    target_translation := by simpa [domains] using Htarget.1
    target_type := by simpa [domains] using Htarget.2
    major_translation := by simpa [domains] using Hmajor.1
    major_typing := by simpa [domains] using Hmajor.2 }

/-- Translating the original constructor telescope and replaying the
consumed field declarations may choose different representatives for binder
domains.  Their dependent contexts nevertheless agree definitionally, as
forced by the retained reconstruction of the whole constructor target. -/
theorem BoundGeneratedRecursorRule.Semantics.fieldContextDefEq
    {H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule}
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF semanticRoot recLparams}
    (S : H.Semantics Rroot decl expectedOwnerIdx) :
    ∃ sourceDomains sourceResidual,
      sourceDomains.length = H.allArgs.size ∧
      S.parameterTarget =
        VExpr.wrapForalls sourceDomains sourceResidual ∧
      VEnv.IsDefEqCtx S.fieldRootContext.venv recLparams.length []
        (sourceDomains.reverse ++
          S.fieldRootContext.mlctx.vlctx.toCtx)
        (S.fieldTelescope.domains.reverse ++
          S.fieldRootContext.mlctx.vlctx.toCtx) := by
  rcases TrExprS.forallTelescope_shape S.fieldOpening.telescope
      S.parameterTranslation with
    ⟨sourceDomains, sourceResidual, hsourceLength, hparameterTarget⟩
  let F := S.fieldTelescope
  have Htarget : S.fieldRootContext.venv.IsDefEqU recLparams.length
      S.fieldRootContext.mlctx.vlctx.toCtx
      (VExpr.wrapForalls sourceDomains sourceResidual)
      (VExpr.wrapForalls F.domains S.targetTarget) := by
    rw [← hparameterTarget]
    simpa [F, BoundGeneratedRecursorRule.Semantics.fieldTelescope,
      TypeChecker.MLCtx.mkForall'_eq_wrapForalls] using
        S.fieldTargetDefEq
  have Hbase : VEnv.IsDefEqCtx S.fieldRootContext.venv
      recLparams.length [] S.fieldRootContext.mlctx.vlctx.toCtx
      S.fieldRootContext.mlctx.vlctx.toCtx :=
    .refl S.fieldRootContext.mlctx_wf.tr.wf.toCtx
  exact ⟨sourceDomains, sourceResidual, hsourceLength, hparameterTarget,
    VEnv.IsDefEqU.wrapForalls_context S.fieldRootContext.checking.tr.wf
      Hbase (hsourceLength.trans F.domains_length.symm) Htarget⟩

/-- Duplicate-free declaration names identify the first family selected by
`isValidIndApp?` with the constructor owner certified by the earlier checker
pass.  This is the explicit bridge between the scan used by rule generation
and the outer mutual-family traversal. -/
theorem BoundGeneratedRecursorRule.Semantics.owner_eq
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hsemantic : H.Semantics Rroot decl expectedOwnerIdx)
    (hnames : (decl.types.map (·.name)).Nodup) :
    Hsemantic.ownerIdx = expectedOwnerIdx := by
  have hselectedValid : AddInductive.isValidIndAppIdx stats H.target
      Hsemantic.ownerIdx = true :=
    (checkPositivityStep.isValidIndApp?_some Hsemantic.target_valid).2
  have hselectedHead : H.target.getAppFn =
      .const (decl.types[Hsemantic.ownerIdx]'Hsemantic.owner_lt).name
        stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead hselectedValid
      (Hsemantic.validStats.indConstAt Hsemantic.owner_lt)
  have hexpectedHead : H.target.getAppFn =
      .const
        (decl.types[expectedOwnerIdx]'Hsemantic.expected_owner_lt).name
        stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead
      Hsemantic.expected_target_valid
      (Hsemantic.validStats.indConstAt Hsemantic.expected_owner_lt)
  have hname :
      (decl.types[Hsemantic.ownerIdx]'Hsemantic.owner_lt).name =
      (decl.types[expectedOwnerIdx]'Hsemantic.expected_owner_lt).name := by
    have heq := hselectedHead.symm.trans hexpectedHead
    injection heq
  have hleft : Hsemantic.ownerIdx < (decl.types.map (·.name)).length := by
    simpa using Hsemantic.owner_lt
  have hright : expectedOwnerIdx <
      (decl.types.map (·.name)).length := by
    simpa using Hsemantic.expected_owner_lt
  apply (List.getElem_inj (h₀ := hleft) (h₁ := hright) hnames).mp
  simpa only [List.getElem_map] using hname

/-- The semantic refinement of the actual recursive-call loop and the
classifier trace together produce the source-level field selection consumed
by an iota translation.  Thus, once the concrete equation has been closed,
no recursive-field premise remains at the generated-rule boundary. -/
theorem BoundGeneratedRecursorRule.iotaRuleTranslation_ofSemanticCalls
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    {root : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF root recLparams}
    (Hcalls : SemanticBoundGeneratedRecursiveCalls indTypes stats motives
      minors lvls R decl depth P H.recursiveArgs H.recursiveResults
      H.recursiveArgs.size)
    {fields : List
      (RecursorRecursiveDomainAt R.venv decl recLparams.length)}
    (Hselection : RecursorFieldSelectionsAt R.venv decl recLparams.length
      H.allArgs H.recursiveArgs fields)
    (Hequation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name)) Δ) :
    Nonempty (H.IotaRuleTranslation trEnv Us Δ R.venv decl block owner ctor
      rule) := by
  rcases Hcalls.sourceSelection Hselection with
    ⟨selections, HsourceSelection⟩
  exact H.iotaRuleTranslation_ofEquationSelectionBase Hequation
    HsourceSelection hctx

theorem BoundGeneratedRecursorRule.iotaRuleTranslation_ofSemantics
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hsemantic : H.Semantics Rroot decl expectedOwnerIdx)
    (Hequation : H.IotaEquationTranslationCertificate trEnv Us Δ decl block
      owner ctor rule)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name)) Δ) :
    Nonempty (H.IotaRuleTranslation trEnv Us Δ Rroot.venv decl block owner
      ctor rule) := by
  rw [← Hsemantic.context_venv]
  exact H.iotaRuleTranslation_ofSemanticCalls Hsemantic.calls
    Hsemantic.selection Hequation hctx

/-- Stage-correct producer for the complete local iota payload.  Unlike the
legacy translation record, this theorem permits equation translation after
recursor installation and derives guarded recursive results from the
retained pre-installation semantic calls. -/
theorem BoundGeneratedRecursorRule.stagedIotaRuleTranslation_ofSemantics
    (H : BoundGeneratedRecursorRule indTypes stats motives minors lvls
      sourceCtor minorIdx sourceRule)
    (Hsemantic : H.Semantics Rroot decl expectedOwnerIdx)
    (Hequation : H.IotaEquationTranslationCertificate trEnv Us Delta decl
      block owner ctor rule)
    (hfresh : ∀ name ∈ block.recursors.map (·.name),
      Rroot.venv.constants name = none)
    (hctx : VLCtx.NoIndConsts (block.recursors.map (·.name)) Delta)
    (hproj : ∀ {Delta : VLCtx} {s i e' e''},
      TrProj Delta.toCtx s i e' e'' →
      e'.containsAnyConst (block.recursors.map (·.name)) = false →
      e''.containsAnyConst (block.recursors.map (·.name)) = false)
    (hrecursor : Hsemantic.calls.bound.RecursorsPresent
      (block.recursors.map (·.name))) :
    Nonempty (H.StagedIotaRuleTranslation trEnv Us Delta
      Rroot.venv decl block owner ctor rule) := by
  rw [← Hsemantic.context_venv] at hfresh ⊢
  rcases Hsemantic.calls.sourceSelection Hsemantic.selection with
    ⟨selections, HsourceSelection⟩
  apply H.stagedIotaRuleTranslationOfResults Hequation HsourceSelection
  intro recursiveArgs Hargs translatedResults Hresults
  apply Hsemantic.calls.abstractedIotaResults H.recursive_args_bound
    Hargs Hresults hfresh
    (VLCtx.NoIndConsts.abstractForallContext hctx) hproj hrecursor
  · intro arg harg
    exact H.params_bound.avoidsConsts arg harg
  · intro arg harg
    exact H.motives_bound.avoidsConsts arg harg
  · intro arg harg
    exact H.minors_bound.avoidsConsts arg harg
  · exact H.binders_nodup
  · exact Hequation.domains_length
  · intro fv hfv
    have hall : fv ∈ H.all_args_bound.fvars :=
      H.recursive_args_bound.fvars_subset_of_sublist H.all_args_bound
        H.recursive_args_sublist hfv
    unfold BoundGeneratedRecursorRule.binders
    exact List.mem_append_right _ hall

/-- Ordered binder-aware coverage of a constructor suffix. -/
inductive BoundGeneratedRecursorRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) :
    List Constructor → Nat → List RecursorRule → Prop
  | nil : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      [] start []
  | cons :
      Nonempty (BoundGeneratedRecursorRule indTypes stats motives minors
        lvls ctor start rule) →
      BoundGeneratedRecursorRules indTypes stats motives minors lvls
        ctors (start + 1) rules →
      BoundGeneratedRecursorRules indTypes stats motives minors lvls
        (ctor :: ctors) start (rule :: rules)

/-- Semantic strengthening of `BoundGeneratedRecursorRules`.  Each emitted
source rule is paired with the exact classifier and recursive-call evidence
from the same executable iteration; the tail advances the flattened minor
ordinal in lockstep. -/
inductive SemanticBoundGeneratedRecursorRules
    (indTypes : Array InductiveType) (stats : AddInductive.InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    {semanticRoot : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF semanticRoot recLparams) (decl : VInductDecl)
    (ownerIdx : Nat) :
    List Constructor → Nat → List RecursorRule → Prop
  | nil : SemanticBoundGeneratedRecursorRules indTypes stats motives minors
      lvls Rroot decl ownerIdx [] start []
  | cons
      (Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
        ctor start rule)
      (Hsemantic : Nonempty
        (Hrule.Semantics Rroot decl ownerIdx))
      (Htail : SemanticBoundGeneratedRecursorRules indTypes stats motives
        minors lvls Rroot decl ownerIdx ctors (start + 1)
          rules) :
      SemanticBoundGeneratedRecursorRules indTypes stats motives minors lvls
        Rroot decl ownerIdx (ctor :: ctors) start
          (rule :: rules)

theorem SemanticBoundGeneratedRecursorRules.bound
    (H : SemanticBoundGeneratedRecursorRules indTypes stats motives minors
      lvls Rroot decl ownerIdx ctors start rules) :
    BoundGeneratedRecursorRules indTypes stats motives minors lvls ctors
      start rules := by
  induction H with
  | nil => exact .nil
  | cons Hrule _ _ ih => exact .cons ⟨Hrule⟩ ih

theorem SemanticBoundGeneratedRecursorRules.length
    (H : SemanticBoundGeneratedRecursorRules indTypes stats motives minors
      lvls Rroot decl ownerIdx ctors start rules) :
    rules.length = ctors.length := by
  induction H with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

theorem SemanticBoundGeneratedRecursorRules.entry
    (H : SemanticBoundGeneratedRecursorRules indTypes stats motives minors
      lvls Rroot decl ownerIdx ctors start rules) :
    ∀ i (hctor : i < ctors.length) (hrule : i < rules.length),
      ∃ Hrule : BoundGeneratedRecursorRule indTypes stats motives minors lvls
          ctors[i] (start + i) rules[i],
        Nonempty (Hrule.Semantics Rroot decl ownerIdx) := by
  induction H with
  | nil =>
      intro i hctor
      simp at hctor
  | @cons ctor start rule ctors rules Hrule Hsemantic Htail ih =>
      intro i hctor hrule
      cases i with
      | zero => exact ⟨Hrule, Hsemantic⟩
      | succ i =>
        have h := ih i (by simpa using hctor) (by simpa using hrule)
        have hindex : start + 1 + i = start + (i + 1) := by omega
        rw [hindex] at h
        exact h

theorem BoundGeneratedRecursorRules.length
    (H : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules) : rules.length = ctors.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem BoundGeneratedRecursorRules.entry
    (H : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules) :
    ∀ i (hctor : i < ctors.length) (hrule : i < rules.length),
      Nonempty (BoundGeneratedRecursorRule indTypes stats motives minors
        lvls ctors[i] (start + i) rules[i]) := by
  induction H with
  | nil =>
      intro i hctor
      simp at hctor
  | @cons ctor start rule ctors rules Hrule Htail ih =>
      intro i hctor hrule
      cases i with
      | zero => simpa using Hrule
      | succ i =>
        have h := ih i (by simpa using hctor) (by simpa using hrule)
        simpa only [List.getElem_cons_succ, Nat.add_assoc,
          Nat.add_comm 1 i] using h


end VerifyInductive
end Lean4Lean
