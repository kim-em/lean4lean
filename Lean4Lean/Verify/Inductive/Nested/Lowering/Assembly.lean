import Lean4Lean.Verify.Inductive.Nested.Lowering.Ordinary
import Lean4Lean.Verify.Inductive.Nested.Lowering.Counts

/-! # The fields of `NestedLoweringOutput`

Each field of the lowering interface (`Verify/Inductive/Lowering.lean`), proved from the run
relation `NestedLoweringOutputClosed` that `ElimNestedInductive.run'.translationClosed` gives for
a successful run from the executable's initial state. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The executable's initial lowering state. -/
abbrev loweringInitialState (lparams : List Name) (types : List InductiveType) :
    ElimNestedInductive.State :=
  { lvls := lparams.map .param, newTypes := types.toArray }

/-- A successful lowering run from the executable's initial state is a closed lowering. -/
theorem loweringRun.closedOfRun {env : Environment} {ves : VEnvs} {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} {res : ElimNestedInductive.Result}
    (wf : ves.WF env) (hsources : checkInductiveSources env types = .ok ())
    (h : (ElimNestedInductive.run fuel nparams types env).run'
      (loweringInitialState lparams types) = .ok res) :
    NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types) res :=
  ElimNestedInductive.run'.translationClosed fuel nparams types env _ wf.inductivesClosed
    (VEnvs.WF.environmentTypesClosed wf) (checkInductiveSources_refines env types _ hsources) rfl rfl _ h

section
variable {env : Environment} {fuel nparams : Nat} {types : List InductiveType}
  {lparams : List Name} {res : ElimNestedInductive.Result}

theorem NestedLoweringOutputClosed.nparams_eq
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) : res.nparams = nparams := by
  obtain ⟨_, Hrun, -, -⟩ := H
  exact Hrun.resultNParams

theorem NestedLoweringOutputClosed.params_size
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) : res.params.size = nparams := by
  obtain ⟨_, Hrun, -, -⟩ := H
  exact Hrun.resultParamsSize

theorem NestedLoweringOutputClosed.source_nonempty
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) : types ≠ [] := by
  obtain ⟨_, Hrun, -, -⟩ := H
  obtain ⟨first, rest, -, -, -, -, htypes, -⟩ := Hrun.source
  rw [htypes]; simp

theorem NestedLoweringOutputClosed.lctx_params
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) :
    res.params.toList.reverse.map (·.fvarId!) = res.lctx.fvars ∧
      ∀ p ∈ res.params.toList, p.isFVar := by
  obtain ⟨_, Hrun, -, fvars, hparams, -⟩ := H
  have hrev := Hrun.resultParams_reverse_fvars
  refine ⟨?_, ?_⟩
  · rw [hrev, List.map_map]
    exact List.map_id'' (fun _ => rfl) _
  · intro p hp
    rw [hparams] at hp
    simp at hp
    obtain ⟨fv, -, rfl⟩ := hp
    rfl

theorem NestedLoweringOutputClosed.params_opening
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) :
    ∃ first rest tail, types = first :: rest ∧
      LoweringParamOpening {} #[] first.type nparams res.lctx tail res.params ∧
      res.lctx.WF ∧ (∀ fv ∈ res.lctx.fvars, ({} : TypeChecker.State).ngen.Reserves fv) ∧
      ∃ fvars : List FVarId, res.params = (fvars.map Expr.fvar).toArray ∧ fvars.Nodup := by
  obtain ⟨_, Hrun, -, Hnodup⟩ := H
  have hfresh := Hrun.resultContextKernelFresh rfl
  have hwf := Hrun.resultContextWF
  obtain ⟨first, rest, tail, paramsState, lctx, params, htypes, Hopening, -, -, -, -, -, -,
    Hqueue⟩ := Hrun.source
  obtain ⟨hlctx, hparams⟩ := Hqueue.resultContext
  refine ⟨first, rest, tail, htypes, ?_, hwf, hfresh, Hnodup⟩
  rw [hlctx, hparams]
  exact Hopening

theorem NestedLoweringOutputClosed.types_length
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) : res.types.length = types.length + res.aux2nested.size := by
  obtain ⟨finalState, Hrun, -, -⟩ := H
  have hnodup := Hrun.resultNamesNodupOfEmpty (by rfl)
  obtain ⟨first, rest, tail, paramsState, lctx, params, htypes, Hopening, hnewTypes, hnestedAux,
    -, -, -, -, Hqueue⟩ := Hrun.source
  have Hbal : SizeBalanced types.length finalState := by
    apply Hqueue.sizeBalanced
    unfold SizeBalanced
    rw [hnewTypes, hnestedAux]
    show types.toArray.size = types.length + (#[] : Array (Expr × Name)).size
    simp
  have hmap := Hrun.resultAuxMap
  have hsize : res.aux2nested.size = finalState.nestedAux.size := by
    rw [hmap]
    change (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp) (entry : Expr × Name) =>
        map.insert entry.2 entry.1) {}).size = _
    rw [← Array.foldl_toList, nestedAuxFold_size _ _ hnodup (by simp)]
    simp
  rw [hsize, Hqueue.resultTypes]
  simpa [SizeBalanced] using Hbal

theorem NestedLoweringOutputClosed.ordinary
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res)
    (hsources : checkInductiveSources env types = .ok ()) (hclosed : SourceBVarClosed types)
    (haux : res.aux2nested.size = 0) : res.types = types :=
  NestedLoweringRun.types_eq_source_of_aux2nested_size_eq_zero
    (initialState := loweringInitialState lparams types) H.toResult
    (checkInductiveSources_refines env types _ hsources) hclosed rfl haux

end

theorem ConstructorLowerings.Resolved.forall₂
    (H : ConstructorLowerings.Resolved env params nparams finalResult sources state out) :
    List.Forall₂ (fun target source => ∃ before after,
      ConstructorLowering.Resolved env params nparams finalResult source before (target, after))
      out.1 sources := by
  induction H with
  | nil => exact .nil
  | cons Hhead _ ih => exact .cons ⟨_, _, Hhead⟩ ih

theorem ConstructorLowerings.Resolved.names
    (H : ConstructorLowerings.Resolved env params nparams finalResult sources state out) :
    out.1.map (·.name) = sources.map (·.name) := by
  induction H with
  | nil => rfl
  | cons Hhead _ ih => simp only [List.map_cons, ih, Hhead.name]

theorem forall₂_imp_mem {R S : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b →
      (∀ x ∈ a, ∀ y ∈ b, R x y → S x y) → List.Forall₂ S a b
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, H =>
    .cons (H _ (by simp) _ (by simp) h)
      (forall₂_imp_mem t fun x hx y hy => H x (by simp [hx]) y (by simp [hy]))

/-- A positional relation on the first `types.length` families of a list that extends it. -/
theorem forall₂_take_of_getElem? {R : InductiveType → InductiveType → Prop}
    {lowered types : List InductiveType} (hlen : types.length ≤ lowered.length)
    (H : ∀ j (hj : j < types.length), ∃ target, lowered[j]? = some target ∧ R target types[j]) :
    List.Forall₂ R (lowered.take types.length) types := by
  refine List.forall₂_of_getElem (by simp [hlen]) fun j hj hj' => ?_
  obtain ⟨target, htarget, hR⟩ := H j hj'
  have : (lowered.take types.length)[j] = target := by
    rw [List.getElem_take]
    exact (List.getElem?_eq_some_iff.mp htarget).2
  rw [this]
  exact hR

section
variable {env : Environment} {fuel nparams : Nat} {types : List InductiveType}
  {lparams : List Name} {res : ElimNestedInductive.Result}

/-- The lowering of the `j`-th source family, against the final result. -/
theorem NestedLoweringOutputClosed.sourceMapping
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) (hj : j < types.length) :
    ∃ fvars : List FVarId, ∃ stepState target loweredState,
      res.params = (fvars.map Expr.fvar).toArray ∧ fvars.Nodup ∧ res.params.size = nparams ∧
      FamilyLowering.Resolved env res.params nparams res types[j] stepState
        (target, loweredState) ∧
      res.types[j]? = some target :=
  NestedLoweringOutputClosed.sourceResolvedMappingAtFreshAligned
    (initialState := loweringInitialState lparams types) H (by rfl) hj

theorem NestedLoweringOutputClosed.source_headers
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res) :
    List.Forall₂ (fun lowered source => lowered.name = source.name ∧
        lowered.type = source.type ∧ lowered.ctors.map (·.name) = source.ctors.map (·.name))
      (res.types.take types.length) types := by
  refine forall₂_take_of_getElem? ?_ fun j hj => ?_
  · rw [H.types_length]; exact Nat.le_add_right _ _
  obtain ⟨_, _, target, _, -, -, -, Hfam, htarget⟩ := H.sourceMapping hj
  exact ⟨target, htarget, Hfam.name, Hfam.type, Hfam.constructors.names⟩

theorem NestedLoweringOutputClosed.restore_source
    (H : NestedLoweringOutputClosed env fuel nparams types (loweringInitialState lparams types)
      res)
    (hsources : checkInductiveSources env types = .ok ()) (hclosed : SourceBVarClosed types)
    (loweredEnv : Environment) :
    List.Forall₂ (fun lowered source => List.Forall₂
        (fun (lc sc : Constructor) => RestoreSourceDisjoint res loweredEnv sc.type →
          (res.restoreNested loweredEnv lc.type == sc.type) = true)
        lowered.ctors source.ctors)
      (res.types.take types.length) types := by
  have Hchecked := checkInductiveSources_refines env types _ hsources
  have Hrestorable : ∀ type ∈ res.types, RestorableInductiveType nparams type := by
    obtain ⟨_, Hrun, -, -⟩ := H
    exact Hrun.resultRestorable
  refine forall₂_take_of_getElem? ?_ fun j hj => ?_
  · rw [H.types_length]; exact Nat.le_add_right _ _
  obtain ⟨fvars, _, target, _, hparams, hnodup, hsize, Hfam, htarget⟩ := H.sourceMapping hj
  refine ⟨target, htarget, ?_⟩
  have hmem : types[j] ∈ types := List.getElem_mem hj
  have htargetMem : target ∈ res.types := List.mem_of_getElem? htarget
  refine forall₂_imp_mem Hfam.constructors.forall₂ fun lc hlcMem sc hscMem hpair hdisjoint => ?_
  obtain ⟨before, after, Hctor⟩ := hpair
  have Htelescope : RestoreTelescope lc.type res.nparams := by
    rw [H.nparams_eq]
    exact Hrestorable target htargetMem lc hlcMem
  obtain ⟨Hinverse⟩ := Hctor.nestedRestoration_inverse rfl fvars hparams hnodup
    ((Hchecked.constructorsClosed hmem) sc hscMem) ((hclosed _ hmem).2 sc hscMem) hsize
    loweredEnv hdisjoint H.nparams_eq
    (restoreNested_refines res loweredEnv {} lc.type Htelescope)
  exact Hinverse.restoredType_eqv_source

end

end VerifyInductive
end Lean4Lean
