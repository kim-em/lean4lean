import Lean4Lean.Theory.Typing.CaseSourceSort
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Verify.Inductive.Recursor.CanonicalMotiveGroup
import Lean4Lean.Verify.Inductive.CompletedSourceSignature

/-! Well-formed family applications (`InductiveSignature.FamilyTypesWF`) for
the two signatures the checker produces: the header-phase source signature and
the signature over the families consumed by the recursor pass.

Neither proof compares a signature's index telescope definitionally with the
declared family type in the telescope's own prefix.  The source signature
reads its telescope off the header phase's definitional equality; the
consumed families read theirs off the recursor pass's index replay and
generated motive, and recover the result sort from the declared constant. -/

namespace Lean4Lean

theorem InductiveSignature.vars_append_eq_bvarRange (a b : Nat) :
    vars a b ++ vars b 0 = VExpr.bvarRange (a + b) (a + b) := by
  apply List.ext_getElem
  · simp [vars]
  · intro j h1 h2
    simp only [List.length_append, vars, List.length_map, List.length_reverse,
      List.length_range] at h1
    rw [VExpr.bvarRange_getElem _ _ _ (by omega)]
    by_cases hj : j < a
    · rw [List.getElem_append_left (by simp [vars]; omega)]
      simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
        List.length_range, VExpr.bvar.injEq]
      omega
    · rw [List.getElem_append_right (by simp [vars]; omega)]
      simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
        List.length_range, List.length_map, List.length_reverse, VExpr.bvar.injEq]
      omega

namespace VEnv

/-- A closed term typed at a telescope, applied to the telescope's own
variables in the telescope's context, has the telescope's body type. -/
theorem HasType.mkApps_bvarRange {env : VEnv} {U : Nat} (henv : env.WF)
    {f B : VExpr} {doms : List VExpr}
    (hf : env.HasType U [] f (VExpr.wrapForalls doms B))
    (hctx : OnCtx doms.reverse (env.IsType U))
    (hB : B.ClosedN doms.length) :
    env.HasType U doms.reverse
      (VExpr.mkApps f (VExpr.bvarRange doms.length doms.length)) B := by
  have hf' : env.HasType U doms.reverse f (VExpr.wrapForalls doms B) :=
    hf.weak0 henv.ordered
  have h := HasType.mkApps_of_telescope henv hctx
    (args := VExpr.bvarRange doms.length doms.length) hf' (by simp) ?_
  · rwa [VExpr.instOuter_range_bvar' B _ _ hB (Nat.le_refl _), Nat.sub_self,
      VExpr.liftN_zero] at h
  · intro j hj hj'
    simp only [VExpr.bvarRange_length] at hj
    rw [VExpr.bvarRange_getElem _ _ _ hj, VExpr.bvarRange_take _ _ _ (Nat.le_of_lt hj)]
    have hclosed : doms[j].ClosedN j := by
      have := OnCtx.reverse_getElem_closedN henv (Γ := []) (by simpa using hctx) j hj'
      simpa using this
    rw [VExpr.instOuter_range_bvar' _ _ _ hclosed (by omega)]
    have hl := Lookup.reverse_append doms [] j hj'
    simp only [List.append_nil] at hl
    exact .bvar hl

end VEnv

namespace VerifyInductive
open Lean hiding Environment Exception
open Kernel

namespace CompletedConstructorPhases

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}

/-- The header-phase source signature has well-formed family applications in
the environment in which the recursors are declared.  Its family telescope is
definitionally the declared family type (`sourceSignatureHeader_families`), so
each family applied to its own telescope variables has the recorded sort. -/
theorem sourceSignature_familyTypesWF
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    R.sourceSignature.FamilyTypesWF (R.ctorVEnv.addProjections decl.projectionEntries)
      decl.uvars := by
  intro owner
  have henv := R.projectedWF
  have hctorsLE : R.headerVEnv ≤ R.ctorVEnv.addProjections decl.projectionEntries :=
    (VEnv.addConstVals_le R.core.ctorsAdded).trans VEnv.addProjections_le
  have hle : sourceEnv ≤ R.ctorVEnv.addProjections decl.projectionEntries :=
    (VEnv.addConstVals_le R.core.typesAdded).trans hctorsLE
  have hheader : owner.val < R.sourceSignatureHeader.families.size := owner.isLt
  have hdecl : owner.val < decl.types.length := by
    have := Lean4Lean.List.Forall₂.length_eq R.sourceSignatureHeader_families
    simp only [Array.length_toList] at this
    omega
  have hfam := Lean4Lean.List.forall₂_getElem R.sourceSignatureHeader_families owner.val
    (by simpa using hheader) hdecl
  simp only [Array.getElem_toList] at hfam
  obtain ⟨hname, _, _, hdefeq⟩ := hfam
  have hmem : decl.types[owner.val] ∈ decl.types := List.getElem_mem hdecl
  have hsourceWF := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core
    (List.ne_nil_of_mem hmem) (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
  have huvars : decl.types[owner.val].uvars = decl.uvars := hsourceWF.2.2.1 _ hmem
  have hlookup : (R.ctorVEnv.addProjections decl.projectionEntries).constants
      decl.types[owner.val].name = some decl.types[owner.val].toVConstant :=
    hctorsLE.constants (VEnv.addConstVals_get R.core.typesAdded
      (List.mem_map.mpr ⟨_, hmem, rfl⟩))
  have hconst := VEnv.HasType.const0 hlookup (henv.ordered.constWF hlookup)
  change (R.ctorVEnv.addProjections decl.projectionEntries).HasType
    decl.types[owner.val].uvars [] (.const decl.types[owner.val].name
      (VLevel.params decl.types[owner.val].uvars)) decl.types[owner.val].type at hconst
  rw [huvars, ← hname] at hconst
  have hW := hconst.defeqU_r henv trivial (hdefeq.symm.mono hle)
  have hWT := hW.isType henv.ordered trivial
  have hctx := (VEnv.IsType.wrapForalls_inv henv.ordered (ctx := []) trivial hWT).1
  simp only [List.append_nil] at hctx
  have happ := VEnv.HasType.mkApps_bvarRange henv hW hctx trivial
  have hctx' : OnCtx (R.sourceSignatureHeader.families[owner.val].indices.reverse ++
      R.sourceSignatureHeader.params.reverse)
      ((R.ctorVEnv.addProjections decl.projectionEntries).IsType decl.uvars) := by
    simpa [List.reverse_append] using hctx
  refine ⟨hctx', ?_⟩
  change (R.ctorVEnv.addProjections decl.projectionEntries).HasType decl.uvars
    (R.sourceSignatureHeader.families[owner.val].indices.reverse ++
      R.sourceSignatureHeader.params.reverse)
    (VExpr.mkApps (.const R.sourceSignatureHeader.families[owner.val].name
      (VLevel.params decl.uvars))
      (InductiveSignature.vars R.sourceSignatureHeader.params.length
          R.sourceSignatureHeader.families[owner.val].indices.length ++
        InductiveSignature.vars R.sourceSignatureHeader.families[owner.val].indices.length 0))
    (.sort R.sourceSignatureHeader.families[owner.val].resultLevel)
  rw [InductiveSignature.vars_append_eq_bvarRange, ← List.length_append]
  simpa [List.reverse_append] using happ

/-- The same statement in the retained checking context's environment. -/
theorem sourceSignature_familyTypesWF_context
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) :
    R.sourceSignature.FamilyTypesWF R.context.venv decl.uvars := by
  rw [R.contextVEnv]
  exact R.sourceSignature_familyTypesWF

end CompletedConstructorPhases

theorem vars_append_canonical (a b : Nat) :
    InductiveSignature.vars a b ++ InductiveSignature.vars b 0 = recursorCanonicalVars (a + b) := by
  rw [recursorCanonicalVars_add, ← vars_eq_canonical, ← vars_eq_canonical, vars_lift, Nat.add_zero]

private theorem familyTypes_ctx_levelWF {env : VEnv} {Γ : List VExpr}
    (H : OnCtx Γ (env.IsType U)) : OnCtx Γ (fun _ A => A.LevelWF U) := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih => exact ⟨ih H.1, (Classical.choose_spec H.2).levelWF (ih H.1) |>.1⟩

private theorem familyTypes_ctx_instL_id {env : VEnv} {Γ : List VExpr}
    (H : OnCtx Γ (env.IsType U)) : Γ.map (VExpr.instL (VLevel.params U)) = Γ := by
  have Hw := familyTypes_ctx_levelWF H
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
    simp only [List.map_cons, Hw.2.instL_id]
    exact congrArg (List.cons A) (ih H.1 Hw.1)

private theorem familyTypes_recursorLevels_zero
    (ha : AddInductive.AdmissibleElimLevel Us elim) (heq : elim = .zero) :
    recursorDeclarationAbstractLevels Us ha = VLevel.params Us.length := by
  subst elim
  rfl

private theorem familyTypes_recursorLevels_param
    (ha : AddInductive.AdmissibleElimLevel Us elim) (heq : elim = .param fresh) :
    recursorDeclarationAbstractLevels Us ha = VLevel.prependShift Us.length := by
  subst elim
  simp only [recursorDeclarationAbstractLevels]
  exact VLevel.inst_map_id VLevel.prependShift_length

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The consumed index telescope of each family, over the cached parameter
context, is a well-formed context.  It is read off the recursor pass's index
replay (`sourceIndexDomains`). -/
theorem CompletedRecursorConstruction.consumedIndices_onCtx
    (H : CompletedRecursorConstruction R) (owner : Fin H.recInfos.size) :
    OnCtx ((H.sourceIndices owner).reverse ++ R.parameterScope.toCtx)
      (R.context.venv.IsType c.lparams.length) := by
  have henv : R.context.venv.WF := R.context.checking.tr.wf
  have hP : OnCtx R.parameterScope.toCtx (R.context.venv.IsType c.lparams.length) := by
    simpa [VLCtx.toCtx] using R.sourceAnonymousParameterWF.toCtx
  have hdomains := Classical.choose_spec (H.sourceIndexDomains owner owner.isLt)
  exact (VEnv.IsType.wrapForalls_inv henv.ordered hP hdomains.2.2.1).1

/-- The generated motive of each consumed family, brought back to the source
universes, contains the family applied to the canonical parameter and index
variables, over the consumed index telescope in the cached parameter
context. -/
theorem CompletedRecursorConstruction.consumedFamilyApp_isType
    (H : CompletedRecursorConstruction R) (owner : Fin H.recInfos.size) :
    R.context.venv.IsType c.lparams.length
      ((H.sourceIndices owner).reverse ++ R.parameterScope.toCtx)
      (VExpr.mkApps
        (.const (decl.types[owner.val]'(by rw [← H.cardinality.records]; exact owner.isLt)).name
          (VLevel.params c.lparams.length))
        (recursorCanonicalVars (stats.params.size + H.recInfos[owner.val]!.indices.size))) := by
  have henv : R.context.venv.WF := R.context.checking.tr.wf
  have hP : OnCtx R.parameterScope.toCtx (R.context.venv.IsType c.lparams.length) := by
    simpa [VLCtx.toCtx] using R.sourceAnonymousParameterWF.toCtx
  have hIdx := H.consumedIndices_onCtx owner
  have hidxId : (H.sourceIndices owner).map (VExpr.instL (VLevel.params c.lparams.length)) =
      H.sourceIndices owner := by
    have h := familyTypes_ctx_instL_id hIdx
    rw [List.map_append, hP |> familyTypes_ctx_instL_id] at h
    have h2 := List.append_cancel_right h
    rw [List.map_reverse] at h2
    exact List.reverse_inj.mp h2
  have hPId := familyTypes_ctx_instL_id hP
  have hparamCtx : H.parameterSuffix.parameterDecls.toCtx =
      R.parameterScope.toCtx.map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)) := by
    have h := congrArg List.reverse H.parameterDomains
    rwa [List.reverse_reverse, ← List.map_reverse, List.reverse_reverse] at h
  -- The generated motive, at the recursor universes.
  have hsplit : H.elimLevel = .zero ∨ ∃ fresh, H.elimLevel = .param fresh := by
    have ha := H.elimLevelAdmissible
    cases helim : H.elimLevel <;> simp_all [AddInductive.AdmissibleElimLevel]
  have hpeel : ∀ {level : VLevel} {indices : List VExpr} {Γ : List VExpr} {A : VExpr},
      Γ = R.parameterScope.toCtx → indices = H.sourceIndices owner →
      R.context.venv.IsType c.lparams.length Γ
        (VExpr.wrapForalls indices (.forallE A (.sort level))) →
      R.context.venv.IsType c.lparams.length
        ((H.sourceIndices owner).reverse ++ R.parameterScope.toCtx) A := by
    intro level indices Γ A hΓ hindices hM
    subst hΓ hindices
    have hbody := (VEnv.IsType.wrapForalls_inv henv.ordered hP hM).2
    exact (VEnv.IsType.forallE_inv henv.ordered hbody).1
  rcases hsplit with helim | ⟨fresh, helim⟩
  · have hL := familyTypes_recursorLevels_zero H.elimLevelAdmissible helim
    have hmot := (H.sourceIndices_motive owner (level := .zero) (by
      rw [helim]; rfl)).2
    rw [H.recursorEnv, hparamCtx, hL, hPId] at hmot
    have hlen : (AddInductive.getRecLevelParams H.elimLevel c.lparams).length =
        c.lparams.length := by
      rw [helim]; rfl
    rw [hlen, hidxId] at hmot
    exact hpeel rfl rfl hmot
  · have hL := familyTypes_recursorLevels_param H.elimLevelAdmissible helim
    have hmot := (H.sourceIndices_motive owner (level := .param 0) (by
      rw [helim]; simp [AddInductive.getRecLevelParams, VLevel.ofLevel])).2
    rw [H.recursorEnv, hparamCtx, hL] at hmot
    have hdrop := hmot.instL (recursorDropLevels_wf (n := c.lparams.length))
    simp only [List.map_map, Function.comp_def, VExpr.instL_instL,
      VExpr.instL_wrapForalls, VExpr.instL, VExpr.instL_mkApps,
      recursorDropLevels_prependShift] at hdrop
    have hcv : (recursorCanonicalVars (stats.params.size + H.recInfos[owner.val]!.indices.size)).map
        (fun e => e.instL (recursorDropLevels c.lparams.length)) =
        recursorCanonicalVars (stats.params.size + H.recInfos[owner.val]!.indices.size) := by
      simp [recursorCanonicalVars, List.map_map, Function.comp_def, VExpr.instL]
    have heta : (fun x => VExpr.instL (VLevel.params c.lparams.length) x) =
        VExpr.instL (VLevel.params c.lparams.length) := rfl
    rw [hcv, heta, hPId, hidxId] at hdrop
    exact hpeel rfl rfl hdrop

/-- The families consumed by the recursor pass have well-formed family
applications, in the environment in which the recursors are declared.  The
telescope's well-formedness comes from the recursor pass's index replay; the
application's well-formedness from the generated motive (at the source
universes); its sort from the declared family constant, whose header is
definitionally a telescope ending in the recorded sort (source formation).
No definitional agreement of the consumed index domains with the declared
ones is used, and the checked recursor type is not consulted. -/
theorem CompletedRecursorConstruction.consumedFamilyTypesWF
    (H : CompletedRecursorConstruction R) {s : InductiveSignature}
    (hp : s.params = R.parameterScope.toCtx.reverse) (hf : s.families = H.consumedFamilies) :
    s.FamilyTypesWF R.context.venv decl.uvars := by
  intro owner
  have hown : owner.val < H.recInfos.size := by
    have hsize : s.families.size = H.recInfos.size := by rw [hf, H.consumedFamilies_size]
    have := owner.isLt
    omega
  let o : Fin H.recInfos.size := ⟨owner.val, hown⟩
  have hdecl : owner.val < decl.types.length := by rw [← H.cardinality.records]; exact hown
  have hfam : s.families[owner] = H.consumedFamilies[owner.val]'(by simp [hown]) := by
    simp only [Fin.getElem_fin, hf]
  have hidx : s.families[owner].indices = H.sourceIndices o := by
    rw [hfam]; exact H.consumedFamilies_indices o
  have hname : s.families[owner].name = (decl.types[owner.val]'hdecl).name := by
    rw [hfam]; exact H.consumedFamilies_name o
  have hlev : s.families[owner].resultLevel = (decl.types[owner.val]'hdecl).resultLevel := by
    rw [hfam]; exact H.consumedFamilies_level o
  have hU : decl.uvars = c.lparams.length := R.core.uvars
  have hPrev : s.params.reverse = R.parameterScope.toCtx := by rw [hp, List.reverse_reverse]
  have hplen : s.params.length = stats.params.size := by
    rw [hp, List.length_reverse, H.sourceParameterCount]
  have hilen : (H.sourceIndices o).length = H.recInfos[owner.val]!.indices.size :=
    H.sourceIndices_length o
  have henv : R.context.venv.WF := R.context.checking.tr.wf
  have hIdx := H.consumedIndices_onCtx o
  rw [← hU] at hIdx
  refine ⟨by rw [hidx, hPrev]; exact hIdx, ?_⟩
  -- The application is well formed (generated motive).
  have hA := H.consumedFamilyApp_isType o
  rw [← hU] at hA
  obtain ⟨_, hAty⟩ := hA
  -- The declared header is a telescope ending in the recorded sort.
  have hmem : decl.types[owner.val] ∈ decl.types := List.getElem_mem hdecl
  have hsourceWF := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF R.core
    (List.ne_nil_of_mem hmem) (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core)
  have huvars : decl.types[owner.val].uvars = decl.uvars := hsourceWF.2.2.1 _ hmem
  have hctorsLE : R.headerVEnv ≤ R.context.venv :=
    (VEnv.addConstVals_le R.core.ctorsAdded).trans R.ctorLE
  have hle : sourceEnv ≤ R.context.venv := (VEnv.addConstVals_le R.core.typesAdded).trans hctorsLE
  have hlookup : R.context.venv.constants decl.types[owner.val].name =
      some decl.types[owner.val].toVConstant :=
    hctorsLE.constants (VEnv.addConstVals_get R.core.typesAdded
      (List.mem_map.mpr ⟨_, hmem, rfl⟩))
  have hT : R.context.venv.IsType decl.uvars [] decl.types[owner.val].type := by
    have := henv.ordered.constWF hlookup
    change R.context.venv.IsType decl.types[owner.val].uvars [] decl.types[owner.val].type at this
    rwa [huvars] at this
  have hconst := VEnv.HasType.const0 hlookup (henv.ordered.constWF hlookup)
  change R.context.venv.HasType decl.types[owner.val].uvars [] (.const decl.types[owner.val].name
      (VLevel.params decl.types[owner.val].uvars)) decl.types[owner.val].type at hconst
  rw [huvars] at hconst
  obtain ⟨_, _, _, Htypes, _, _⟩ := R.formation.formationWF.sourceParameterWF
  obtain ⟨doms, body, exprType, hdlen, h1, h2⟩ := (Htypes _ hmem).header
  have hclose := VEnv.IsDefEq.close_sort_header henv hT (h1.mono hle) (h2.mono hle)
  have hW := (hconst.defeqU_r henv trivial hclose).weak0 henv.ordered
    (Γ := (H.sourceIndices o).reverse ++ R.parameterScope.toCtx)
  have hlen : (recursorCanonicalVars (stats.params.size + H.recInfos[owner.val]!.indices.size)).length =
      doms.length := by
    rw [hdlen, ← H.cardinality.params, ← H.cardinality.indices owner.val hown]
    simp [recursorCanonicalVars]
  have happ := (VEnv.HasType.mkApps_wrapForalls henv hIdx hW ⟨_, hAty⟩ hlen).2
  simp only [VExpr.instOuter_sort] at happ
  change R.context.venv.HasType decl.uvars
    (s.families[owner].indices.reverse ++ s.params.reverse)
    (VExpr.mkApps (.const s.families[owner].name (VLevel.params decl.uvars))
      (InductiveSignature.vars s.params.length s.families[owner].indices.length ++
        InductiveSignature.vars s.families[owner].indices.length 0))
    (.sort s.families[owner].resultLevel)
  rw [hidx, hPrev, hname, hlev, hplen, vars_append_canonical, hilen]
  exact happ

end VerifyInductive
end Lean4Lean
