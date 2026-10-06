import Lean4Lean.Verify.Inductive.Recursor.TelescopeUniqueness
import Lean4Lean.Verify.Inductive.Recursor.SecondPass
import Lean4Lean.Verify.Inductive.Recursor.FieldTypeScope

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker
open scoped _root_.List

/-! Restriction of a generated recursive call's context to the shape row of
its recursive field: the call-local arguments, the fields before the
recursive field, and the parameters. -/

/-- A sublist of a duplicate-free list is the filter of that list by its
membership predicate. -/
theorem List.Sublist.eq_filter_of_nodup {α : Type} {p : α → Bool} :
    ∀ {l' l : List α}, l' <+ l → l.Nodup → (∀ x, x ∈ l' ↔ x ∈ l ∧ p x) → l' = l.filter p
  | _, _, .slnil, _, _ => rfl
  | l', a :: l, .cons _ h, hnd, hmem => by
    have hpa : ¬ p a := by
      intro hp
      have : a ∈ l' := (hmem a).2 ⟨List.mem_cons_self, hp⟩
      exact (List.nodup_cons.1 hnd).1 (h.subset this)
    rw [List.filter_cons_of_neg hpa]
    refine eq_filter_of_nodup h (List.nodup_cons.1 hnd).2 fun x => ?_
    constructor
    · intro hx
      have := (hmem x).1 hx
      rcases List.mem_cons.1 this.1 with rfl | hx'
      · exact absurd this.2 hpa
      · exact ⟨hx', this.2⟩
    · rintro ⟨hx, hp⟩
      exact (hmem x).2 ⟨List.mem_cons_of_mem _ hx, hp⟩
  | _, a :: l, .cons_cons _ h, hnd, hmem => by
    have hpa : p a := ((hmem a).1 List.mem_cons_self).2
    rw [List.filter_cons_of_pos hpa]
    congr 1
    refine eq_filter_of_nodup h (List.nodup_cons.1 hnd).2 fun x => ?_
    constructor
    · intro hx
      have hxa : x ≠ a := fun heq => (List.nodup_cons.1 hnd).1 (heq ▸ h.subset hx)
      have := (hmem x).1 (List.mem_cons_of_mem _ hx)
      rcases List.mem_cons.1 this.1 with rfl | hx'
      · exact absurd rfl hxa
      · exact ⟨hx', this.2⟩
    · rintro ⟨hx, hp⟩
      have hxa : x ≠ a := fun heq => (List.nodup_cons.1 hnd).1 (heq ▸ hx)
      rcases List.mem_cons.1 ((hmem x).2 ⟨List.mem_cons_of_mem _ hx, hp⟩) with heq | hx'
      · exact absurd heq hxa
      · exact hx'


/-- Two sublists of a duplicate-free list with the same members coincide. -/
theorem List.Sublist.eq_of_nodup_of_mem_iff {α : Type} {l₁ l₂ l : List α}
    (h₁ : l₁ <+ l) (h₂ : l₂ <+ l) (hnd : l.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁ = l₂ := by
  classical
  have e₁ := List.Sublist.eq_filter_of_nodup h₁ (p := fun x => decide (x ∈ l₂)) hnd fun x => by
    rw [hmem x, decide_eq_true_iff]
    exact ⟨fun h => ⟨h₂.subset h, h⟩, fun h => h.2⟩
  have e₂ := List.Sublist.eq_filter_of_nodup h₂ (p := fun x => decide (x ∈ l₂)) hnd fun x => by
    rw [decide_eq_true_iff]
    exact ⟨fun h => ⟨h₂.subset h, h⟩, fun h => h.2⟩
  rw [e₁, ← e₂]

namespace VerifyInductive

/-- Restrict the current context of a generated recursive call to its shape
row: the recent call-local arguments, then the fields before the recursive
field at `pos`, then the parameters (newest first).  Retained declarations
keep their original types, the parameter part of the abstract context is
literally the cached parameter suffix, and the exposed type still
translates. -/
theorem SemanticBoundGeneratedRecursiveCall.restrictToFieldPrefix
    {root c origin : AddInductive.Context} {recLparams : List Name}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {Rroot : RecursorContextWF root recLparams} {Rfield : RecursorContextWF c recLparams}
    {Rorigin : RecursorContextWF origin recLparams} {fields prior : Array Expr}
    (Hsuffix : RecursorParameterContextSuffix Rroot stats depth)
    (Hfields : RecursorRecentBoundFVarArray Rroot Rfield fields)
    (Hprior : RecursorRecentBoundFVarArray Rfield Rorigin prior)
    {indTypes : Array InductiveType} {motives minors : Array Expr} {lvls : List Level}
    {decl : VInductDecl} {d : Nat} {field value : Expr}
    (Sc : SemanticBoundGeneratedRecursiveCall indTypes stats motives minors lvls Rorigin decl d
      field value)
    (pos : Nat) (hpos : pos < Hfields.fvars.length)
    (hscope : Sc.rootScope =
      RecursorFieldPrefixScope stats.params Hfields.fvars (.fvar Hfields.fvars[pos])) :
    ∃ c' : TypeChecker.MLCtx,
      c'.WF Sc.current_context.venv recLparams ∧ VerifyInductive.MLCtxOnlyLams c' ∧
      c'.vlctx.fvars = Sc.recent.fvars.reverse ++ (Hfields.fvars.take pos).reverse ++
        (ExprArrayFVarIds stats.params).reverse ∧
      (∀ fv decl', c'.lctx.find? fv = some decl' →
        ∃ decl, Sc.generated.current.lctx.find? fv = some decl ∧ decl.type = decl'.type) ∧
      c'.vlctx.toCtx.reverse.take stats.params.size = Hsuffix.parameterDecls.toCtx.reverse ∧
      ∃ exposedTarget', TrExprS Sc.current_context.venv recLparams c'.vlctx
        Sc.generated.exposedType exposedTarget' := by
  let Rc := Sc.current_context
  have henv : Rc.venv.WF := Rc.checking.tr.wf
  have hidx : Hfields.fvars.idxOf Hfields.fvars[pos] = pos :=
    List.Nodup.idxOf_getElem Hfields.nodup pos hpos
  have hroot : ∀ fv, Sc.rootScope fv ↔
      fv ∈ Hfields.fvars.take pos ∨ fv ∈ ExprArrayFVarIds stats.params := by
    intro fv
    rw [hscope]
    simp only [RecursorFieldPrefixScope, recursorFVarId, hidx]
  obtain ⟨c', n, hwf', honly', W, hfvars, hfind⟩ :=
    TypeChecker.MLCtx.restrictUpSetCtx henv _ Rc.mlctx Rc.mlctx_wf Rc.onlyLams
      Sc.current_scope_up
  -- the full context decomposition
  have hfull : Rc.mlctx.vlctx.fvars = Sc.recent.fvars.reverse ++ (Hprior.fvars.reverse ++
      (Hfields.fvars.reverse ++ (Hsuffix.ambientDecls.fvars ++
        (ExprArrayFVarIds stats.params).reverse))) := by
    rw [Sc.recent.contextFVars, Hprior.contextFVars, Hfields.contextFVars, Hsuffix.context,
      VLCtx.fvars_append, Hsuffix.parameterDecls_fvars]
  have hnodup : Rc.mlctx.vlctx.fvars.Nodup := Rc.mlctx_wf.fvars_nodup
  let T := Sc.recent.fvars.reverse ++ (Hfields.fvars.take pos).reverse ++
    (ExprArrayFVarIds stats.params).reverse
  have hTsub : T <+ Rc.mlctx.vlctx.fvars := by
    rw [hfull]
    simp only [T, List.append_assoc]
    refine List.Sublist.append (.refl _) ?_
    refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
    refine List.Sublist.append ?_ ?_
    · exact (List.take_sublist _ _).reverse
    · exact List.sublist_append_right _ _
  have hPT : ∀ fv, (fv ∈ Sc.recent.fvars ∨ Sc.rootScope fv) ↔ fv ∈ T := by
    intro fv
    rw [hroot]
    simp [T]
  have hc'fvars : c'.vlctx.fvars = T := by
    refine List.Sublist.eq_of_nodup_of_mem_iff W.fvars_sublist hTsub hnodup fun fv => ?_
    rw [hfvars, hPT]
    exact ⟨fun h => h.2, fun h => ⟨hTsub.subset h, h⟩⟩

  have hfind' : ∀ fv decl', c'.lctx.find? fv = some decl' →
      ∃ decl, Sc.generated.current.lctx.find? fv = some decl ∧ decl.type = decl'.type :=
    fun fv decl' h => by rw [← Sc.current_context.lctx_eq]; exact hfind fv decl' h
  -- (iv) the exposed type translates in the restricted context
  have hvwf : VLCtx.WF Rc.venv recLparams.length Rc.mlctx.vlctx := Rc.mlctx_wf.tr.wf
  have hc : Closed Sc.generated.exposedType 0 := by
    have h := Sc.exposed_translation.closed
    rwa [Rc.mlctx.noBV] at h
  have hv : Sc.generated.exposedType.FVarsIn (· ∈ c'.vlctx.fvars) :=
    Sc.exposed_scope.mono fun fv h => by rw [hc'fvars]; exact (hPT fv).1 h
  obtain ⟨e', he'⟩ :=
    Sc.exposed_translation.weakFV'_inv henv W (.refl henv.ordered hvwf) hc hv
  -- (iii) the parameter suffix carries exactly the cached parameter domains
  let nP := stats.params.size
  have hPmlen : (ExprArrayFVarIds stats.params).length = nP := by simp [ExprArrayFVarIds, nP]
  have hdepth : depth ≤ Rroot.mlctx.length := by
    have := congrArg List.length Hsuffix.context
    rw [TypeChecker.MLCtx.vlctx_length, List.length_append, Hsuffix.prefixLength] at this
    omega
  let cP := Rroot.mlctx.dropN depth hdepth
  have hwfP : cP.WF Rroot.venv recLparams := Rroot.mlctx_wf.dropN depth hdepth
  have honlyP : MLCtxOnlyLams cP := Rroot.onlyLams.dropN depth hdepth
  have hcP : cP.vlctx = Hsuffix.parameterDecls := by
    rw [Rroot.onlyLams.vlctx_dropN, Hsuffix.context, List.drop_left' Hsuffix.prefixLength]
  have hcPf : cP.vlctx.fvars = (ExprArrayFVarIds stats.params).reverse := by
    rw [hcP, Hsuffix.parameterDecls_fvars]
  have hc'len : c'.length = Sc.recent.fvars.length + pos + nP := by
    rw [← honly'.fvars_length, hc'fvars]
    simp [T, hPmlen, Nat.min_eq_left (Nat.le_of_lt hpos), Nat.add_assoc]
  have hnP : c'.length - nP ≤ c'.length := Nat.sub_le _ _
  let cQ := c'.dropN (c'.length - nP) hnP
  have hwfQ : cQ.WF Rc.venv recLparams := hwf'.dropN _ hnP
  have honlyQ : MLCtxOnlyLams cQ := honly'.dropN _ hnP
  have hcQf : cQ.vlctx.fvars = (ExprArrayFVarIds stats.params).reverse := by
    have h := TypeChecker.MLCtx.fvars_eq_append c' (n := c'.length - nP) (hn := hnP)
    rw [hc'fvars] at h
    refine (List.append_inj h.symm ?_).2
    simp [hc'len, Nat.min_eq_left (Nat.le_of_lt hpos)]
  have hFeq : cQ.vlctx.fvars = cP.vlctx.fvars := by rw [hcQf, hcPf]
  have hQlen : cQ.length = nP := by
    rw [← honlyQ.fvars_length, hcQf, List.length_reverse, hPmlen]
  have hPlen : cP.length = nP := by
    rw [← honlyP.fvars_length, hcPf, List.length_reverse, hPmlen]
  have hvenv : Rc.venv = Rroot.venv := by
    rw [Sc.recent.venv_eq, Hprior.venv_eq, Hfields.venv_eq]
  have hLE : BindingContextLE root Sc.generated.current :=
    Hfields.contextLE.trans (Hprior.contextLE.trans Sc.recent.contextLE)
  have hL : cQ.lamTypes = cP.lamTypes := by
    apply List.ext_getElem (by simp [hQlen, hPlen])
    intro i hiQ' hiP'
    have hiQ : i < cQ.length := by simpa using hiQ'
    have hiP : i < cP.length := by simpa using hiP'
    have hmemP : cP.vlctx.fvars.reverse[i]'(by simpa [honlyP.fvars_length] using hiP) ∈
        cP.vlctx.fvars := List.mem_reverse.mp (List.getElem_mem _)
    obtain ⟨dP, hdP⟩ := hwfP.tr.find?_eq_some.2 hmemP
    have htyP := TypeChecker.MLCtx.lamTypes_find? cP hwfP honlyP i hiP dP hdP
    have hmemQ : cQ.vlctx.fvars.reverse[i]'(by simpa [honlyQ.fvars_length] using hiQ) ∈
        cQ.vlctx.fvars := List.mem_reverse.mp (List.getElem_mem _)
    obtain ⟨dQ, hdQ⟩ := hwfQ.tr.find?_eq_some.2 hmemQ
    have htyQ := TypeChecker.MLCtx.lamTypes_find? cQ hwfQ honlyQ i hiQ dQ hdQ
    have hfvEq : cQ.vlctx.fvars.reverse[i]'(by simpa [honlyQ.fvars_length] using hiQ) =
        cP.vlctx.fvars.reverse[i]'(by simpa [honlyP.fvars_length] using hiP) := by
      simp only [hFeq]
    rw [hfvEq] at hdQ hmemQ
    generalize cP.vlctx.fvars.reverse[i]'(by simpa [honlyP.fvars_length] using hiP) = fv
      at hdP hdQ hmemP hmemQ
    rw [← honly'.dropN_find?_eq hwf' _ hnP hmemQ] at hdQ
    obtain ⟨dd, hdd, hty⟩ := hfind' fv dQ hdQ
    rw [← Rroot.onlyLams.dropN_find?_eq Rroot.mlctx_wf _ hdepth hmemP, Rroot.lctx_eq] at hdP
    have hmemRoot : fv ∈ root.lctx.fvars := by
      rw [← Rroot.lctx_eq, Rroot.mlctx_wf.tr.fvars_eq]
      exact TypeChecker.MLCtx.dropN_fvars_subset depth hdepth hmemP
    rw [hLE.declarations fv hmemRoot, hdP] at hdd
    cases hdd
    rw [← htyQ, ← htyP, hty]
  have htake : c'.vlctx.toCtx.reverse.take nP = cQ.vlctx.toCtx.reverse := by
    rw [honly'.toCtx_dropN, List.take_reverse, honly'.toCtx_length]
  have hparams : cQ.vlctx.toCtx.reverse = cP.vlctx.toCtx.reverse := by
    refine TrExprS.telescope_unique (env := Rroot.venv) (Us := recLparams) []
      (List.ofFn (n := cP.length) fun i =>
        (cP.lamTypes[i.1]'(by simp)).abstractList (cP.vlctx.fvars.reverse.take i.1))
      _ _ (by simp [honlyQ.toCtx_length, hQlen, hPlen])
      (by simp [honlyP.toCtx_length]) ?_ ?_
    · intro i h
      have := TypeChecker.MLCtx.lamTypes_telescope cQ hwfQ honlyQ i
        (by simp [hQlen, hPlen] at h ⊢; omega)
      simp only [hL, hFeq, hvenv] at this
      simpa using this
    · intro i h
      have := TypeChecker.MLCtx.lamTypes_telescope cP hwfP honlyP i (by simpa using h)
      simpa using this
  refine ⟨c', hwf', honly', hc'fvars, hfind', ?_, e', he'⟩
  rw [htake, hparams, hcP]

end VerifyInductive

end Lean4Lean
