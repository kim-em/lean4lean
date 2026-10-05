import Lean4Lean.Verify.Typing.UniverseSupport
import Lean4Lean.Verify.Inductive.Recursor.SourceReplay
import Lean4Lean.Verify.Inductive.Recursor.SourceUniverses
namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

@[simp] theorem Expr.levelParamsIn_instantiate1_fvar (e : Expr) (fv : FVarId) (k : Nat) :
    (e.instantiate1' (.fvar fv) k).levelParamsIn params = e.levelParamsIn params := by
  induction e generalizing k <;> simp [Expr.instantiate1', Expr.levelParamsIn, *]
  case bvar i =>
    split
    · rfl
    · split <;> rfl

theorem Expr.levelParamsIn_consumeTypeAnnotationsVerified {e : Expr}
    (H : e.levelParamsIn params = true) : e.consumeTypeAnnotationsVerified.levelParamsIn params = true := by
  fun_induction Expr.consumeTypeAnnotationsVerified e
  all_goals simp_all [Expr.levelParamsIn]

namespace VerifyInductive

def FieldUniverseSupport (params : List Name) (c : AddInductive.Context) (fields : Array Expr) : Prop :=
  ∀ e ∈ fields, ∃ fv index name type bi kind,
    e = .fvar fv ∧ c.lctx.find? fv = some (.cdecl index fv name type bi kind) ∧
      type.levelParamsIn params = true

private theorem fieldUniverseSupport_push
    (Hc : BindingContextWF c) (H : FieldUniverseSupport params c fields)
    (hdom : dom.levelParamsIn params = true) :
    FieldUniverseSupport params { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name dom bi }
      (fields.push (.fvar ⟨c.ngen.curr⟩)) := by
  intro e he
  simp only [Array.mem_push] at he
  have hnew : (c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name dom bi).find? ⟨c.ngen.curr⟩ =
      some (.cdecl c.lctx.decls.size ⟨c.ngen.curr⟩ name dom bi .default) := by
    simp [LocalContext.mkLocalDecl, LocalContext.find?, Hc.wf.map_wf.find?_insert]
  rcases he with he | rfl
  · obtain ⟨fv, index, oldName, type, oldBi, kind, rfl, hfind, htype⟩ := H e he
    by_cases hfv : fv = ⟨c.ngen.curr⟩
    · subst fv
      exact ⟨_, _, _, _, _, _, rfl, hnew, hdom⟩
    · refine ⟨fv, index, oldName, type, oldBi, kind, rfl, ?_, htype⟩
      simpa [LocalContext.mkLocalDecl, LocalContext.find?, Hc.wf.map_wf.find?_insert,
        Ne.symm hfv] using hfind
  · exact ⟨_, _, _, _, _, _, rfl, hnew, hdom⟩

theorem RecursorFieldDecisions.levelParamsIn
    (H : RecursorFieldDecisions stats root source current terminal fields selected positions)
    (Hroot : BindingContextWF root) (hsource : source.levelParamsIn params = true) :
    terminal.levelParamsIn params = true ∧ FieldUniverseSupport params current fields := by
  induction H with
  | nil => exact ⟨hsource, by intro e he; simp at he⟩
  | @nonrecursive c name dom body bi fields selected positions H _ ih
  | @recursive c name dom body bi fields selected positions target H _ ih =>
    have Hc := (H.freshBindings Hroot).choose
    have hx : dom.levelParamsIn params = true ∧ body.levelParamsIn params = true := by
      simpa [Expr.levelParamsIn] using ih.1
    have hdom := hx.1
    have hbody := hx.2
    refine ⟨?_, fieldUniverseSupport_push Hc ih.2
      (Expr.levelParamsIn_consumeTypeAnnotationsVerified hdom)⟩
    simpa using hbody

theorem FieldUniverseSupport.mono
    (H : FieldUniverseSupport params c fields) (Hfields : BoundFVarArray c fields)
    (hle : BindingContextLE c c') : FieldUniverseSupport params c' fields := by
  intro e he
  obtain ⟨fv, index, name, type, bi, kind, rfl, hfind, htype⟩ := H e he
  have hfv : fv ∈ c.lctx.fvars := by
    rw [Hfields.expressions] at he
    simp only [List.mem_toArray, List.mem_map, Expr.fvar.injEq] at he
    obtain ⟨fv', hfv', rfl⟩ := he
    exact Hfields.members _ hfv'
  exact ⟨fv, index, name, type, bi, kind, rfl, (hle.declarations fv hfv).trans hfind, htype⟩

theorem FieldUniverseSupport.mkForall
    (H : FieldUniverseSupport params c fields) (Hfields : BoundFVarArray c fields)
    (hbody : body.levelParamsIn params = true) :
    (c.lctx.mkForall fields body).levelParamsIn params = true := by
  have hdecl : ∀ fv ∈ Hfields.fvars, ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) ∧ type.levelParamsIn params = true := by
    intro fv hfv
    have he : Expr.fvar fv ∈ fields := by
      rw [Hfields.expressions]
      simpa using hfv
    obtain ⟨fv', index, name, type, bi, kind, heq, hfind, htype⟩ := H _ he
    cases Expr.fvar.inj heq
    exact ⟨index, name, type, bi, kind, hfind, htype⟩
  have hgo : ∀ fvars : List FVarId, (∀ fv ∈ fvars, fv ∈ Hfields.fvars) →
      ∀ body : Expr, body.levelParamsIn params = true →
      (LocalContext.mkBindingList.go false c.lctx fvars body).levelParamsIn params = true := by
    intro fvars hmem body hbody
    induction fvars generalizing body with
    | nil => exact hbody
    | cons fv fvars ih =>
      obtain ⟨index, name, type, bi, kind, hfind, htype⟩ := hdecl fv (hmem _ (by simp))
      apply ih (fun other hother => hmem other (by simp [hother]))
      simpa [LocalContext.mkBindingList1, hfind, Expr.levelParamsIn, htype] using hbody
  rw [Hfields.expressions, LocalContext.mkForall, LocalContext.mkBinding_eq]
  apply hgo Hfields.fvars.reverse (by simp) _
  simpa using hbody

/-- Constructor fields are opened from literal source syntax, with only
annotation consumption. Their accepted domains therefore stay in the source
universe scope even though the surrounding recursor context has a fresh level. -/
theorem CompletedRecursorConstruction.minorFieldSourceUniverses
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size)
    (hsourceOwner : owner < indTypes.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (hindex : recursorMinorOffset indTypes owner + localIndex < decl.ownedConstructors.length) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    ((H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars).levelParamsIn
      c.lparams = true := by
  let S := H.origins.minorShapes owner howner localIndex hlocal
  obtain ⟨HS⟩ := H.minorSemantics owner howner localIndex hlocal
  obtain ⟨traversal, htraversal, _, _, _, Htr⟩ :=
    H.minorSourceReplay owner howner hsourceOwner localIndex hlocal hindex
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  rw [heq] at Htr
  have Hsupport := HS.semantic.traversal.decisions.levelParamsIn
    HS.semantic.rootWF.toBindingContextWF Htr.levelParamsIn
  have Hfields : FieldUniverseSupport c.lparams HS.semantic.traversal.terminalContext S.fields := by
    simpa [HS.semantic.traversal_fields] using Hsupport.2
  have Hext := HS.semantic.hypothesesRecent.contextLE.trans HS.semantic.extension.contextLE
  have Hfull := Hfields.mono HS.semantic.fieldsRecent.toBoundFVarArray Hext
  have Hbound := S.fields_bound.mono HS.semantic.extension.contextLE
  simpa using Hfull.mkForall Hbound (body := .sort .zero) rfl

end VerifyInductive
end Lean4Lean
