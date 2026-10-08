import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.Inductive.Recursor.CanonicalMinorFields
import Lean4Lean.Verify.Inductive.Recursor.SourceUniverses

/-! Uniqueness of translated binder telescopes.

A list of abstract domains translating a list of source domains, each in the
abstract context of the earlier ones, is determined by the sources.  A
well-formed lambda-only typechecker metacontext supplies such a telescope:
each stored binder type, abstracted over the earlier identifiers, translates
to the stored abstract domain in the abstract context of the earlier
domains. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker

/-- The stored binder types of a metacontext, outermost first. -/
def TypeChecker.MLCtx.lamTypes : TypeChecker.MLCtx → List Lean.Expr
  | .nil => []
  | .vlam _ _ ty _ _ c => c.lamTypes ++ [ty]
  | .vlet _ _ ty _ _ _ c => c.lamTypes ++ [ty]

@[simp] theorem TypeChecker.MLCtx.lamTypes_length (c : TypeChecker.MLCtx) :
    c.lamTypes.length = c.length := by
  induction c <;> simp [lamTypes, *]

/-- Every entry of a lambda-only metacontext's abstract context is a named
lambda. -/
theorem TypeChecker.MLCtx.vlctx_allLams :
    ∀ (c : TypeChecker.MLCtx), VerifyInductive.MLCtxOnlyLams c →
      ∀ entry ∈ c.vlctx, ∃ fv deps ty, entry = (some (fv, deps), .vlam ty)
  | .nil, _ => by simp
  | .vlet .., honly => honly.vlet_false.elim
  | .vlam id name ty ty' bi c, honly => by
    intro entry hentry
    simp only [MLCtx.vlctx, List.mem_cons] at hentry
    rcases hentry with rfl | h
    · exact ⟨_, _, _, rfl⟩
    · exact vlctx_allLams c honly.tail_vlam entry h

/-- The local declaration found at an identifier of a lambda-only
metacontext carries the stored binder type at the same position. -/
theorem TypeChecker.MLCtx.lamTypes_find? {env : VEnv} {Us : List Name} :
    ∀ (c : TypeChecker.MLCtx) (_hwf : c.WF env Us) (honly : VerifyInductive.MLCtxOnlyLams c)
      (k : Nat) (hk : k < c.length) (decl : LocalDecl),
      c.lctx.find? (c.vlctx.fvars.reverse[k]'(by simpa [honly.fvars_length] using hk)) =
        some decl →
      decl.type = c.lamTypes[k]'(by rw [lamTypes_length]; exact hk)
  | .nil, _, _, k, hk, _, _ => by simp at hk
  | .vlet .., _, honly, _, _, _, _ => honly.vlet_false.elim
  | .vlam id name ty ty' bi c, hwf, honly, k, hk, decl, hfind => by
    obtain ⟨hwfc, hfresh, _, _⟩ := hwf
    have honlyc := honly.tail_vlam
    have hlenF : c.vlctx.fvars.reverse.length = c.length := by
      simp [honlyc.fvars_length]
    have hF : (MLCtx.vlam id name ty ty' bi c).vlctx.fvars.reverse =
        c.vlctx.fvars.reverse ++ [id] := by simp
    have hL : (MLCtx.vlam id name ty ty' bi c).lamTypes = c.lamTypes ++ [ty] := rfl
    have hk' : k ≤ c.length := by simp at hk; omega
    simp only [hF] at hfind
    simp only [hL]
    rcases Nat.lt_or_eq_of_le hk' with hlt | rfl
    · rw [List.getElem_append_left (by omega)] at hfind
      rw [List.getElem_append_left (by simpa using hlt)]
      have hmem : c.vlctx.fvars.reverse[k]'(by omega) ∈ c.vlctx.fvars :=
        List.mem_reverse.mp (List.getElem_mem _)
      have hne : id ≠ c.vlctx.fvars.reverse[k]'(by omega) := fun h =>
        hwfc.tr.find?_eq_none.1 hfresh (h ▸ hmem)
      simp only [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl, LocalContext.find?,
        hwfc.tr.1.map_wf.find?_insert] at hfind
      rw [if_neg (by intro heq; exact hne (beq_iff_eq.mp heq))] at hfind
      exact lamTypes_find? c hwfc honlyc k hlt decl hfind
    · rw [List.getElem_append_right (by omega)] at hfind
      rw [List.getElem_append_right (by simp)]
      simp only [List.getElem_cons_zero, Nat.sub_self, hlenF, lamTypes_length] at hfind ⊢
      simp only [TypeChecker.MLCtx.lctx, LocalContext.mkLocalDecl, LocalContext.find?,
        hwfc.tr.1.map_wf.find?_insert, BEq.rfl, ↓reduceIte, Option.some.injEq] at hfind
      subst hfind
      rfl

namespace VerifyInductive

/-- Two telescopes of abstract domains translating the same source domains,
each in the context of the earlier ones, coincide. -/
theorem TrExprS.telescope_unique {env : VEnv} {Us : List Name} (Δ : VLCtx) :
    ∀ (sources : List Lean.Expr) (L₁ L₂ : List VExpr),
      (h₁ : L₁.length = sources.length) → (h₂ : L₂.length = sources.length) →
      (∀ i (h : i < sources.length), TrExprS env Us (abstractForallContext (L₁.take i) Δ)
        sources[i] (L₁[i]'(by omega))) →
      (∀ i (h : i < sources.length), TrExprS env Us (abstractForallContext (L₂.take i) Δ)
        sources[i] (L₂[i]'(by omega))) →
      L₁ = L₂ := by
  intro sources L₁ L₂ h₁ h₂ H₁ H₂
  have key : ∀ n, n ≤ sources.length → L₁.take n = L₂.take n := by
    intro n
    induction n with
    | zero => intro; simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hn' : n < sources.length := by omega
      have heq : L₁[n]'(by omega) = L₂[n]'(by omega) := by
        have a := H₁ n hn'
        have b := H₂ n hn'
        rw [hprev] at a
        exact a.uniqueS b
      rw [List.take_add_one, List.take_add_one, hprev, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem (h := by omega), heq]
  have := key sources.length (Nat.le_refl _)
  rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this

/-- Universe un-shift: a translation under a fresh leading universe of
source syntax omitting it is the shift of a translation without it. -/
theorem TrExprS.chooseOriginalUniverses_eq {env : VEnv} {Us : List Name} {fresh : Name}
    {Δ : VLCtx} {e : Lean.Expr} {e' : VExpr}
    (henv : env.WF) (hΔ : VLCtx.WF env Us.length Δ) (hfresh : fresh ∉ Us)
    (hsource : Expr.instantiateLevelParamsCore' false (recursorDropLevel fresh) e = e)
    (H : TrExprS env (fresh :: Us) (Δ.instL (VLevel.prependShift Us.length)) e e') :
    ∃ sourceTarget, TrExprS env Us Δ e sourceTarget ∧
      e' = sourceTarget.instL (VLevel.prependShift Us.length) := by
  obtain ⟨t, ht, hshift⟩ := H.chooseOriginalUniverses henv hΔ hfresh hsource
  exact ⟨t, ht, H.uniqueS hshift⟩

end VerifyInductive
end Lean4Lean
