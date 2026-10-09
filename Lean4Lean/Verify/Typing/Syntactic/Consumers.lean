import Lean4Lean.Verify.Typing.Syntactic.Strengthening
import Lean4Lean.Verify.QuotInit
import Lean4Lean.Verify.Inductive.Rules.Translation

/-!
# Three consumers restated on syntactic translation

Demonstrations for `docs/inductives/SYNTACTIC_TRANSLATION_PLAN.md`. Nothing here is used by the
verification; each section restates an existing consumer of `TrExprS` on top of `TrSyn` and
`TrTyped`, next to the original.

1. **Quotient initialization.** `QuotInit.plainTr` is a hand-written fragment of `trSyn?`
   (`plainTr_trSyn`), and `TrExprS.ofPlainTr`, which re-derives the typing premises of
   `TrExprS` by inversion, is the general `TrSyn.toTrExprS`. The quotient types are computed by
   `trSyn?` with `rfl` (`trSyn?_quot` and siblings), and `trConstant_quot_syn` is
   `trConstant_quot` with `plainTr` replaced by `trSyn?`.
2. **Projection inference.** A constructor telescope certificate is a computed translation
   together with a typing-only certificate (`CtorTelescopeAt.iff_trSyn`): the syntax of every
   deleted telescope is a theorem, and what remains is the typing of the residual types in the
   smaller contexts (`TelWF`), which the executable's locality route supplies.
3. **Iota rules.** `TrExprSyn` of `Inductive/Rules/Translation.lean` has been replaced by
   `TrSyn`, its lemmas by the `TrSyn` lemmas, and the typed right-hand side of a
   rule follows from its syntactic translation and the typing of the generator's equation
   (`RecursorCheck.ruleRhsTranslation_of_wf`), instead of from a typed translation of the same
   source (`RecursorCheck.ruleRhsTranslation`).
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/-! ### 1. Quotient initialization -/

theorem plainTr_trSyn {Us : List Name} :
    ∀ {e : Expr} {e' : VExpr} {As : List VExpr},
      plainTr Us As.length e = some e' →
      TrSyn Us (As.map fun A => (none, .vlam A)) e e'
  | .bvar i, e', As, h => by
    simp only [plainTr] at h
    split at h <;> cases h
    obtain ⟨A, hA⟩ := plainTr_find? ‹i < As.length›
    exact .bvar hA
  | .sort u, e', As, h => by
    simp only [plainTr, Option.map_eq_some_iff] at h
    obtain ⟨u', hu, rfl⟩ := h
    exact .sort hu
  | .const c us, e', As, h => by
    simp only [plainTr, Option.map_eq_some_iff] at h
    obtain ⟨us', hus, rfl⟩ := h
    exact .const hus
  | .app f a, e', As, h => by
    simp only [plainTr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨f', hf, a', ha, rfl⟩ := h
    exact .app (plainTr_trSyn hf) (plainTr_trSyn ha)
  | .forallE _ ty body _, e', As, h => by
    simp only [plainTr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ty', hty, body', hbody, rfl⟩ := h
    exact .forallE (plainTr_trSyn hty) (plainTr_trSyn (As := ty' :: As) hbody)
  | .fvar _, _, _, h | .mvar _, _, _, h | .lam .., _, _, h
  | .letE .., _, _, h | .lit _, _, _, h | .mdata .., _, _, h
  | .proj .., _, _, h => by simp [plainTr] at h

/-- `TrExprS.ofPlainTr`, as an instance of `TrSyn.toTrExprS`. -/
theorem TrExprS.ofPlainTr' {env : VEnv} {Us : List Name} (henv : env.Ordered)
    {e : Expr} {e' : VExpr} {As : List VExpr}
    (hp : plainTr Us As.length e = some e') (hΓ : OnCtx As (env.IsType Us.length))
    (hs : e.letLitFree = true) (hwf : VExpr.WF env Us.length As e') :
    TrExprS env Us (As.map fun A => (none, .vlam A)) e e' := by
  have hΔ : VLCtx.WF env Us.length (As.map fun A => (none, .vlam A)) := by
    clear hp hwf hs
    induction As with
    | nil => trivial
    | cons A As ih =>
      refine ⟨ih hΓ.1, nofun, ?_⟩
      show env.IsType Us.length (VLCtx.toCtx _) A
      rw [VLCtx.toCtx_map_anonymousLams]; exact hΓ.2
  have H := plainTr_trSyn hp
  exact H.toTrExprS henv hΔ (by simpa using hwf) (.of_simple hs H)

theorem trSyn?_quot : trSyn? [`u] [] QuotInit.tQuotC = some quotConst.type := rfl
theorem trSyn?_mk : trSyn? [`u] [] QuotInit.tMkC = some quotMkConst.type := rfl
theorem trSyn?_lift : trSyn? [`u, `v] [] QuotInit.tLiftC = some quotLiftConst.type := rfl
theorem trSyn?_ind : trSyn? [`u] [] QuotInit.tIndC = some quotIndConst.type := rfl

theorem letLitFree_quot : QuotInit.tQuotC.letLitFree ∧ QuotInit.tMkC.letLitFree ∧
    QuotInit.tLiftC.letLitFree ∧ QuotInit.tIndC.letLitFree := ⟨rfl, rfl, rfl, rfl⟩

/-- `trConstant_quot` with the computed syntactic translation in place of `plainTr`: the only
obligations left are the typing of the abstract constant and the shape of the source. -/
theorem trConstant_quot_syn {venv : VEnv} (henv : venv.Ordered) {lps : List Name} {t : Expr}
    {ci' : VConstant} (hlen : lps.length = ci'.uvars)
    (hp : trSyn? lps [] t = some ci'.type) (hs : t.letLitFree = true) (hwf : ci'.WF venv)
    (n k) :
    TrConstant .safe venv (.quotInfo { name := n, kind := k, levelParams := lps, type := t })
      ci' :=
  ⟨DefinitionSafety.le_rfl, hlen, by
    show TrExprS venv lps [] t ci'.type
    have hwf' : VExpr.WF venv lps.length [] ci'.type := by
      obtain ⟨_, h⟩ := hwf; exact ⟨_, hlen ▸ h⟩
    have H := TrSyn.of_eval hp
    exact H.toTrExprS henv trivial hwf' (.of_simple hs H)⟩

/-! ### 2. Projection inference -/

/-- The constructor telescope certificate read by `inferProj`: its translation is computed, and
its content is the typing-only certificate `TelWF`. -/
theorem CtorTelescopeAt.iff_trSyn {venv : VEnv} (henv : venv.Ordered) {ci : ConstructorVal} :
    CtorTelescopeAt venv ci ↔ ∃ T, trSyn? ci.levelParams [] ci.type = some T ∧
      TelWF venv ci.levelParams (AddInductive.constructorArity ci.type) [] ci.type T := by
  constructor
  · rintro ⟨T, H⟩
    obtain ⟨S, W⟩ := (TelTrN.iff_syn_telWF henv (show VLCtx.WF venv _ [] from trivial)).1 H
    exact ⟨T, S.eval, W⟩
  · rintro ⟨T, hT, W⟩
    exact ⟨T, (TelTrN.iff_syn_telWF henv (show VLCtx.WF venv _ [] from trivial)).2 ⟨.of_eval hT, W⟩⟩

/-- The delete step of the projection walk (`TelTrN.delete_closed`), read through the
decomposition: the lowered translation and its relation to the body are syntactic; the
certificate's content at the deleted binder is the typing of the lowered residual telescope in
the smaller context. -/
theorem TelWF.delete_closed {env : VEnv} {Us : List Name} {Δ : VLCtx}
    (S : TrSyn Us Δ (.forallE nm d b bi) (.forallE d' b'))
    (H : TelWF env Us (n + 1) Δ (.forallE nm d b bi) (.forallE d' b'))
    (hb : b.looseBVarRange' ≤ 0) :
    ∃ b₀', b' = VExpr.lift b₀' ∧ TrSyn Us Δ b b₀' ∧ TelWF env Us n Δ b b₀' := by
  have e : b = Expr.liftLooseBVars' b 0 1 := (Expr.liftLooseBVars_eq_self hb).symm
  let .forallE _ sb := S
  rw [e] at sb
  obtain ⟨b₀', s, hb'⟩ := sb.lower
  cases H with
  | succ _ _ _ h4 => exact ⟨b₀', hb', s, h4 _ _ e hb'⟩

/-! ### 3. The iota rules' syntactic translation

`TrExprSyn` (`Inductive/Rules/Translation.lean`) is now `TrSyn` itself (an abbreviation kept for
`Inductive/Prelude/EqSyntax.lean`), and its former lemmas are the `TrSyn` lemmas: the
right-hand-side derivations `RecursorCheck.ruleRhsSyn` are `TrSyn` derivations. -/

namespace VerifyInductive

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The typed translation of a rule's right-hand side from its syntactic translation
(`RecursorCheck.ruleRhsSyn`) and the typing of the generator's equation right-hand side. The
existing `RecursorCheck.ruleRhsTranslation` asks instead for some typed translation of the same
source, which `RecursorCheck.ruleRhsTyped` builds from the checker's typing of the rule. -/
theorem RecursorCheck.ruleRhsTranslation_of_wf {outEnv : Environment}
    (H : RecursorCheck R outEnv) (henv : H.outVEnv.Ordered)
    (o : Nat) (ho : o < H.entries.length)
    (i : Nat) (hi : i < (H.generated.entry o ho).info.rules.length)
    (hs : ((H.generated.entry o ho).info.rules[i]).rhs.letLitFree = true)
    (hwf : ∀ hk : recursorMinorOffset indTypes o + i < H.generator.signature.constructors.size,
      VExpr.WF H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        (H.generator.generation.equation ⟨recursorMinorOffset indTypes o + i, hk⟩).rhs) :
    ∃ hk : recursorMinorOffset indTypes o + i < H.generator.signature.constructors.size,
      TrExprS H.outVEnv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
        ((H.generated.entry o ho).info.rules[i]).rhs
        (H.generator.generation.equation ⟨recursorMinorOffset indTypes o + i, hk⟩).rhs := by
  obtain ⟨hk, S⟩ := H.ruleRhsSyn o ho i hi
  exact ⟨hk, S.toTrExprS henv trivial (hwf hk) (.of_simple hs S)⟩

end VerifyInductive

end Lean4Lean
