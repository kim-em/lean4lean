import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaOperationalSemantics
import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaGenerated

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Shape-derived primary-iota LHS telescope facts -/

/-- Rebuild the complete nested recursor telescope from its five successive
`takeForalls` observations. -/
theorem VInductDecl.NestedRecursorShape.type_eq_wrapForalls
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    (H : decl.NestedRecursorShape owner recursor) :
    recursor.type = VExpr.wrapForalls
      (H.params ++ H.motives ++ H.minors ++ H.indices ++ H.major)
      H.result := by
  have hp := (VExpr.takeForalls_rebuild H.params_take).1
  have hm := (VExpr.takeForalls_rebuild H.motives_take).1
  have hmi := (VExpr.takeForalls_rebuild H.minors_take).1
  have hi := (VExpr.takeForalls_rebuild H.indices_take).1
  have hmajor := (VExpr.takeForalls_rebuild H.major_take).1
  rw [hp, hm, hmi, hi, hmajor]
  simp only [VExpr.wrapForalls_append, List.append_assoc]

/-- After consuming a prefix of a telescope with one remaining binder, the
literal result is still a forall.  This purely syntactic lemma avoids making
the resulting dependent domain an extra producer premise. -/
theorem VExpr.applyForallType_wrapForalls_append_singleton_exists
    (pre args : List VExpr) (last body : VExpr)
    (hlength : args.length = pre.length) :
    ∃ domain result,
      VExpr.applyForallType
        (VExpr.wrapForalls (pre ++ [last]) body) args =
          .forallE domain result := by
  induction args generalizing pre last body with
  | nil =>
    have hpre : pre = [] :=
      List.eq_nil_of_length_eq_zero hlength.symm
    subst pre
    exact ⟨last, body, rfl⟩
  | cons arg args ih =>
    cases pre with
    | nil => simp at hlength
    | cons domain pre =>
      have htail : args.length = pre.length := by
        simpa using Nat.succ.inj hlength
      change ∃ nextDomain result,
        VExpr.applyForallType
          ((VExpr.wrapForalls (pre ++ [last]) body).inst arg) args =
            .forallE nextDomain result
      rw [VExpr.inst_wrapForalls,
        VExpr.instForallDomains_append]
      simp only [Nat.zero_add, List.length_append, List.length_singleton]
      have hsingle : VExpr.instForallDomains [last] arg pre.length =
          [last.inst arg pre.length] := by
        rfl
      rw [hsingle]
      exact ih (VExpr.instForallDomains pre arg 0)
        (last.inst arg pre.length)
        (body.inst arg (pre.length + 1)) (by
          simpa using htail)

/-- The major binder exposed after the generated equation's leading
arguments is forced by the retained nested-recursor shape.  In particular,
`RestoredPrimaryLhsSpineAlignment.leadingResult` is not an independent
semantic obligation. -/
theorem VInductDecl.NestedIotaRule.leadingResult_exists
    {decl : VInductDecl} {block : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {rule : VDefEq}
    (H : decl.NestedIotaRule block owner ctor rule) :
    ∃ majorDomain resultBody,
      VExpr.applyForallType
        (H.recursor.type.instL H.recursorLevels) H.leadingArgs =
          .forallE majorDomain resultBody := by
  have hparams : H.recursor_shape.params.length = decl.nparams :=
    VExpr.takeForalls_domains_length H.recursor_shape.params_take
  have hindices : H.recursor_shape.indices.length = owner.numIndices :=
    VExpr.takeForalls_domains_length H.recursor_shape.indices_take
  have hmajor : H.recursor_shape.major.length = 1 :=
    VExpr.takeForalls_domains_length H.recursor_shape.major_take
  cases hmajorList : H.recursor_shape.major with
  | nil => simp [hmajorList] at hmajor
  | cons major tail =>
    have htail : tail = [] := by simpa [hmajorList] using hmajor
    subst tail
    let pre := H.recursor_shape.params ++ H.recursor_shape.motives ++
      H.recursor_shape.minors ++ H.recursor_shape.indices
    have hleading : H.leadingArgs.length = pre.length := by
      simp only [pre, List.length_append]
      rw [H.leading_arity, hparams, hindices]
    have htype :=
      Lean4Lean.VerifyInductive.VInductDecl.NestedRecursorShape.type_eq_wrapForalls
        H.recursor_shape
    rw [htype, VExpr.instL_wrapForalls]
    have Hexists :=
      VExpr.applyForallType_wrapForalls_append_singleton_exists
        (pre.map (VExpr.instL H.recursorLevels)) H.leadingArgs
        (major.instL H.recursorLevels)
        (H.recursor_shape.result.instL H.recursorLevels) (by
          simpa using hleading)
    simpa [pre, hmajorList, List.map_append, List.append_assoc] using Hexists

end VerifyInductive

namespace VInductDecl.NestedIotaRule

/-- Data-valued form of the shape-derived final leading binder. -/
structure LeadingSplit
    {decl : VInductDecl} {block : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {rule : VDefEq}
    (H : decl.NestedIotaRule block owner ctor rule) where
  majorDomain : VExpr
  resultBody : VExpr
  eq : Lean4Lean.VerifyInductive.VExpr.applyForallType
    (H.recursor.type.instL H.recursorLevels) H.leadingArgs =
      VExpr.forallE majorDomain resultBody

/-- Canonical choice of the major/result split forced by recursor shape. -/
noncomputable def leadingSplit
    {decl : VInductDecl} {block : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {rule : VDefEq}
    (H : decl.NestedIotaRule block owner ctor rule) : H.LeadingSplit :=
  let Hexists :=
    Lean4Lean.VerifyInductive.VInductDecl.NestedIotaRule.leadingResult_exists H
  let majorDomain := Classical.choose Hexists
  let Hresult := Classical.choose_spec Hexists
  let resultBody := Classical.choose Hresult
  { majorDomain := majorDomain
    resultBody := resultBody
    eq := Classical.choose_spec Hresult }

end VInductDecl.NestedIotaRule

namespace VerifyInductive

/-- Source reinterpretation preserves the exact shape-derived major split. -/
theorem RecursorPhasesResult.GeneratedNestedIotaSource.leadingResult_exists
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {generatedOwner : Nat} {howner : generatedOwner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[generatedOwner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us generatedOwner howner i hctor
      generatedRule}
    {sourceDecl : VInductDecl} {sourceBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    (S : H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor) :
    ∃ majorDomain resultBody,
      VExpr.applyForallType
        (S.source.recursor.type.instL S.source.recursorLevels)
        S.source.leadingArgs = .forallE majorDomain resultBody :=
  Lean4Lean.VerifyInductive.VInductDecl.NestedIotaRule.leadingResult_exists
    S.source

end VerifyInductive
end Lean4Lean
