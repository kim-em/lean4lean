# Phase 1a notes: a sound shape model for the full calculus

Branch `agent/verify-inductives-headinv`. Standing goal: `docs/inductives/GOAL.md`.
Background and the obstruction for the injectivity half: `docs/inductives/PHASE1_SPIKE.md`.
This file records the design of Phase 1a and every decision taken under it, with its
rationale. It is updated as the work proceeds.

## 0. Scope

Phase 1a delivers the *separation* half of `VEnv.HeadInversion` (`sort_sort`,
`sort_forallE`, `sort_rigid`, `forallE_rigid`, and the `c = c'` / `ls ≈ ls'` conjuncts of
`rigid_rigid`) for every `VEnv.WF` environment, from a model that is sound for every rule
of `VEnv.IsDefEq` (Theory/Typing/Basic.lean). The remaining *injectivity* half becomes the
strictly smaller conjecture `VEnv.WF.headInjectivity`.

## 1. Decisions

D1 (Experimental port). `NormalEq.lean`, `ParallelReduction.lean`, `Stratified.lean`,
`StratifiedUntyped.lean` were ported to this branch's `VExpr` rather than deleted (commits
3284ffc4..5e455f59). Two theorems of `ParallelReduction.lean` that are false once iota or
structure eta can fire (`VEnv.IsDefEq.toTyping`, `VEnv.IsDefEqU.church_rosser`) were restated
with the hypothesis `VEnv.NoInductiveRules` (no eliminators, no projections); the general
statement is `VEnv.IsDefEq.church_rosser` in `Theory/Typing/FullChurchRosser.lean`. These two
files already carried "TODO: remove, this is now part of ChurchRosser.lean".

D2 (the `.num b o` encoding in `Experimental/SExpr.lean`). Kept. The new model is built
directly on `VExpr` (D3), so the prototype's `SExpr` never needs to distinguish `elim` or
`proj`; `SExpr` has no such constructors, and the encoding only classifies `Pattern.elim`
heads in the prototype's `Pattern.WF`.

D3 (model over `VExpr`, not over `SExpr`). The model is a new development under
`Lean4Lean/Theory/Typing/ShapeModel/`, over `VExpr` and `VEnv.IsDefEq` themselves. It reuses
Carneiro's shape domain (`Experimental/ShapeLogRel.lean`, lines 1-3280) with the changes of
section 2, and re-proves interpretation and soundness for the real calculus. Rationale: the
prototype's calculus (`SExpr.IsDefEq`) lacks eliminators, projections, structure eta,
unit-like, level equivalence, and its `const` typing goes through `CtorBundle`; translating
`VEnv.IsDefEq` into it would need all of these anyway, plus a translation proof. Living under
`Theory/` lets `HeadInversion.lean` import it; it imports only the uniqueness-free base
(no `UniqueTyping`, `Injectivity`, `ChurchRosser`, `FullReduction`, `HeadReduction`).

D4 (explicit hypotheses in the `SExpr` prototype). Under the standing rule (no axioms beyond
`Verify/Axioms.lean`, no hidden conjectures), the adequacy path of
`Experimental/{SExpr,ShapeLogRel,ShapeLogRelAdequacy,UniqueTyping}.lean` now has no axiom and
no `sorry`; `#print axioms LR.adequacy` gives `propext`, `Classical.choice`, `Quot.sound`.
Every unproved obligation is a named hypothesis instead:
* The global axiom `Params.extra_pat` is the field of the `Prop`-valued class
  `Params.PatternRegistry` (same content). It cannot be a field of `Params` itself because it
  mentions `IsDefEq`, which is defined from `Params`.
* The `const` case of `LR.adequacy` is the explicit hypothesis `LR.ConstAdequate Γ₀` (the case
  itself, as a `Prop`). It is false for checked patterns (`PHASE1_SPIKE.md`, section 3), and we
  expect it to fail also for unchecked patterns that match a constructor argument, because the
  relation at an `indTy` shape is `True`.
* `IsDefEq.strong` and the two-sided `IsDefEq.subst` were false as stated: they had no
  context well-formedness hypothesis, and `Params` does not relate `env` to the `SExpr` typing
  judgment. They now take `⊢ Γ` and the assumption class `Params.TypedEnv` (constant types,
  constructor telescopes as `CtorBundle`s, and stored rules are strongly typed in the empty
  context); `Params.ctor_ty` follows from it. Adequacy is proved for strong derivations
  (`LR.adequacy'`, without `TypedEnv`) and, through `IsDefEq.strong`, for `IsDefEq`
  derivations; the corollaries and `UniqueTyping` take `⊢ Γ`, `TypedEnv` and
  `∀ Γ, LR.ConstAdequate Γ`.
* `Ctx.SubstEq`'s base case is now an arbitrary weakening (the identity base made
  `Ctx.SubstEq.lift` false), and its binder types carry strong derivations, from which the
  two-sided substitution `IsDefEqStrong.substEq` follows without assumptions.
The seven `SExpr.lean` declarations still unproved are off the adequacy path; each docstring
says why (strengthening, registry soundness, confluence, or validity in a judgment without a
context hypothesis). The false and unused `InferType.whRed` was removed, with the
counterexample in a comment.

D5 (declared field count in constructor typing). Shape typing of a constructor shape
`ctor c fs` at a rigid family requires `fs.length = nfields c`, the declared number of fields
(`ShapeParams.nfields`, from `SemSig.nfields`; commit d90f7789, by the M3 author). Without it a
constructor shape with fewer fields than the constructor is typed at its structure and
approximates a variable of that type but not the variable's structure eta expansion, so
`structEta` is unsound in the model.

D6 (rule matching independent of the parameter/field split). Two facts about real
environments rule out a single agreed split of a constructor's arguments into parameters and
fields:
* the same constants can be registered twice with different splits: a structure registration
  (`inductProjections`) and an eliminator schema (`inductEliminators`) over the same constructor,
  e.g. `S.mk : (α : Type) → α → S α` as a structure with one parameter and one field, and as the
  constructor of an inductive with no parameters, one index and two fields
  (counterexample in `Theory/Typing/ShapeModel/EnvTables.lean`, M4a work on branch
  `agent/verify-inductives-headinv-m4`);
* a native rule's field count is the normalized signature's, tied to the constructor's syntactic
  arity only by a definitional equality in the header environment
  (`Theory/Typing/ShapeModel/EnvHeaderArity.lean`, same branch).
So the model no longer assumes that a rule's major has as many fields as the constructor stores.
`S.ctor c = some ⟨I, np, nf⟩` means that constructor shapes of `c` store the last `nf` arguments
of a saturated application with `np + nf` arguments; `np` is the structure's parameter count for
a registered structure constructor (`ctor'` collapse and projections work as before) and `0`
otherwise (the shape stores every argument). In mode AB the stored fields have the stored count
(`fs.length = S.nfields mj.ctor`) and are aligned with the rule's `k` fields at the end: rule
field `i` is stored field `nf - k + i` when that is an index. Every other rule field, and every
field in mode C, is read from an index argument through the new `Rule.fieldIndex` (one entry per
rule field, `some j` = the argument at position `j` before the major), and is bottom if `none`.
A binder that is not a rule field is read from its first literal occurrence among the arguments,
as before. `SemSig.Coherent` and the statements of `Sound.lean` are unchanged.

## 2. The domain (ShapeModel/Domain.lean, ShapeModel/ShapeTyping.lean)

Carneiro's depth-indexed finite shapes, with:

* `sort (l : SLvl)`, `SLvl := List Nat → Nat` (the evaluation of a level). Equal sort shapes
  give `≈` levels (`VLevel.equiv_def'`). Shape typing only looks at whether a level is
  identically zero (`isZero l`); a sort is a proposition sort iff its level is identically 0.
* `indTy` is replaced by `rigid (c : Name) (ls : List SLvl) (args : List S)
  (cts : List (Name × S))`: a rigid type former (inductive family, axiom, opaque, rule-free
  recursor), its evaluated universe levels, argument shapes, and, for an inductive family, one
  entry per constructor holding an approximation of the constructor's type instantiated at
  the parameters (a Pi telescope over the fields). Order, compatibility and join are
  componentwise (same name, same levels, same constructor names in the same order).
* `ctor (c : Name) (fields : List S)`: constructor shapes store the *fields only* (not the
  parameters); "fields" are the last `nfields` arguments of the split chosen by the signature
  (D6). `ctor'` collapses a structure constructor (`isStruct c`) with all-bot fields
  to `bot` (validates `structEta`, `unitLike`).
* Shape typing is parametrised by `class ShapeParams` (`isStruct : Name → Bool`,
  `famProp : Name → List SLvl → Bool`, "this rigid former is a proposition at these levels";
  `true` for non-families):
  * `rigid c ls as cts : sort r` iff `(isZero r → famProp c ls)` and every telescope in
    `cts` is a type;
  * `ctor c fs : rigid I ls as cts` iff `¬ famProp I ls`, `(c, T) ∈ cts`, and `Fits fs T`:
    the fields are typed along the telescope `T` (first field at its domain, the rest along
    the codomain applied to the first field; depth mismatches handled by `lift`/`plift`).
  Precise field typing is needed: projections have no typing filter of their own, and a
  valuation with an ill-typed field would break proof irrelevance and eta under binders.
  Element typing ignores the constructor's result indices (they are not needed for
  soundness: recursor results are filtered by the recursor's own type, see section 3).

## 3. Interpretation (ShapeModel/Interp.lean)

`Interp ρ m e` ("`m` approximates `e` under valuation `ρ`"), downward closed, mutually
inductive with the spine machine `Const h ls rargs m` for heads `h = const c | elim b o`.
As in the prototype, a head's whole table is filtered by its type: the `const`/`elim` clauses
require the produced table to be typed at an approximation of the head's type
(`ci.type.instL ls`, `schema.genericType owner`). Clauses of `Const`:

* `bot`; `lam` (tables over further arguments);
* `ctor`: constructor `c` with `nparams + nfields` arguments gives `ctor' c fields`;
* `rigid`: a constant with no rule and not a constructor gives
  `rigid c (ls.map eval) args cts`, `cts` from the constructor types if `c` is a family;
* `rule`: one generic clause for every computation rule (definition unfoldings, native
  iota rules after restoration, the quotient rule, abstract eliminators' generic equations).
  A rule is a lambda-wrapped equation whose left body is the head applied to arguments that
  are bound variables (parameters, motives, minors), arbitrary terms (indices), and one
  constructor application (the major) whose trailing arguments are distinct field variables.
  Matching reads the bound variables from the argument shapes and:
  * mode AB (major's family not a proposition at the levels): the major shape is
    `ctor' c fs`; this includes the bottom major of a structure (`fs` all bottom), which is
    what `structEta` forces; the rule's fields are aligned with `fs` at the end, and those
    not stored are read through `Rule.fieldIndex` (D6);
  * mode C (major's family a proposition with one constructor): the major is ignored (proof
    irrelevance makes it invisible); each field is read from the index argument given by
    `Rule.fieldIndex`, and is bottom if there is none. This is read-through
    (PHASE1_SPIKE.md section 3.1); the recursor's typing filter keeps it typed.
* `proj S i e`: the `i`-th field of a `ctor` shape of `S`'s constructor; bottom otherwise.

## 4. Soundness (ShapeModel/Sound*.lean)

For every strong derivation (`IsDefEqStrong`, Theory/Typing/Strong.lean), both sides have
the same approximations under every valuation fitting the context, and every approximation
is below one typed at an approximation of the type. The `extra` and `elimIota` cases use rule
validity (`RuleValid`). Rule validity of a mode-C rule at a large elimination needs that the
fields not recoverable from the indices are proofs *semantically*; that comes from the
formation evidence of singleton elimination, a derivation in an earlier environment, so rule
validity and soundness are proved together by induction along the `VEnv.WF'` chain
(soundness for derivations in the environments before the rule's declaration).

## 5. Status

(updated as the work proceeds)

* Head classification and separation (`ShapeModel/Head.lean`): the shape model at the base
  valuation is a `HeadModel` (`headModel_of_shapeModel`, interface moved from the spike to
  `Theory/Typing/HeadSeparationModel.lean`), giving `headSeparation_of_shapeModel` from
  `SemSig.Coherent`, `SemSig.EnvFacts`, `SemSig.HeadFacts`, `ExtraValid`, `ElimValid`. The
  `sorry` of `VEnv.WF.headSeparation` remains until the signature of a real environment is built.
