# Feasibility: machine-checked refutation of `IsDefEqU.weakN_iff`

Worktree: /home/kim/worktrees/lean4lean/lean4lean-base (branch `agent/verify-inductives-base`,
merged with `agent/verify-inductives` at de0ec37; merge commit 070911e, no other commits).
Status: study only. Scope was cut by the coordinator (top-level theorem may assume canonical
`Eq`), so no refutation was implemented.

## Verdict

* `IsDefEqU.weakN_iff` as stated (hypothesis only `VEnv.WF env`): I judge it FALSE. The
  STRENGTHENING.md countermodel is mathematically sound as far as I checked it.
  A machine-checked refutation is feasible in principle, but it does not fit a 4k-line budget.
  Realistic size: 10k to 18k lines (breakdown below).
* With canonical `Eq` in the environment: plausibly TRUE (argument below), but unproved, and
  a proof would need the same normalization/confluence machinery whose absence is the reason
  `weakN_iff` is currently a `sorry`.

## (a) Obtaining `VEnv.WF env`

* `VEnv.WF'` (Theory/Typing/Env.lean) separates installation of constants from registration of
  eliminators. `inductEliminators` only needs (i) the block's type/constructor constants to be
  present with the right `VConstant`s, (ii) `env.defeqs = base.defeqs`, (iii) `schema.Certified
  base source block`, (iv) `ProjNamesRegistered`, (v) `Fresh`. In principle, then, `I`, `I.mk`,
  `J`, `J.mk` could be added as plain `VDecl.axiom`s, which avoids `VDecl.induct`/`AddInduct`.
  Only `Certified` remains as a hard obligation. The projection table (`inductProjections`) is
  optional. Leaving it out removes the `projDF`/`projIota` cases from the model.
* `Certified` unfolds to `CompilationData` (Inductive/Compilation.lean:153). This has about 25
  fields: `SourceWF` for both the source and the expanded declaration, `SourceParameterWF`,
  `FormationWF`, `s.Models env expanded`, `g.Admissible`, `RecursiveTypesWF`,
  `FamilyTypesWF`, restoration correspondence (`RestoresFamily`), plus `restoredRecursors` and
  `restoredEquations` equal to `block.recursors`/`block.rules`, and name freshness. Most fields
  are typing derivations built from `IsDefEq` constructors over a 6-constant base, together with
  computations on concrete data. These are axiom-free by construction if done by hand or by
  `decide`/`rfl` where the functions are computable. Estimate: 1.5k to 3k lines, with risk in
  the `Models`/`Admissible`/restoration fields. These are large definitions that I did not fully
  read.
* Using `Lean4Lean.addDecl` plus `addDecl.WF` is ruled out: it lies in the cone of the base
  sorries. I did not audit individual `Verify/Environment.lean` lemmas for axiom-cleanliness.
* Fallback: drop `VEnv.WF` and refute strengthening for a hand-built `VEnv` record with the
  eliminator entry inserted directly. This saves the certificate but not the model. The model is
  the dominant cost, and such an environment says nothing about `weakN_iff`, whose hypothesis
  is `WF`.

## (b) The semantic model: the real obstacle

* A set-theoretic model, or any model with proof-irrelevant identity on `C` (setoid model,
  presheaf topos, G-sets), cannot separate `SI` and `SJ`. In any such model the recursor at
  the internally definable "image" motive forces `I c v w → P v`. The separation needs a
  non-trivial automorphism of the index type, so the model has to be (at least) the
  Hofmann-Streicher groupoid model.
* Soundness must cover EVERY rule of `VEnv.IsDefEq`, because a derivation in the small context
  may pass through arbitrary intermediate terms, sorts and motives. No fragment restriction is
  available without a subject/fragment lemma, and that is itself a normalization-type result.
  The obligations are:
  - Universe hierarchy: closed levels `Sort n` for all `n`, since `U = 0` still allows any
    closed level. This needs a Nat-indexed, inductive-recursive-style tower of groupoid codes
    in one Lean universe, plus `instL`, `VLevel` equivalence and `imax`.
  - Impredicative `Prop` as {empty, terminal}. Pi into `Prop` from any universe.
  - Dependent Pi over groupoids, with functorial sections: lam/app/beta/eta, `defeqDF`.
  - A partial interpretation of de Bruijn `VExpr`, with weakening and substitution lemmas for
    `lift`/`inst`/`instL`. This is the classic Streicher partial-interpretation work, and it is
    the bulk of the effort.
  - `elimDF`/`elimIota`: interpret the `.elim block owner levels` former for the concrete
    schema. Check the concrete `genericType`/`genericEquations` output against the all-motives
    construction `rec(M,s)(x) = M(g_x)(s(o(x)))`. The coherence proof (functoriality in `x`,
    naturality in motive and branch) is the groupoid-specific part.
  - `proofIrrel`. `projDF`/`projIota`/`structEta`/`unitLike` are vacuous if no projections are
    registered. `extra` covers only delta rules: none here, since the base is all axioms.
  Estimate: 8k to 15k lines. Groupoid-valued dependent families in Lean need setoid-style
  hom-sets and functoriality proofs everywhere, and Lean's metatheory has UIP, so the groupoid
  structure must be explicit data.
* Cheaper alternatives I considered and rejected:
  - Erasure or untyped interpretation: proofs erase to a single constant. Then iota fires on
    the index syntax and the model identifies `SI` and `SJ` even without `q`.
  - Syntactic non-derivability: needs confluence/normalization with typed proof irrelevance.
    This is not available, and it is exactly what the `weakN_iff` sorry stands in for.
  - Quotients instead of inductives: `QuotReady` requires `Eq`, and `Quot.ind` extracts the
    witness.
  - Projections instead of a recursor (single family `I`, endpoints `proj I 0 p` and `v`): the
    `projDF` side condition `resultLevel.IsNeverZero ∨ fieldLevel ≈ 0` blocks projecting a data
    field out of a `Prop` family, so no shortcut there.
  - Delta/beta/eta/proof-irrelevance only (axioms and definitions, no inductives): no new
    conversions arise from an extra hypothesis without an eliminator that computes on a
    constructor. I expect strengthening to hold in that fragment, so it yields no
    counterexample.

## Judgement with canonical `Eq`

With `Eq` (and its K-like recursor), the separating point disappears. STRENGTHENING.md (last
section) records the checked term `extract : I c v (leftMap v) → P v`. More generally, for
every large-eliminating (subsingleton-eliminating) Prop family, every field is either a Prop,
recoverable by the recursor into a Prop motive cast along `Eq`, or occurs as an index,
recoverable via `Eq` transport. So in the small context any neutral proof `h : T` is already
provably (by proof irrelevance) equal to a constructor application built from `h` alone. The
only way a removed hypothesis `q` creates new conversions is through proof irrelevance at a
Prop `T` followed by iota/K on a constructor form. With `Eq`, that constructor form is
reconstructible without `q`. I know of no other mechanism:
* empty families have no iota;
* `structEta`/`unitLike` require both sides typed at the same type;
* `Acc` follows the same singleton pattern and is covered by the same reconstruction.

So I consider strengthening plausibly true for environments containing canonical `Eq`. I have
no counterexample, and the obvious candidates (`Acc`, `Eq`-indexed casts, `False`) all fail.
A proof would still need a normalization or confluence argument for typed proof irrelevance
with iota/K, so it is not cheap either. The repo's ChurchRosser files may be the starting point.
