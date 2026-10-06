# Machine-checked countermodel to strengthening: status

Lean files: `Lean4Lean/Theory/Typing/Countermodel/` (`Syntax`, `Typing`, `EnvWF`,
`Derivation`, `Reduction`). All results below have axioms `[propext, Quot.sound]`;
none depends on the base sorries.

## Done

* `envCM_wf : VEnv.WF envCM`. Trace: six axioms (`C F c P leftMap rightMap`), then
  `VDecl.induct` for `I` and for `J`, with the full ordinary-compilation certificate
  (`SourceWF`, `FormationWF`, `OrdinaryShape`, `Compiles` including singleton-elimination
  admissibility, `CompiledInductive`, `VInductBlock.WF`). The recursor and iota rule are
  the signature generator's own output (`FamSpec.recursors_eq`, `FamSpec.equations_eq`
  hold by `rfl`). The abstract `.elim` registration cannot replace this:
  `CaseSchema.Permission` requires `target ≈ 0` for a `Prop` family, so it gives no
  large elimination.
* `larger_defeq : envCM.IsDefEq 0 ctxL (SI.liftN 1 0) (SJ.liftN 1 0) (.sort 1)`, with
  `ctx_lift : Ctx.LiftN 1 0 ctxS ctxL` and `ctxL_wf : OnCtx ctxL (envCM.IsType 0)`.
* `strengthening_fails_of_separated (hsep : ¬ envCM.IsDefEqU 0 ctxS SI SJ) :
  ∃ env, VEnv.WF env ∧ ¬ env.Strengthening`.

## Open: the separating model (`hsep`)

The planned Hofmann–Streicher model cannot be built in Lean. This is a set-theoretic
obstruction, not a matter of size.

* Soundness must cover derivations at every closed level, since `sortDF` types
  `Sort n` for every `n` at `U = 0`. So the model needs `⟦Sort 1⟧ ∈ ⟦Sort 2⟧ ∈ ⋯`, all
  in one Lean universe, because `⟦·⟧` is a single function.
* Context variables range over all objects of their semantic types. With
  full-section Π, `⟦Sort (k+2)⟧` must therefore be closed under Π over arbitrary families
  `A → ⟦Sort (k+2)⟧` with `A ∈ ⟦Sort (k+2)⟧`. Since `⟦Sort 1⟧` is infinite (it contains
  every finite groupoid), the least such collection is indexed by a regular strong limit,
  i.e. an inaccessible. An ω-chain of such universes inside a fixed `Type m` is not
  provable in Lean, whose consistency strength gives only `m` inaccessibles below
  `Type m`.
* Lean has no induction-recursion, and the indexed-family encoding of a code universe
  raises the Lean universe by one at every object level.
* This is independent of groupoids: a set model with full sections has the same problem.
  Groupoids are still needed, because a transport-free model fails. The motive
  `fun n v w h => I n (I.rec (fun .. => F n) (fun v _ => v) n v w h) w` is true at the
  constructor point `(c,0,0)` and false at `(c,2,2)` unless `rec` transports along the
  `Z/3` action.

Viable replacements. Both are research-scale.

1. A realizability-style groupoid model. Objects (in particular Π-objects and universe
   codes) are closures over syntax with a big-step evaluation relation, morphisms are
   Lean data, and universes are level-stratified inductive decoding relations. The
   motive's transport needs the morphism action of arbitrary terms, i.e. a second,
   morphism-level evaluation.
2. A Hofmann–Streicher model whose Π-objects and families into universes are restricted
   to hereditarily bounded (majorizable) sections. Carriers live in a cumulative
   rank-indexed hierarchy of small types, with canonical encodings so that type equality
   stays strict.
