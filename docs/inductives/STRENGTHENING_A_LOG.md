# Direction A log: transitivity of pilot conversion

Branch `agent/verify-inductives-strengthening3-A`. Companion to
`STRENGTHENING_ATTEMPT_2026-10-09b.md`, section 3.A. Library files:
`Lean4Lean/Theory/Typing/Strengthening/ProofAware.lean` (step 1, Astra round 7(A) integrated),
`Lean4Lean/Theory/Typing/Strengthening/PilotTrans.lean` (step 2, the proved parts). Everything
with `sorry` lives in `scratch/` and is not committed.

## 1. Decisions

* **Reification.** `Cert` is `Prop`-valued (`proof_rank_constant`, Astra round 8), so a rank
  on certificates needs either a `Type`-valued copy or size indices. Decision: the rank is
  **not** a function of certificates in the first place. The obligations below are stated over
  the `Prop`-valued `Cert` with *declaratively typed endpoints*, and the recursion is organised
  on data visible in the statements: the terms, their declarative types and the context. A
  reified `DCert` is introduced only if a rank on derivations is found that the obligations
  need (section 4); until then every lemma is proved by structural induction on one of its
  input certificates plus the declarative theory (`henv.WF`, unique typing, inversion), which
  is sound to use because `Cert.sound` connects the two worlds.
* **Side information.** Every obligation carries `OnCtx Γ (env.IsType U)` and declarative
  typings `HasType Γ a A` of its endpoints. These are free (soundness, subject reduction in
  the declarative theory) and let impossible cases be refuted by declarative inversion (a `Π`
  is never a proof, a sort never reduces to a `Π`) without a certificate.
* **Stored equations.** `step_extra` fires on arbitrary `env.defeqs`; the shape lemmas assume
  `ConstHeadedEquations env` (every stored left side is `mkApps (const c ls) args`), which
  holds for definitional unfoldings and recursor and quotient rules.

## 2. Obligations (pilot, `Pilot.lean`) and the recursive-call relation

Judgements: `T` = `Cert .ty`, `S` = `.step`, `R` = `.red`, `N` = `.norm`, `C` = `.conv`.
Nesting: `T` nests `R` (exposure) and `C` (argument guard of `ty_app`); `S` nests `T`, `R`
(`step_eta` only); `N` nests `C` (`norm_lam`, `norm_forallE` domains; `norm_eta*` domains;
`norm_proofIrrel` alignment), `T`, `R`; `C` nests `R`, `N`.

Target: **O1** `C.trans : C a b → C b c → C a c` (typed endpoints). Proved from O2, O3, O4 by
the strip lemma `CConv.trans_of` (`PilotTrans.lean`). The remaining obligations:

| # | statement | calls |
|---|---|---|
| O2 `RedConfluent` | `R a b → R a c → ∃ d d', R b d ∧ R c d' ∧ N d d'` | S.diamond (modulo `N`), O3 to tile |
| O3 `NormTransport(L)` | `N a b → R b b' → ∃ a', R a a' ∧ N a' b'` | O8 (N.subst at a beta step under `norm_app`), O6 (the body of `norm_lam` lives under the left domain, the step under the right), O9 (eta and proof-irrelevance leaves against a step of their subject), O1 at types |
| O4 `NormTrans` | `N a b → N b c → N a c` | O9 (`proofIrrel` against a congruence), O6 (`norm_lam` bodies), O1 at types (`C p p'`, `C p' p''` → `C p p''`) |
| O5 `N.symm`, `C.symm` | | O6 (`norm_lam` compares bodies under the left domain) |
| O6 `CtxTransport` | `C Γ A A' → J (A::Γ) .. → J (A'::Γ) ..` for every kind `J` | `ty_bvar 0` returns `A'↑` instead of `A↑`; every consumer of that type (`ty_app` exposure, `norm_proofIrrel`) must be re-established: O1 at types with `C A↑ A'↑` |
| O7 `T.subst` | `T (A::Γ) e F → T Γ a A' → C A' A → ∃ F', T Γ e[a] F' ∧ C F' F[a]` | the variable case returns `C A' A`; `ty_app` must compose `C F' F[a]` with the exposure `R F[a] (Π ..)`: O2 on `F'`/`F[a]` and O3, then O10; the new argument guard `C A''[a] B` is O1 on outputs |
| O8 `S/R/N/C.subst` | substitution for the other kinds, heterogeneous in the substituted term for `N` (`N m m' → N x x' → N m[x] m'[x']`) | O7 at every `T` leaf of `N`; `step_eta` under substitution re-exposes (O7, O2, O10) and returns a `λ` at a different domain, so `S.subst` is only `∃ c, R b[a] c ∧ N c b'[a']` |
| O9 `T.sr`, `T.coh`, `T.uniq` | `S e e' → T e F → ∃ F', T e' F' ∧ C F F'`; `N e e' → T e F → T e' F' → C F F'`; `T e F → T e F' → C F F'` | the `app` case needs `C (B[a]) (B'[a'])` from `C (Π A B) (Π A' B')` (O10) and `N a a'` (O8); `T.uniq` needs O2 on two exposures of the same type |
| O10 `C.piInj` | `C (Π A B) (Π A' B') → C A A' ∧ (C (A::Γ) B B' up to O6)` | O2 (join the two reductions of each side: `CRed.forallE_inv` gives the shape), O3, O6 |
| O11 `N.refl`, `C.refl` | proved for certified-typed terms (`Cert.norm_refl_of_ty`) | none |
| O12 `CComplete` | `IsDefEq → C`, `HasType → ∃ T, T` | O1 (`trans`), O7 (`beta`, `instDF`), O5 (`symm`), O6 (`defeqDF` at a binder), O9 (`defeqDF` for typing) |

Every arrow "O1 at types" is a transitivity call whose arguments are *outputs* of the current
lemma (an exposure of a substituted type, a re-synthesised domain, an alignment composed with
a reduct comparison). The designer's four places (section 2 of the attempt document) appear
as: `ty_app` guard under O7; eta against a reduction of its subject in O3/O9; proof-irrelevance
leaves under O3/O8 (`S ~ p[n] ~ p'[n] ~ p'[n'] ~ S'`); the K/alignment guard is absent in the
pilot.

Proved so far at zero `sorry` (`PilotTrans.lean`): the eta-free fragment of S.diamond and
confluence (`PStep.diamond`, `PRed.confluent`, with `PStep.inst` as the substitution lemma for
eta-free steps), the shape lemmas `CRed.sort_inv`, `CRed.forallE_inv`, `CRed.lam_inv`,
`CRed.trans`, O11, `Cancel.of_cComplete`, and the strip lemma `CConv.trans_of`.

## 3. Outcome: obstruction (ii), with the proved parts in the library

### 3.1 The attempt and where it stops

The strip lemma `CConv.trans_of` reduces O1 to O2, O3, O4. O2 is proved exactly for the
eta-free steps (`PStep.diamond`, `PRed.confluent`); with `step_eta` every eta/beta and
eta/congruence overlap re-synthesises the expanded domain (O9), so O2 for the full pilot is
confluence *modulo* `N` and already needs O3 to tile. O3 (transport of `N` along a certified
reduction) was written out case by case. Its beta case under `norm_app` with `norm_lam` on the
left is:

```
N (app (lam A m) u) (app (lam A' m') u')   along   app (lam A' m') u' → m''[u'']
```

The induction hypotheses transport `N m m'` along `m' → m''` and `N u u'` along `u' → u''`,
giving `N m₁ m''` and `N u₁ u''`; the result `N (m₁[u₁]) (m''[u''])` is the heterogeneous
substitution `N.subst` of the second into the first. `N.subst` is exact when the two
substituends have the *same exact* synthesised type (`Cert.instN` is the homogeneous case);
in general `u₁ : X` with only a guard `C X A`, and at every `T` leaf of `N m₁ m''`
(`norm_proofIrrel`, `norm_eta*`) it needs `T.subst` with a guard, whose `ty_app` case must
expose the substituted function type through the guard (`C F' F[u]` composed with
`R F[u] (Π ..)`): O2 and O3 again, and then O1 on the composed argument guard. So O3,
`N.subst`, `T.subst` and O1 form one mutual block, and a rank must decrease along the call
O3 → `N.subst`.

### 3.2 The failing call, formally (`PilotRank.lean`)

Rank used: the total size of the input certificates, made meaningful by the size-indexed copy
`CertN` (`Cert.toN`, `CertN.erase`). The instance is `Duplication`: `u = (λ X:Prop. n) w`,
`u' = (λ X:Prop. n) w'` where `n` mentions `X` five times and `w`, `w'` are closed
irreducible propositions whose comparison `C w w'` costs at least 21 because it contains a
comparison of two `Π`-towers of sorts differing by equivalent level expressions. Checked:

* `transport_output_exceeds_inputs`: `N u u'` has size 53, the step `u' → Π w'. Π w'. Π w'.
  Π w'. w'` has size 21, both endpoints are typed, and *every* certificate `N u₁ (Π w' ...)`,
  for every `u₁`, has size at least 98 (`norm_tower_ge`, a lower bound by cases on the right
  side only: at every level the certificate is a `norm_forallE` with a guard against `w'` or a
  `norm_proofIrrel` whose typing of the `Π` is at least as large; eta is excluded because a
  `Π` synthesises a sort).
* `substitution_call_not_decreasing`: wrapping once more, `a = (λ X. X) u`, `b = (λ X. X) u'`
  (sizes 60 and 23), the `N.subst` call of the beta case receives the body certificate (size 1)
  and the transported argument certificate (at least 98): total at least 99 > 83.
* `no_monotone_size_rank`: hence no rank that is a monotone function of the total input size
  decreases on this call.

The lower bound is independent of the reduct chosen on the left, so it does not depend on
how the transport is organised; it is the duplication of the argument comparison by
substitution, which Astra's `no_additive_size_decrease` showed for typing certificates of a
contractum and which here lands on the transport obligation itself.

### 3.3 Reorganisations tried, and why none removes the call

1. **Chains (zigzags of joins) as guards.** Every "O1 at types" call becomes concatenation and
   `T.subst`, `N.subst`, O3 are structural. But a chain guard admits arbitrary intermediates,
   and the exposure of a function type by a chain (instead of by reduction) makes the
   synthesised type of an application depend on a free choice of `Π`; both break `Cert.descend`
   (a `q`-dependent intermediate or domain is reachable by one beta step from a lift). The
   intermediates produced by the strip lemma *are* lifts, but that is a property of the
   proof, not of the calculus, so it would have to be a reified `Supported` predicate on
   derivations, with completeness producing supported derivations: the same recursion with a
   bookkeeping layer added.
2. **Dropping `step_eta`.** Steps become untyped (`PStep`), O2 is exact and `R.subst` exact.
   The eta leaves of `N` still expose the synthesised type of their subject by reduction, so
   `N.subst` at an eta leaf has the same exposure-through-a-guard problem as `T.subst`.
3. **Typing premises on `norm_app`** (as `NormalEqN.appDF` has them). Supplies the certified
   typings `N.subst` needs for its substituends, but not the exact types: the guard remains.
4. **Exactly typed substituends only.** `Cert.instN` is proved; it is the inhabited-binder
   case, and the uninhabited case is exactly the guarded one.
5. **Ranks other than size.** Guard nesting depth: `N.subst` inserts the argument comparison
   inside the guards of the body (`C (G x) (G' x')` with `x` the substituted variable), so the
   depth of the output is the sum of the depths of the inputs (same example, with a
   `norm_lam` guard inside `w`). Universe of the compared type: `no_layer_universe_rank`.
   Term size or context position: the recursion enters the types of subterms, which are
   context entries or substitution instances of them, unbounded in the terms.

No universal pair (a statement whose required call is the same statement) exists in a
normalising fragment, so the obstruction is to syntactic ranks, not to the truth of O1..O4.

## 4. Log

* Step 1 (015c7811): `ProofAware.lean`, all of Astra's round 7(A) at zero sorry.
* Step 2a (b6b37b40): `PilotTrans.lean` first increment; obligations list above.
* Step 2b (391a07e6): `Cert.instN`, exact substitution for every kind.
* Step 2c: `PilotRank.lean`, the size-indexed calculus and the duplication obstruction
  (section 3); outcome (ii) recorded.
