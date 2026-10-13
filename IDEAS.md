# Strengthening idea ledger

Scope: `GOAL.md`; canonical `Eq`, every well-formed environment, unchanged executable.
No proof, counterexample, or strictly smaller sufficient obligation has been obtained yet.
An open entry is not a rejection. Work continues while an unrefuted route remains.

| Idea | Test and current verdict |
| --- | --- |
| Finite developments with explicit redex marks | **Active.** Develop the original marks, including their copies, without marking created redexes. Then test a marking invariant on the actual comparison join. Finite developments alone do not justify repeated marking until beta-normality. |
| Standardisation of just the obstructing comparisons | **Open.** Needs a rule for newly created obstructing pairs, not normalization of all endpoints. No concrete refutation yet. |
| Descend normal equality up to parallel substitutions | **Open.** Route A log §5.2 identifies the exact eta/proofness bridge to maintain. Existing open typings do not survive inverse exposure after substitution. |
| Strong derivation induction, including typing certificates | **Open with constraints.** Prior `Obstructions.lean`, `PilotRank.lean`, and direction A log refute source-only substitution bounds, size-monotone transport ranks, and global proof/type phase ranks. They do not refute every derivation order. |
| Algorithmic cache certificates | **Open.** The executable's proof comparison infers endpoint types (`TypeChecker.lean:isDefEqProofIrrel`); the equivalence manager takes transitive closure of facts inserted in larger contexts (`Verify/EquivManager.lean:eqv_uniq`). A support theorem must cover those inferred types and intermediate nodes; endpoint free-variable lookup independence alone is insufficient. |
| Use canonical Eq extraction directly | **Open.** `EqTyping.lean` provides casts and `SingletonExtraction/` extracts fields. Old counterexample candidates fail because the major already supplies a field inhabitant. Need an invariant for arbitrary conversion derivations, beyond one singleton step. |
| Existing observation model | **Rejected as a reflecting model.** Route B's `extension_not_typedReflection` separates two opaque constants that every observation identifies, even at a common type. |
| Set-valued semantics in Carneiro's thesis | **Insufficient by itself.** The source `soundness.tex` proves interpretation weakening and soundness, not reflection of definitional equality. Equality over valuations of an empty context extension is vacuous. This does not reject a new syntactic/realisability model. |
| Syntactic Kripke/realisability model | **Open.** Must preserve opaque names and account for empty domains without requiring an inhabitant in the old context; using definitional-equivalence classes simply restates reflection. |
| Beta-normal or first-order proposition fragment | **Open.** Route A proves strict-normal-comparison descent already. A useful new fragment must come with a general-case reduction, not merely another equivalent front. |
| Counterexample using recursive definitions | **Open.** `mutualDef` permits looping definitions. No new canonical-Eq counterexample; a loop by itself does not produce a new equation under a binder. |
| Add a fresh global inhabitant, substitute, then remove it | **Open but no simplification established.** Removal of an opaque axiom from conversion may be the same support problem as removing a variable; a self-looping definition adds no extra equation beyond reflexivity. |
| Erase lambda annotations, then reflect at a common type | **Open.** Could address the matched-lambda case, but needs typed coherence for applications and proof irrelevance. Untyped proof erasure is already refuted by the previous study. |

Evidence read: `OPEN_PROOFS.md`; fetched route A/B logs and their front/descent statements;
the previous calculus's tagged `Obstructions.lean`, `Kripke.lean`, attempt reports and
direction A/B2/C/F logs; Astra round 7 summaries and earlier review material. The old
checkout named in the goal lacks the cited docs, so the pinned tag is used instead.

Source audit: route A's `TypingFront.lean` proves `PropFront ↔ TypedFront`, but explicitly
does not reproduce the converse `TypedFront → Cancel`. `StrictJoinRepair → TypedFront`
is checked; its converse is not proved in that file. Do not promote log prose about
equivalence or normalization to a checked theorem.

Thesis source: https://github.com/digama0/lean-type-theory/blob/master/soundness.tex
(read alongside `typesys.tex`, 2026-10-13). Its set model also targets a different
declaration discipline from arbitrary looping `VDecl.WF.mutualDef` declarations.
