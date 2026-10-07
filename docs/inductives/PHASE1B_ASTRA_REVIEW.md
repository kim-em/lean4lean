**The obstruction defeats the proposed adequacy interface, not Pi injectivity itself. I recommend a small, motive-directed cast prototype before committing to the proposed repair. None of A–D currently supplies a complete proof for this calculus.**

**1. What the spike establishes.**  
[`check_of_piAdequacy`, ReadThrough.lean:82](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Experimental/Spike/ReadThrough.lean:82) is valid conditional reasoning. Its substantive assumptions are compositional interpretation, equal denotations for indices and majors, semantic Pi shape, and `hstuck`: reaching anything other than the original term requires the check. The proof actually discards the domain-typing conclusion.

However, the comment at [ReadThrough.lean:61](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Experimental/Spike/ReadThrough.lean:61) overstates matters: semantic Pi shape implying reduction to Pi is stronger than bare Pi injectivity. It is required by **this prototype’s** [`ValTyPi2`, ShapeLogRel.lean:5388](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Experimental/ShapeLogRel.lean:5388), not by every conceivable proof of injectivity.

The connection to the prototype is convincing: its fundamental lemma quantifies over shapes ([Adequacy:106](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Experimental/ShapeLogRelAdequacy.lean:106)), and identity substitution explicitly uses the bottom valuation ([ShapeLogRel:6066](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Experimental/ShapeLogRel.lean:6066)). Thus distinct variables can have identical denotations while the transported type has a nonbottom Pi observation.

Two qualifications matter:

- `hmaj` identifies proofs of **different propositions**. Declarative proof irrelevance only identifies proofs at one proposition ([Basic:80](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Theory/Typing/Basic.lean:80)). Global erasure supplies `hmaj`; proof irrelevance alone does not.
- The spike does not construct the full model, instantiate the witness in `VExpr`, or prove `hstuck` for a finished reduction. These remain obligations, albeit plausible ones for the proposed checked reduction.

The witness is well-typed: the recursor’s motive takes values in `Type 1`; its result is `Q b → Type`; application to `y` therefore gives `T : Type`. Canonical recursor types support this directly ([CanonicalEq:30](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Theory/CanonicalEq.lean:30)). I also successfully ran the source-level [KObstructionExamples.lean:21](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Experimental/Spike/KObstructionExamples.lean:21).

Reflection does not require strengthening away the auxiliary variables: specialize `Q := fun _ => α`, `R := fun _ => α`, `y := b`, `y' := a`. The dependent version additionally exposes why unchecked deletion produces an ill-typed domain.

**2. Truth of injectivity and uniqueness.**  
The witness supplies no declarative equality between two Pi types. With variable `h : a = b`, iota does not apply directly. Proof irrelevance replaces `h` by `rfl` only after both inhabit the same proposition; the native reconstruction interface explicitly requires that typing ([NativeKReduction:48](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Theory/Typing/NativeKReduction.lean:48)). Neither function eta nor structure eta turns an arbitrary sort-typed expression into a Pi.

Accordingly, `T` is operationally stuck, and no displayed rule supplies its conversion to a Pi. The failed `rfl` tests support this, but do **not** prove declarative nonderivability: Lean’s checker is incomplete.

For the exact theory, I would retain injectivity and uniqueness as conjectures. [Lean4Lean §2.4](https://arxiv.org/html/2403.14064v2#S2.SS4) retracts the thesis proofs because their stratification incorrectly requires substitution to preserve a maximum bound rather than an additive bound. Consistency models do not by themselves recover declarative component equalities.

The newer [*Definitional Inversion, Without Normalisation*, §§3.5–3.6](https://arxiv.org/html/2607.13662v1) strengthens the evidence for the semantic strategy, but treats proof-relevant identity separately from strict propositions; it does not establish this combined K/singleton case. Locally, uniqueness still invokes the admitted head-inversion theorem ([UniqueTyping:129](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Theory/Typing/UniqueTyping.lean:129)).

**3. Comparing the repairs.**  
**B** does not work merely by declaring proof eliminators neutral. For `h : a = a`, congruence, proof irrelevance and iota equate a neutral-major eliminator with its canonical result. A relation allowing only neutral–neutral declarative equality misses that equation. Restoring checked K restores the spike’s obstruction. Kripke indexing or step indexing alone changes neither fact. A syntax-sensitive model might escape `hidx` or `hmaj`, but requires a different adequacy argument.

**C** has the same problem: the witness already lies at type level. Moreover, singleton eta requires a constructor reconstruction **at the actual indices**; it cannot manufacture that typing. Neutral reflexivity proves self-relatedness only after changing the Pi clause. Allowing a neutral alternative then leaves transitivity through neutral/canonical intermediates unresolved. The current proof crucially identifies the middle Pi reduct ([ShapeLogRel:5464](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Experimental/ShapeLogRel.lean:5464)).

**A** is promising but substantially underspecified. Its Pi rule needs component transports:

`cast f ↦ fun x => castCod x (f (castDomBack x))`.

For the witness, the uniform motive supplies `castDomBack y := h.symm ▸ y`. For arbitrary motives whose **endpoints** happen to expose Pi heads, whole-type transport does not automatically provide domain/codomain transports. OTT adds equality projections precisely for this purpose; see [CICobs §§3.2–3.3](https://pujet.fr/pdf/toplas25_cicobs.pdf). `HasCanonicalEq` supplies ordinary equality and its recursor, not those projections.

Equal-level sort casts can erase. Distinct rigid families, incompatible levels, or neutral endpoints should remain suspended; proving that no required positive observation is lost is essential. Same-family constructor casts need declaration-specific dependent field transports and index coherence. The `I` example’s [`orig` and `toOrigin`, Examples:96](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Experimental/Spike/KObstructionExamples.lean:96) demonstrate whole-motive transport without `Eq`, **not** general component decomposition. Thus “needs no canonical Eq” remains conditional on a generic construction.

**D** offers techniques, not replacements. [Abel–Öhman–Vezzosi](https://www.cse.chalmers.se/~abela/popl18.pdf) supplies a reducibility architecture for a normalizing fragment; [Gilbert et al.](https://doi.org/10.1145/3290316) deliberately changes singleton elimination to avoid K. CICobs is the closest cast precedent, but its equality and computation rules differ.

**4. Recommended prototype and proof contract.**  
I recommend **A restricted initially to motive-directed transports**, retaining Carneiro’s finite-shape architecture. This is a research proposal, not a completed repair.

Use enriched `WShape n` codes for bottom, level-labelled sorts, Pi tables, rigid names/levels/argument shapes, functions and constructors. Define simultaneously:

- `TyRel env U Γ n A B s`;
- `TmRel env U Γ n t u A m s`;
- related substitutions fitting a semantic valuation.

Bottom imposes no observation; proofs have trivial term relatedness. Pi type relatedness demands deterministic auxiliary Pi observations with **declaratively equal, typable components**, plus smaller-shape codomain instances. Rigid observations carry dependent spine equality. Functions are related pointwise; data records constructor/index coherence; structures are related through permitted projections. Auxiliary evaluation need not imply `IsDefEq`, but exposed components must remain genuine typed `VExpr`s.

The fundamental lemma should retain the prototype’s full substitution generality: an `IsDefEq U Δ t u A` derivation, compatible interpreted shapes `m : s`, and related substitutions `σ,τ : Γ ⇒ Δ` yield related substituted endpoints, including cross-substitution self-relatedness. Restricting its conclusion to types does not eliminate term obligations.

Adequacy must then provide:

- sort levels and the three separations;
- declarative Pi component equalities;
- rigid head/level equality and argument equality;
- telescope-typed `SpineArgsEq`;
- independently, the field-type chain required by `proj_fieldType`.

The first group follows from a completed [`HeadModel`, HeadModel:112](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Experimental/Spike/HeadModel.lean:112). Projection coherence is not an automatic corollary.

The intended well-founded measures are shape depth for relation clauses and transport compatibility, finite interpretation derivations for recursive-definition observations, and typing derivations **uniformly over all depths** for the fundamental lemma. No global normalization measure is available. The missing component-transport construction must genuinely respect these measures.

The three hardest cases are:

1. **K:** prove cast identity from related endpoints, using derivational premises rather than invoking the fundamental lemma on a new check. Uniform motives look tractable; arbitrary endpoint decomposition remains open.
2. **Indexed singleton/native elimination:** reconstruct origins, transport dependent fields, and establish iota/congruence coherence without reflecting index equality.
3. **Projections with eta:** handle unused, untypable earlier projections through a restricted substitution/strengthening theorem. [HeadInversion:43](/home/kim/worktrees/lean4lean/lean4lean-agent-verify-inductives/Lean4Lean/Theory/Typing/HeadInversion.lean:43) correctly identifies this independent gap.

Risk is research-level. First formalize the witness in `VExpr`, then prove the restricted cast lemma and test a nonuniform motive. Require an explicit account of the `I` and projection cases before accepting a full implementation estimate.