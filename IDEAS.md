# Strengthening idea ledger

Scope: `GOAL.md`; canonical `Eq`, every well-formed environment, unchanged executable.
No proof, counterexample, or strictly smaller sufficient obligation has been obtained yet.
An open entry is not a rejection. Work continues while an unrefuted route remains.

| Idea | Test and current verdict |
| --- | --- |
| Compatible concrete pattern computation in eta postponement | **Checked, including the original concrete ParRed relation.** `PatternProjectionTransport` handles constructor projection; `NormalPatternSimulation.normal_pattern_simulation` transports every finite PatternCompute path through ordinary NormalEq without eta reduction. `normal_core_computation` instantiates the actual environment Params. `NormalPatternFactorization.TypedPatternEta.factor` factors compatible pattern/function-eta paths; universe closure supplies the closed-equation hypotheses. Prefixes and structure eta remain outside the input relation, and opaque comparison domains still prevent a strengthening conclusion. |
| Applied iota transport without eta reduction | **Root-rule transport checked; compatible assembly open.** `FreshPatternReflection` proves that concrete patterns cannot consume a fresh final variable and reflects all finite pattern/projection computation at a fresh argument. `NormalSpineExposure.normal_spine_expose_beta` retains extensionality as a strictly smaller comparison instead of adding eta. `PatternIotaTransport.normal_iota_compute` mirrors every enabled concrete ordinary/quotient iota root step through NormalEq using PatternCompute alone. General compatible simulation, singleton/quotient prefixes, and structure eta are still missing. |
| Closed-definition unfolding in eta postponement | **Checked, including actual stored constant equations.** `FreshDeclarationReflection` extends fresh-argument reflection to beta plus closed unfolding. `DeclarationLevelClosure` supplies a sound universe-stable collection containing every original sound equation. `NormalDeclarationSimulation.normal_compute_simulation` mirrors compatible beta/delta paths through ordinary NormalEq; `TypedComputeEta.factor_ofEnv` factors typed beta/delta/function-eta paths into computation followed by normal comparison. Applied patterns, singleton/quotient prefixes, projection-iota and structure eta are still outside the theorem. |
| Postpone eta while mirroring beta through ordinary normal equality | **Compatible beta simulation and beta/function-eta factorization checked; full computation open.** `NormalBetaSimulation.normal_beta_simulation` mirrors every finite compatible beta path through ordinary NormalEq by beta alone, including annotation reductions, eta and extensionality. `NormalBetaFactorization.TypedBetaEta.factor` puts a typed beta/function-eta path into beta followed by one ordinary normal comparison. Opaque domain equalities remain, so this does not supply descending recursive domain certificates. Stored rules, singleton/quotient prefixes, projection-iota and structure eta remain outside the factorization. |
| Finite developments with explicit redex marks | **Active, tool proved.** `MarkedDevelopments.lean` proves termination, existence and uniqueness of complete developments, and typing preservation. `DevelopmentRounds.no_uniform_round_bound` refutes a fixed number of ordinary marking rounds, even on typed identities; it does not refute selective join repair. |
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
| Erase lambda annotations, then reflect at a common type | **Refuted under canonical Eq, even for propositions.** `RecursiveLoopSeparation.canonical_loop_erasure_counterexample` gives two closed, same-typed loops with identical lambda-annotation erasures and no full conversion. `canonical_proposition_erasure_counterexample` lifts the obstruction to two propositions using rigid Eq-family injectivity. This does not refute annotated proof erasure, which retains lambda domains, or strengthening. |
| Superdevelopments, permitting upward-created redexes | **Active, first pass proved.** `Superdevelopments.lean` supplies a structural pass, beta-reduction soundness, typing preservation, and commutation with binder insertion. It solves every identity spine in one pass. `downwardExample_still_hasBeta` leaves a typed lambda-argument redex created at a substituted variable; this tests one pass, not every marking strategy. |
| Recursive lambda-domain comparison certificates | **Active, descent proved.** `DomainNormal.descend` handles non-proof lambdas independently of endpoint type equality and permits beta-redex functions. Symmetry, transitivity, heterogeneous substitution, superdevelopment preservation, and simulation of arbitrary finite beta reductions are checked. Eta and completeness of full confluence remain open; the old domain-counted pilot warns about opaque witness alignment. |
| Beta-only global repair into recursive domain certificates | **Refuted.** `DomainBoundary.no_beta_certificate_join` uses beta-normal `λ h : P f. Prop` and `λ h : P (λ x. f x). Prop`. They have an eta-free `NormalEqF false` comparison, but its opaque domain equality hides eta. This does not refute selective repair or an eta-aware certificate relation. |
| Selective domain certificates plus eta-aware strict descent | **Active, descent proved.** `HybridNormal.descend` permits function lambdas carrying a `DomainNormal` certificate while retaining route A’s eta rules elsewhere. It embeds the recursive relation and handles the global-certificate counterexample. Variable rigidity, symmetry, weakening, homogeneous substitution, and heterogeneous substitution with domain-certified arguments are checked. Construction of hybrid joins remain open. Direct substitution with arbitrary hybrid arguments is refuted; closure up to reduction remains open. |
| Direct heterogeneous closure of selective comparisons | **Refuted.** `DomainBoundary.unrestricted_substitution_fails` substitutes the related boundary lambdas into `g h` and proves no hybrid comparison of the instances. `application_repaired` checks their join after one beta contraction each. A reduction-repair theorem remains live. |
| Arbitrary finite beta-only selective repair | **Refuted.** `RecursiveDomain.canonical_beta_only_failure` constructs a well-formed recursive-family extension preserving canonical Eq, with normally equal typed self-application loops that cannot have a beta-only hybrid join. |
| Typed eta reannotation | **Active, repair proved for the loop test.** `lambda_reannotation` changes a lambda’s domain by eta expansion plus beta when a typing at the new function type is available. `RecursiveDomain.full_repair` repairs the beta-inert loop pair. Obtaining a common function typing below from only a common application type remains open. |
| Full ambient joins with recursive domain certificates | **Proved.** `normal_domain_join` finitely repairs every normal comparison using reannotation and eta expansion; `domain_join_complete` gives such joins for all canonical-Eq declarative equalities. Generated reducts/typings need not descend to the smaller context, so this does not close strengthening. |

Literature check: Bonelli–Barenbaum, [Superdevelopments for Weak Reduction](https://arxiv.org/pdf/1001.4429),
§1 distinguishes upward creation (I/II) from substitution into function positions (III).
Its discussion explicitly allows I/II in ordinary superdevelopments; the identity-spine
example here only excludes a fixed number of ordinary development rounds.

The 2026 Felicissimo–Winterhalter [formalisation](https://github.com/thiagofelicissimo/typed-confluence)
was also inspected. `theories/ConversionChecking.v:eq_erased` assumes an erased **normal**
form (`Nf`) or neutral form (`Ne`), then uses the same common-type/neutral-mode split.
It does not supply reflection of arbitrary non-normal erased terms. It remains a useful
reference, but this theorem alone does not remove the present matched-beta obstruction.

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

| Further refinement | Test and current verdict |
| --- | --- |
| Arbitrary full reduction preserves absence of an unused binder | **Refuted.** `EtaScope.scope_failure_and_cleanup` gives a typed eta step from a lifted identity to a term whose domain explicitly mentions the inserted variable. A finite beta cleanup restores scope in this example. |
| Eta descent from endpoint typings | **Proved.** `eta_lift_descend` lowers a syntactically lifted eta target when both endpoints have a common typing below. It does not derive that target typing from ambient subject reduction. |
| Eta-free repair borrowing only left annotations | **Proved in the ambient context.** `normal0_left_reannotation` fixes the left endpoint and retains the comparison index. `Reannotates.lift_inv` makes the repaired endpoint a lift whenever both inputs are lifts. Lowering the repair's typing and reduction witnesses remains open. |

| Reannotation reduction reflection from scoped, independently typed endpoints | **Equivalent to the original front, not a smaller obligation.** `probeReflection_iff_propositionFront` proves this already for `λ (_ : P). Prop`. `domainProbe_repair_certificate` supplies scoped output syntax and a reflexive certificate below without supplying the missing reduction. |
| Recover function-type shape below before eta repair | **Open, insufficient alone for the current gap.** Pi exposure below would supply eta annotations, but matched lambda arguments still need domain alignment. Existing head observations separate constructors; no operational adequacy or lift-reflection theorem was found in their API. |

| Annotated proof erasure with typed reflection | **Active, structural foundation checked.** `proofErase_reflect` preserves all lambda annotations and reflects equal erased syntax at convertible endpoint types or independently for a non-proof endpoint. This avoids the old heterogeneous-proof counterexample. `proofErase_instN` and `proofErase_liftN` commute with typed substitution and binder insertion. Erased computation, including canonical-Eq singleton and quotient cases, remains to be established. |

| Replay beta reduction of annotated erasures | **Proved.** `proofErase_beta_replay` lifts every finite erased beta path from a typed source to an original beta path with exactly the target erasure. `proofErase_beta_join_descend` descends erased beta joins of lifted terms. Eta and full declaration computation remain open; beta-only completeness is not claimed. |

| Exact replay of eta contraction after erasing proof dependencies | **Conditional obstruction checked; typed eta repair remains open.** `ErasedEta.source_typed_and_erased` makes `λ h : Q. F h h` an apparent erased eta redex. `target_representative_iff` says its short form `F ⋆` has a typed original exactly when Q is inhabited below. `source_eq_of_inhabitant` repairs it when an inhabitant is supplied. No concrete uninhabited canonical-Eq environment or strengthening counterexample is claimed. |

| Bidirectional normal comparison with recursive eta-aware domains | **Active, descent proved.** `BiNormal.descend` uses a common-type mode for arguments and domains and an independent non-proof mode for function heads and lambda bodies. `omega_bidirectional` directly compares the previous recursive loop obstruction. Context conversion and embedding of `DomainNormal` are checked. Transitivity, substitution repair, and completeness are still open; common-mode eta comparisons cannot be blindly used as independent application functions. |

| Applying common-mode comparisons to the same argument | **Proved up to beta joins.** `BiNormal.apply_same_arg` contracts displayed lambda cases and instantiates eta bodies. Homogeneous substitution preserves mode/index; `BiBetaJoin.descend` lowers joins. This is a local rule, not heterogeneous substitution or transitivity. |
| Independent-mode beta simulation | **Refuted, full repair remains live.** `BiBetaBoundary.beta_simulation_failure` compares identity applications to `f` and its eta expansion, then reduces the left to a non-proof variable. No right beta reduct has an independent comparison with it. `full_repair` explicitly joins by eta and beta. This does not refute common-mode beta-join completeness. |

| Common-mode beta-only completeness of bidirectional comparison | **Refuted under canonical Eq, already for propositions.** `GuardedEta.canonical_proposition_failure` uses `D = D → (Prop → Prop)` and eta-related diagonals. A beta-stable guarded-lambda grammar excludes every finite bidirectional beta join. `propositions_full_repair` supplies finite typed eta repair. The proved descent theorem remains useful, but full scope-controlled repair is required. |

| Scope preservation of generated declaration computation | **Proved.** `singletonUnfolding_liftN_inv` and `generate_liftN_inv` use raw dummy substitution, renaming, and determinism. Checked singleton/quotient RHS syntax lowers for arbitrary binder insertions. This does not lower the ambient replay typing checks. |
| Full repair with scoped eta annotations | **Syntax theorem proved; insufficient alone.** `ScopedFullReduction.scope` needs extra scope checks only on function-eta domains and structure-eta parameters; all actual paths below weaken to this presentation. `scopedProbeReflection_iff_propositionFront` shows that reflecting even fully scoped probe paths is still exactly the original front. Recovering the required typings below remains essential. |

| Class-free finite-demand observations for head exposure | **Active; beta/function-eta case proved.** `PureObservation.BetaEta.pi_exposure` and `sort_exposure` extract actual beta paths from arbitrary compatible beta/eta-expansion paths. Finite support supplies beta substitution inversion; eta is sound backwards without typed short representatives. `function_type_below` reconstructs a Pi typing below from such an ambient type trace. Declaration unfolding, pattern/projection computation, structure eta, and adequacy for full declarative conversion remain open. This model is for head exposure, not annotation-erased equality reflection. |
| Finite head observations with recursive closed constant equations | **Proved syntactically.** `ComputeEta.pi_exposure_below` removes function eta and lowers the resulting beta/delta computation through any lift. Constant observations use finite body derivations, with no acyclicity or normalization premise. Environment replay is next; pattern/projection computation and structure eta remain open. |
| Replaying recovered beta/delta type exposure in the smaller context | **Proved for actual environments.** `Definitions.ofEnv_sound`, `Compute.simAt`, and `ComputeEta.function_type_below` reconstruct a Pi typing below without strengthening. `canonical_recursive_head` verifies the strict extension beyond beta on D := D → (Prop → Prop) in a canonical-Eq environment. Full-conversion adequacy remains open. |
| Preserve all untyped finite observations through proof irrelevance | **Refuted in every environment.** `ProofBoundary.no_defeq_observation_preservation` separates the equal proofs λ x : Q. x and λ x : Q. h by `app [pi] pi`. Typed replay nevertheless excludes Pi/sort observations of proofs. This refutes direct full-equality preservation, not the computational head-exposure route: full reduction has no proof-irrelevance step. |
| Lower projection computations by reconstructing dependent field typings | **Proved for saturated constructors.** `ProjectionCompute.descend` lowers complete compatible beta/delta/projection paths and replays their typings solely from the source typing below. Eta elimination and field/constructor observations remain to be added; no ambient field typing is assumed to descend. |
| Cancel captured structure parameters through their projections | **Local cancellation proved.** `RecordExpansion.cancel_projection` removes arbitrary finite nested root expansions, even with unscoped parameters, by actual projection computation. `captured_structure_projection` checks scope failure followed by exact recovery of the lifted original projection. Integration into arbitrary mixed paths remains open. |
| A structure expansion directly computes to a Pi/sort head | **Excluded for the computational fragment.** `ProjectionCompute.struct_no_pi` and `struct_no_sort` use actual constructor rigidity. Any contribution of structure eta to head exposure must go through a surrounding eliminator; field/constructor observations are the next extension. |
| Finite field and constructor observations with actual computational realization | **Foundation proved.** `FieldObservation.Obs.realizes` realizes observations by beta/delta/projection paths; finite support, substitution inversion, function-eta soundness, and backwards projection-computation closure are checked. Structure-eta inversion is next; pattern/prefix computation remains absent. |
| Remove both eta forms from computational projection head exposure | **Proved for arbitrary finite compatible paths.** `FieldObservation.EtaCompute.pi_exposure_below` extracts a beta/delta/projection path below despite unscoped eta annotations; `function_type_below_ofEnv` reconstructs the function type there. `Obs.struct_eta_back` uses actual constructor rigidity and family uniqueness. All existing `EtaPar` steps embed. Pattern/prefix computation and full comparison repair remain open. |
| Replace checked quotient prefixes by a closed constant equation | **Proved for all quotient prefixes.** `ClosedQuot.equation` closes the existing atFive rule by eta; `value_prefix_beta` reaches every generated prefix exactly. The augmented declaration model remains sound and constructor-rigid. `prefix_reflect` reconstructs the exact quotient-prefix equality below using only source typing below, bypassing all ambient capture/major checks. General singleton prefixes are not covered. |
| Package pattern checks uniformly over typed occurrences | **Proved for every concrete core rule.** `ConcretePattern.checkFromTyping` reuses route A's quotient rigid-head alignment proof and retains only fixed universe-level guards. `PatternCompute` embeds all actual `ParRed` steps, is closed under arbitrary raw substitution, lowers syntactically through lifts, and replays from source typing below. `core_reflect` needs no ambient context WF or context-lift relation. This extends operational replay, not eta elimination or the full comparison theorem. |
| Shared constructor tuples and uniform finite RHS certificates | **Proved and integrated for non-structure iota.** `ConstructorObservation.Obs.apply_pat_inv` extracts finite capture demands from ANY pattern RHS observation and certifies operational realization under every realizing capture assignment. A single constructor-tuple observation supplies all major arguments together. `Obs.iota_back` and `EtaCompute.pi_exposure_below` extend mixed head exposure through non-projection constructor rules, both eta forms, and all checked quotient prefixes. Structure-major iota and singleton prefixes still require separate treatment; full comparison repair is still open. |
| Reconstruct structure constructors from dependent projections | **Proved with the actual projection guard.** `StructureReplay.structure_constructor` derives parameter alignment from the declaration and types each projection along the constructor telescope; it does not assume expansion typing. `structure_constructor_neverZero` discharges all field guards for never-zero source universes. `projected_iota` replays the resulting RHS even when its matching constructor uses arbitrary dummy parameters/levels, using checked iota parameter independence. Integration into the raw head model remains open; Prop and universe expressions that may become zero still require the guard argument. |
| Close structure-recursion replay into a constant equation | **Proved and integrated for unindexed structures at never-zero source universes.** `ClosedStructure.canonical_equation` recovers the registered telescope and major-family arity, reconstructs the generic major, and closes by eta. `iota_compute` simulates every raw matching rule through this closed equation, beta, and projections, without occurrence typing. The augmented constructor-observation model retains all previous computations, both etas, and quotient prefixes. Prop-source structures, potentially-zero universes, and indexed singleton prefixes remain open. |

| Discharge structure projection guards from a closed proof-field telescope | **Proved and integrated.** `StructureReplay.ProofFields` records proposition typings for the constructor's field domains in their closed prefix telescopes. `of_telescope` reduces it to one finite telescope; `of_decl_telescope` specializes declaration-level evidence. Reconstruction instantiates these typings along earlier projections, and uniqueness discharges the projection guard. The closed equation and raw iota simulation now accept either this certificate or a never-zero source universe. Zero-field and conjunction-shaped certificates are checked. Enabled-rule checks remain necessary; this does not bypass zero-source singleton prefixes or cover non-proof fields in potentially-zero source universes. |

| Close zero-source unindexed singleton prefixes using proof extraction | **Proved and integrated for every generated prefix.** `ClosedSingleton.zero_equation` derives the exact generated zero-prefix value as a closed equation of the recursor constant, using registered reconstruction, typed captures, actual PatEquation realization, and eta. `generated_prefix_beta` specializes that program to every generated prefix (its syntax theorem also allows indices). `generated_compute` embeds all unindexed prefixes into the mixed head model without occurrence checks; `prefix_reflect_ofEnv` replays them below using only source typing. The augmented model retains all prior equations and both etas. Indexed alignment and full matched-lambda repair remain open. |

| Restrict abstract structure eta to its actual unindexed families | **Proved and integrated.** `NotEtaCtor` admits indexed projection constructors, using constructor-family uniqueness to rule out alternative unindexed metadata. The raw structure-eta rule now carries the actual zero-index guard, and every actual `EtaPar` step still embeds. `of_indexed_iota` admits enabled concrete indexed rules with arbitrary mixed capture paths; all combined head-exposure wrappers rebuild. `indexed_eta_excluded` proves why unrestricted indexed expansion cannot coexist with the new tests. Indexed singleton-prefix alignment and full matched-lambda repair remain open. |

| Recover the exact closed projection-admissibility criterion from actual eta typing | **Proved.** `StructureEtaAdmissibility.expansion_typed_iff` characterizes typed unindexed expansions by a never-zero source universe or `ProofFields`. Projection inversion and universe uniqueness force each projected field to be propositional, then uniqueness in the instantiated closed telescope recovers its original sort. No strengthening is used. Refining constructor observations by this universe-sensitive criterion is next. |

| Universe-sensitive constructor tests cover the remaining ordinary structure iota | **Proved and integrated for every enabled concrete iota occurrence.** Tuple observations now retain actual constructor levels. `NotEtaInstance.iff_registered` permits a test exactly at indexed constructors or eta-inadmissible instances; typed eta still embeds via its recovered closed certificate. `StructureEtaUniverses` transports proof-field certificates across equivalent levels and aligns typed constructor levels with the major family. `OrdinaryIotaCoverage.concrete_iota_coverage` derives registry, family, arity, and the closed-equation/tuple-test split from concrete pattern registration and source typing, without caller-supplied admissibility. Indexed singleton-prefix alignment and full matched-lambda repair remain open. |

| Recover Pi typing below finite actual core/eta traces | **Proved for the complete concrete core and both eta forms.** `CoreHeadExposure.core_compute` embeds every typed `ParRed`, including all parallel capture reductions; stored definitions and all enabled iota patterns are covered. `CoreEtaTrace.compute` threads subject reduction through arbitrary finite interleavings with typed `EtaPar`. `function_type_below_core_eta` reconstructs a Pi typing below an arbitrary binder insertion without lowering eta annotations. This trace fragment excludes projection-iota and generated prefixes; the existing raw model supports projection-iota, quotient prefixes, and unindexed singleton prefixes separately. Indexed singleton-prefix alignment and full comparison repair remain open. |

| Unified actual full-reduction bridge | **Conditional bridge checked; its premise is now refuted.** `FullHeadExposure.step_of_indexed` and `reduction_of_indexed` handle core steps, both etas, projection-iota, every quotient prefix, and unindexed singleton prefixes. `CanonicalEqHeadBoundary.not_indexedPrefixReplay` proves that the remaining `IndexedPrefixReplay` premise is false for this model in every canonical-Eq environment. The bridge locates a missing capability and cannot supply full head recovery until the model changes. It is not a sufficient smaller obligation for PropFront. |

| Indexed K computation using only constructor-tuple demands at the major | **Refuted for the stored-equation model, with registration and typing premises explicit.** `IndexedPrefixBoundary.recursor_variable_no_pi` proves that a registered head with no closed unfolding cannot expose a Pi when its major is a free variable. `canonical_cast_boundary` pairs a canonical-Eq reflexive cast equation with non-simulation in the stored-definition/guarded-iota/projection/eta model. This is not a strengthening counterexample and does not yet refute `FullHead.IndexedPrefixReplay` for the collection enriched by closed unfoldings. Indexed proof elimination needs a new observation/replay mechanism, or a proof that appropriate extra closed equations provide it. |

| Add nonlinear syntactically reflexive cast computation | **Replay and descent proved.** `typeCast_typings` recovers canonical endpoint, proof, and payload typings from any typed source. `CastCompute` extends concrete computation by `cast X X p x → x`, remains closed under arbitrary raw substitution, and descends through every binder insertion using source typing below alone. This covers free proof majors directly. Eta elimination and general indexed-prefix coverage remain open; syntactic endpoint equality may be created by eta expansion. |

| Remove eta after adding nonlinear reflexive casts to raw beta computation | **Refuted for the raw beta/K fragment.** `CastEtaBoundary.raw_eta_elimination_failure` checks a beta/K-normal cast whose endpoints contain `f` and `λ x. f x`. Expanding both short-endpoint occurrences enables K and exposes a Pi; beta/K alone has no Pi reduct. This example is untyped and does not exclude repair by additional declaration rules or typing. A raw finite-demand theorem cannot simply be extended with the nonlinear rule unchanged. |

| Use universe uniqueness to replay casts whose payload exposes a type | **Proved locally, including mixed payload traces.** `cast_type_eq` proves a cast equal to its payload whenever both are types below: the shared endpoint universe equates the successors of their sort levels, hence the levels themselves. No ambient equality or syntactic endpoint alignment is needed. `cast_mixed_pi_exposure_below` and `cast_function_type_below` recover a Pi below an outer cast when its lifted payload has a path in the existing mixed constructor model. Arbitrarily nested casts in function/argument positions and general indexed prefixes remain open; this is not a compatible raw cast-erasure rule. |

| Extract index-type equality witnesses from the major instead of supplying reflexivity | **Closed witness functions proved; arbitrary-occurrence reconstruction is next.** `PropElim.stepValue_typed` eliminates the major into Prop to produce the next cast-telescope witness for every slot. Proof slots return proofs; data slots return equality proofs between the index's type and the next field's type. Constructor branches follow from two typings of the same literal field variable. The generic occurrence has no index-alignment premise. This aims at a transported, uniformly typed singleton program; its field reconstruction, comparison with existing aligned prefixes, and whole recursor equation remain to be proved. |

| Reconstruct singleton fields with actual extracted witnesses at arbitrary indices | **Proved and compared with aligned extraction.** `transportedWitnesses_typed` and `transportedFields_typed` recursively instantiate the closed witness functions without a constructor/alignment premise. `transportedConstructor_typed` produces the constructor at its own resulting indices. `PropTelescope.substEq` proves all typed witness choices equal, and `transportedFields_eq_occ`/`eq_aligned` identify the transported fields with the old program wherever alignment holds. The result-index obligation remains: `eqRefl_typed_iff_endpoint_eq`, with Eq rigidity derived from canonical constructor provenance, shows that typing the Eq constructor at requested endpoints is exactly endpoint conversion. A transported field program is not yet a uniform definitional recursor unfolding. |

| Transport the reconstructed constructor to the requested family proposition | **Proved, with the computational boundary isolated.** `familyWitness_typed` extracts equality of the reconstructed and requested family propositions at arbitrary indices. `castedConstructor_typed` and `transported_singleton_eta` reconstruct the major at its original type using a family cast. Substitution naturality and the constructor-branch computation are checked. `bare_constructor_iff_family_conversion` proves that exposing the bare constructor is exactly definitional conversion of the two family propositions; the extracted propositional equality does not remove that condition. An indexed recursor computation through the retained cast remains open; no unconditional closed recursor equation or smaller sufficient strengthening front is claimed. |

| General K computation with arbitrary dependent Eq.rec motives | **Replay and descent proved.** `eqRecApp_typings` recovers the six canonical telescope arguments from source typing. `eqRecApp_simAt` computes whenever the endpoints are definitionally equal, including proof-dependent motives. `CastCompute.eqRec` makes syntactically reflexive general K available inside every existing compatible computational path; substitution, lift inversion, replay, and descent still hold. It does not lower an ambient endpoint equality or solve raw eta matching. |

| Recover general Eq.rec endpoint alignment from source/minor result typing | **Refuted under canonical Eq.** `EqRecResultBoundary.common_result_does_not_align` builds the well-formed context `[q : Eq Type Prop (Prop → Prop)]`. A constant motive gives an Eq.rec application and its Pi-shaped minor the same sort below, while `sort_forallE_inv` proves its endpoints nonconvertible in that context. This rules out extending `cast_eq_of_common_typing` by first recovering endpoint conversion for arbitrary motives. It does not prove that the recursor and minor themselves are nonconvertible, nor refute full head exposure from an actual ambient reduction. |

| Expose a different reflexivity constructor after transporting the major | **Exact obstruction proved.** `HasCanonicalEq.rigid` derives Eq rigidity from canonical iota provenance. `eqProof_constructor_iff` shows that conversion of a typed equality proof to any Eq.refl, with arbitrary universe/carrier/endpoint, is exactly endpoint conversion. `eqProof_no_constructor_reduction` excludes every finite full reduction to such a constructor at nonconvertible endpoints. The constant-motive test specializes this to every proof of its equality, including transported reconstructions, without an extra rigidity premise. This does not establish nonequality of the enclosing recursor and minor; that alternative remains open. |

| Supply the canonical recursor metadata in the K-model boundary | **Proved from canonical Eq itself.** `HasCanonicalEq.recursorRegistration` recovers the actual registry entry and major offset from the stored pattern. `RecursorRegistered.eqRec_numIndices` derives the exact one-index count from the stored recursor result spine. `canonical_cast_counterexample` constructs a well-formed context and a typed cast-to-Pi equation missed by the stored-equation head model in every canonical-Eq environment. `eqRec_no_unindexed_unfold` excludes the added unindexed singleton equations at Eq.rec. The following full-model test also excludes structure unfoldings. |

| The existing added closed equations might suffice for indexed-prefix replay | **Refuted for the complete current model.** `HasCanonicalEq.projection_indexed` excludes unindexed projection metadata for Eq, and `RecursorRegistered.eqRec_family` identifies Eq as every registered Eq.rec's family. `eqRec_no_full_unfold` excludes all existing stored/Quot/structure/unindexed-singleton equations at Eq.rec. The variable-major observation obstruction therefore survives all these additions. `defeq_pi_full_exposure` turns the genuine canonical K equation into an actual full Pi-exposing reduction; `not_indexedPrefixReplay` contradicts the proposed simulation of that reduction. This refutes exactly the named model premise, not strengthening, full typed head recovery, or an observation model extended with new indexed computation. |

| Source typing repairs eta removal after adding general syntactic K | **Refuted for beta/general-K.** `EqRecEtaBoundary.typed_eta_elimination_failure` uses a constant motive, neutral function endpoint, its eta expansion, and a free equality proof. The source is typed in a constructed well-formed context in every canonical-Eq environment; eta enables K and exposes a Pi, while beta/K alone leaves the source fixed. `source_eq_minor` replays the example using typed endpoint eta below, so this refutes raw eta removal with source typing, not typed strengthening or adequacy of a richer model. |

| Replace syntactic K matching by finite recursive endpoint certificates | **Descent and compatible replay proved.** `GuardedKCompute` separates endpoint matching from compatible concrete computation; its entire path descends whenever common-typed endpoint certificates descend. `KCertificate` discharges that condition at every finite depth: depth zero uses HybridNormal, and successors compute both endpoints with prior-depth K guards before a hybrid comparison. `CertifiedKCompute.pi_exposure_below` therefore handles nested computational/eta alignment from source typing below, without assuming arbitrary ambient conversion descends. Typed examples repair the preceding eta obstruction and use it as an enclosing K endpoint, including arbitrary binder insertion. General indexed-prefix coverage and completeness of the final hybrid comparison remain open; no smaller sufficient front is claimed. |

| Keep proof substitutions delayed without requiring open smaller-context typings | **Same-template comparison proved with certificates.** `HeterogeneousProofSubstitution.subst_certificate_nonproof` and `subst_certificate_common` compare independently typed instances of an arbitrary raw template. Corresponding entries may coincide, have recursive domain certificates, or be proofs of unrelated propositions. No common open typing is required; application typing aligns proof positions locally. `beta_proofs_same_template` places matched proof-argument redexes with a shared body in the existing bidirectional beta-join relation. The following suspension results address general certified bodies and eta; arbitrary lambda-argument repair remains open. |

| Preserve recursive K certificates through beta substitution | **Typed homogeneous substitution proved.** `GuardedKCompute.instN` recovers well-formed binder contexts from source typing and intermediate typings from replay. `KCertificate.substitution` inducts on certificate depth and uses HybridNormal's typed substitution theorem at its leaves. `CertifiedKCompute.instN` preserves the computation at the same certificate depth, including lambda arguments that create redexes. Arbitrary heterogeneous substitution and full comparison completeness remain separate obligations. |

| Supply ambient typing for delayed proof substitutions | **Recursive domain certificates and one-sided eta descend.** `SubstLiftSquare` couples a raw substitution below with a typed ambient substitution, without an open smaller template context. Its commuting square reflects proofness and extends under a chosen domain using ambient alignment. `DomainNormal.suspended_reflect` preserves recursive certificates; `suspended_proof_inst` delays unrelated proof arguments; `suspended_eta_left` handles a certified eta body. The following result closes bidirectional suspension descent; arbitrary lambda-argument repair remains open. |

| Apply computational K certificates through displayed lambda redexes | **Positive-depth application law proved for domain-certified arguments.** `HybridNormal.apply_domain_arg` contracts displayed lambdas and instantiates eta bodies using heterogeneous domain-certified substitution. `KCertificate.apply_domain_arg` lifts the rule to computationally aligned functions without increasing positive depth. Arguments may themselves compute to a DomainNormal pair (`apply_computed_domain_args`); a shared argument always qualifies, even if it is a lambda. Arbitrary hybrid lambda-argument comparisons remain outside the premise, so this does not establish application closure of the entire certificate relation or full completeness. |

| Use separate ambient realizations for eta under delayed substitutions | **Full mode-indexed certificate descent proved.** `BiNormal.suspended_reflect` preserves BiNormal through heterogeneous proof suspensions with independent ambient targets. `SubstLiftSquare.extend` realizes every source-only eta prefix separately; spine inversion removes the eta applications without Pi exposure below. `suspended_sort_types` aligns lower universes using uniqueness within each ambient target. `suspended_beta_proofs` contracts distinct certified bodies with proof arguments. This closes eta for the suspended bidirectional fragment; arbitrary lambda-argument repair and comparison completeness remain open. |

| Increasing K matching strength might supply the old loop's body-eta repair | **Refuted for that exact repair, for every matching predicate and declaration collection.** `PureBodyComputation` proves that variables/applications/lambdas remain in that grammar, and every guarded computation erases to beta after removing lambda domains. `GuardedEta.omega_body_fixed` fixes the ordinary loop's erased body under all such paths. `canonical_guarded_repair_failure` exhibits its genuine full eta repair in a canonical-Eq-preserving extension, while no guarded K path reaches that target. This does not exclude another final comparison or prove failure of all certificate joins. Body eta needs its own scope-safe mechanism; stronger K guards alone cannot produce it. |

| Keep already-proved lambda-argument equalities opaque inside suspensions | **Declarative suspension descent proved.** `DefEqProofSubstRel` admits arbitrary lower equalities alongside unrelated proof pairs. `subst_defeq_nonproof` and `BiNormal.suspended_defeq` use those equalities directly at variable occurrences without re-inspecting substituted lambdas or requiring open template typings. `suspended_beta_eq` handles distinct certified bodies once the argument equality is known below. It does not establish equality of independently typed lambda arguments before their types align, nor produce BiNormal certificates for arbitrary equality entries; the central completeness obligation remains open. |

| Body eta backed by recoverable function types | **Compatible descent proved and the recursive-loop repair is now covered.** `TypeRecovery` reconstructs a chosen type from source syntax, lookup, declarations, and certified type computation. Its complete output syntax and typing descend from source well-formedness below. Application uses uniqueness to obtain the argument typing, avoiding a new conversion premise. `RecoveredEtaCompute` adds compatible eta using recovered Pis; whole paths and Pi exposures descend and weaken. `canonical_recovered_eta_repair` supplies the exact loop repair missed by all old K guards. `captured_eta_not_recovered` confirms arbitrary ambient eta annotations remain excluded. Projection type recovery, broader staged type computations, and coverage up to scoped joins remain open; exact coverage of all ambient targets is impossible. |

| Descend concrete computational joins through suspended substitutions | **Proved for the existing concrete computation.** `CastBiJoin.suspended_reflect` preserves mode-indexed joins under proof suspensions; `suspended_defeq` also accepts opaque lower equalities. Scope inversion and raw substitution lower both paths, and replay supplies reduct typings. Computation includes beta, sound closed pattern equations, and syntactic K. General indexed/eta coverage and join completeness are not assumed. |

| Replace unconditional argument equality with equality conditional on common types | **Refuted, including matched lambda-argument beta pairs.** `ConditionalBoundary.common_entry_descent_failure` gives two typed ambient squares and a reflexive source BiNormal comparison. Every substitution entry agrees whenever its two supplied types are convertible, yet the complete lower applications share a type and reduce to the nonconvertible `Prop` and `Prop → Prop`. A hidden source type is realized differently on the two sides. Both arguments are lambdas. The example works in every Params environment, including canonical Eq; it refutes the weakened invariant, not strengthening. |

| Recover projection field types from the major's recovered family | **Proved without assuming the lower field typing or elimination guard.** `projection_at_recovered_family` uses source projection inversion, rigid-family injectivity, and field-type congruence to reconstruct the selected field type. Raw field selection both preserves and reflects injective binder renaming. `TypeRecovery.proj` therefore weakens and descends, completing its expression-constructor coverage and enabling recovered eta at projections. This does not give completeness of its restricted conversion certificates or full scoped comparison coverage. |

| Use recovered endpoint types to permit common comparison in function position | **Descent and the guarded-loop repair proved.** `RecoveredComparison` extends BiNormal at application nodes. Its independent `recover` rule reconstructs both endpoint types, recursively compares those types, and uses a common-mode child; `sameType` is the shared-output specialization. Soundness, binder insertion, and descent are checked. `canonical_recovered_comparison` compares the guarded eta-loop propositions directly while the old BiNormal relation admits no finite beta join. General recovery/comparison completeness and suspended substitution remain open. |

| Preserve exact type-recovery outputs under arbitrary typed substitution | **Refuted, with a concrete repaired output.** `EtaScope.exact_recovery_substitution_failure` substitutes a valid lifted identity for a variable declared at the captured Pi type. Lookup supplies the source recovery, but exact output preservation contradicts scope reflection. The identity still recovers its ordinary Pi type, and the captured type computes to that output. This rejects an unconditional exact substitution law, not recovery after re-synthesis or substitution with extra argument-recovery evidence. |

| Supply exact recovery evidence for substituted arguments | **Homogeneous substitution proved.** `TypeRecovery.instN_of_recovery` preserves every chosen output type when the argument recovers its declared source type. Lookup uses the argument certificate and weakening; conversion uses certified K substitution; projection reconstruction is preserved. `RecoveredComparison.instN_of_recovery` then preserves both comparison modes, including lambda arguments creating redexes. Arbitrary argument re-synthesis, heterogeneous substitution, and full comparison completeness remain open. |

| Separate type recovery and eta from a fixed computational base | **Checked generic descent interfaces.** `TypeRecoveryWith` and `RecoveredEtaWith` preserve the prior rules and proofs while accepting any computation with verified `ComputeDescent` and `ComputeWeakening`. The old public relations are specializations, and existing loop/comparison/substitution-boundary clients still build. Monotonicity maps certificates between computational bases. This factors the proof so eta computation can itself drive later type recovery; it assumes no arbitrary equality descent. |

| Iterate recovered eta through type computation and K endpoint matching | **All finite stages descend and weaken.** `StagedEtaCompute` lets each stage use its predecessor both for type recovery and for computed endpoint comparisons guarding K. `ComputedComparison.descends` derives matching below; no new descent assumption enters at any stage. `canonical_staged_cast_eta` checks a complete eta → K → recovered-Pi → eta interaction in a canonical-Eq-preserving recursive environment. Uniform scope tests exclude captured eta and captured output recovery at every stage. This closes the finite staging gap, not general comparison coverage, indexed prefixes or re-synthesis under arbitrary substitution. |

| Substitute across different recovery/computation bases | **Generic transformation proved.** `ComputeSubstitutionTo` allows the computational base to change after a fixed typed substitution. `TypeRecoveryWith.instN_to` uses the argument's recovery in the target base; `RecoveredEtaWith.instN_to` then preserves compatible eta and exact output syntax. `GuardedKCompute.instN_to` allows endpoint guards to change as well. The old certified-K and recovery substitution theorems are specializations, without duplicated inductions. This provides the interface needed to grow finite stages; it does not remove the argument-recovery premise. |

| Preserve finite eta/K stages through recoverable beta substitution | **Additive bound proved.** A stage-n computation or type recovery survives substitution of an argument recovered at stage r at stage r+n. The simultaneous transformation covers type computations and computed K guards. `beta_inst` carries staged body computations through displayed beta redexes, including lambda arguments. `loopCast_beta_eta` exercises a stage-two cast-type argument substituted into a stage-one eta body. The argument-recovery premise remains essential. |

| Allow arbitrary finite stage growth to remove argument recovery | **Refuted for exact computation outputs.** `staged_exact_substitution_failure` has a well-formed source context, a typed identity argument, and a stage-one lookup-backed eta step. Substitution yields the captured eta expansion of the lifted identity; no finite stage reaches that exact target. This strengthens the earlier exact-type-recovery obstruction to whole computation paths with unbounded finite stage growth. It does not rule out a different scoped target or re-synthesis of convertible types. |

| Re-synthesize some output after substitution instead of retaining the declared type | **Exact local criterion proved; completeness remains open.** `recoveryExists_iff_heads` characterizes existence of a TypeRecoveryWith output by Pi recovery for applications and usable-family recovery for projections. Other syntax synthesizes structurally. `resynthesize_instN` yields a new recovered type convertible to the old substituted output under those explicit clauses, with no argument-recovery premise. `RecoveryHeads.of_type_exposure` reduces the clauses to computation on inferred types. These head obligations are unproved for the concrete model and are not claimed sufficient alone for strengthening. |

| Remove field-selection success from projection recovery | **Proved redundant.** `projection_recovered_field_exists` derives selection from any recovered family typing, using the source projection's index bound, family injectivity, and constructor telescope shape. `recoveryExists_iff_familyHeads` now characterizes re-synthesis by Pi and family heads alone; `recoveryProjectionExposure_iff_familyExposure` removes the same witness from computation exposure. These remaining head clauses are still unproved for the staged model, and no sufficient strengthening front is claimed. |

| Let recovery choose a term-dependent finite eta/K stage | **Compactness and complete finite-stage closure proved.** `finite_recovery_iff` equates union-based recovery with recovery at one finite stage. `finite_staged_fixedPoint` shows the union is closed under the entire recovered-eta/K stage operation. Nonuniform Pi/family exposure gives finite-stage re-synthesis after arbitrary typed substitution with a convertible new output. Exposure itself remains open; further iteration of the same rules cannot enlarge the union, so coverage must be proved or the rules/guards improved. |

| Open registered residual telescopes using recoverable eta before indexed computation | **Checked for generic recovered telescopes and canonical Eq prefixes.** `TypeRecoveryWith.supplyType` infers the literal residual type of a supplied spine. `StagedEtaCompute.etaOpen` opens any recovered telescope at one extra stage, independent of telescope length; `prefix` closes a body computation again. `eqRec_prefix` applies this to any syntactically supplied canonical Eq telescope with a preceding-stage comparison of its opened endpoints. Concrete prefixes before the proof major and before a fresh proof endpoint are checked. This does not assert that arbitrary ambient index equations have certificates, or identify every registered singleton program with the resulting output. |

| Closed unfolding of indexed Eq.rec when its carrier universe is propositional | **Proved and available as a sound equation extension.** `ClosedProofEq.compute` opens the entire canonical telescope; the carrier is a proposition when its universe is equivalent to zero, so the two fresh endpoints are proof-irrelevant. `equation` types the resulting closed six-binder value at the original recursor type. `definitions_sound` adds it to any existing definition collection, and `definitions_rigid` preserves constructor-sensitive observations. Every supplied arity inherits the unfolding by application. This covers a universe-restricted indexed class, not data endpoint alignment or general indexed singleton coverage. |

| Use recovered application comparisons as staged K guards | **Descent and old-model inclusion proved.** `RecoveredComparisonWith` accepts any checked computational base. `ComparedEtaCompute` lets its K guards use computed endpoints followed by this recovered comparison; every finite stage descends and the old stages embed at equal bounds. The canonical loop/cast/variable-eta example now has a two-stage certificate using direct endpoint comparison, versus the previous three-stage construction. Strict enlargement of the old finite union and general equality coverage are not claimed. |

| Preserve beta substitution after admitting recovered endpoint comparison guards | **Additive bound proved.** `RecoveredComparisonWith.instN_to` transforms the recoveries inside both modes across computational bases. `ComparedEtaCompute.substitution` carries the full new guard relation at stage r+n when the argument recovers its declaration at stage r; `beta_inst` includes displayed beta contraction. The old certified comparison law is a specialization. The essential argument-recovery premise remains; arbitrary re-synthesis is still open. |

| Extend indexed singleton reconstruction from propositional Eq carriers to arbitrary dependent proof indices | **Family conversion and original generated eta proved.** `ProofIndexReconstruction` aligns two typed instances of a propositional suffix after fixed arbitrary parameters. Specialized constructor indices therefore agree with the requested indices, removing the outer family cast. Literal data slots then align with transported fields; `proof_indices_singleton_eta` validates the original generated occurrence without assumed aligned fields or index equations. This covers dependent proof-index telescopes, not arbitrary data indices or full registered-prefix coverage. |

| Use confluence to expose the family of an inferred projection-major type | **Proved for full reduction.** `defeq_rigid_full_exposure` normalizes the rigid side's eta spine and transports it through the join; sort typing rules out proof and lambda alternatives. Normalized projection headers discharge sort-headedness, yielding `projection_type_full_exposure`. Together with existing Pi exposure, the remaining computational completeness issue is repair of full head-exposing paths, with changed annotations/arguments allowed. |

| Separate ambient recovery completeness from scoped computation descent | **Unconditional completeness baseline proved.** `TypeRecoveryWith.hasType_of_replay` needs only ambient ComputeReplay. Canonical confluence then proves `full_recovery_exists` and completeness up to conversion using full reduction as the computational base. Full reduction fails ComputeDescent, so this is not a strengthening proof; it separates synthesis existence from scoped repair. |

| Restrict exact full-reduction descent to sort-typed Pi endpoints | **Refuted by a checked typed example.** `full_pi_target_scope_failure` starts with a closed Pi type and reaches another Pi whose domain contains a captured eta annotation inside a beta-erased argument. The target is not a lift. Thus full head repair must permit changed annotations even when both endpoints already have Pi heads. |

| Turn proof-index reconstruction into a closed equation of the registered recursor | **Exact generated zero-prefix equation proved.** `ProofIndexTelescope` identifies the complete registered telescope with fresh dependent indices and derives the extraction instance after removing motive/minor slots. `ClosedProofIndexUnfolding.zero_equation` reconstructs the major, aligns its proof indices, applies the installed iota equation at typed captures, and closes by eta. The result is the actual generated program, with no ambient unfolding check and no zero-index assumption. Data-index recursors remain outside this fragment. |

| Replay all proof-index singleton prefixes from their closed registered equations | **Raw computation and exact descent proved.** `ProofIndexHeadComputation` adds the generated closed equations to any sound definition collection, preserving constructor rigidity. Every generated arity computes by one closed unfolding plus finite beta specialization, even on raw arguments. Checked prefixes therefore descend using only source typing below the lift, and reflect exactly when both endpoints are supplied below. Empty proof telescopes include all earlier unindexed equations. Arbitrary data-index prefixes and general equality coverage remain open. |

| Reuse tuple observations to repair projection-family exposure | **Proved for the covered mixed head model.** Registered family heads cannot be projection constructors. Empty tuple demands therefore survive backwards through both eta forms, giving pattern computation to the same family/levels with replacement arguments of the same length. `family_exposure_below` removes arbitrary inserted binders; `projection_type_below` reconstructs the selected field typing. `proj_of_eta_trace` compiles this repair into generic type recovery without recovering intermediate eta annotations. Arbitrary indexed-prefix coverage is not claimed. |

| Test annotation erasure on loops at distinct recursive fixed-point types | **Full non-convertibility proved.** `RecursiveTypeSeparation` separates two fresh copies of `D := D → (Prop → Prop)`. `RecursiveLoopSeparation` then separates their closed self-application loops at the shared type Prop → Prop under full canonical-Eq conversion. A cross-domain normal comparison would exclude every recursive body role; finite observations show every full loop reduct retains one. Equal annotation erasures therefore do not reflect conversion, including after encoding the loops as Eq-family propositions. Strengthening itself is not refuted. |

| Track closed type roles throughout full reduction of recursive loops | **Hereditary invariant and separation application proved.** `RecursiveLoopTypes` separates the recursive, Prop → Prop, and Prop roles and determines every eta domain up to conversion. `RecursiveLoopBodies` preserves a role typing at every computational body node through typed substitution, context conversion, core reduction and all full steps. Structure eta and proof irrelevance cannot apply at those nodes; declaration computation remains inside annotations. Full paths erase to beta/function-eta paths. `RecursiveLoopComparison` and `RecursiveLoopObservation` use this invariant to separate the same-typed loops without ambient normalization. |

| Guard arbitrary indexed reconstruction by one comparison of its transported and requested families | **Exact local criterion and certificate descent proved.** For a rigid family, `reconstruction_iff_family_conversion` equates validity of the original generated field telescope and constructor eta with the single family conversion. Rigid injectivity supplies dependent index equations and literal-slot alignment; the converse compares the typed generated fields with the always-typed transported fields. Family substitution/lift naturality then lets existing finite recovered-comparison guards descend this criterion. Registration supplies rigidity and slot bounds. This covers data-index reconstruction under concrete certificates, not certificate completeness or the entire prefix rule. |

| Track proof-index coverage at individual nodes of full reduction | **Whole-path head repair proved.** `PrefixCoveredReduction` retains all full-step constructors and records a declaration-level proof-index certificate only at singleton-prefix nodes. Covered paths embed in the closed proof-index head model, including compatible function and structure eta. Pi/family exposure and lower function/projection typing follow without scope assumptions on intermediate annotations. Coverage is local to a path, not a global restriction excluding canonical Eq's data-index instances. Arbitrary data-index paths and general equality coverage remain open. |

| Derive the complete registered prefix check from its family guard | **Both directions proved at arbitrary prefix arity.** `SingletonPrefixArguments` recovers the full typed argument telescope of the opened source and removes motive/minor slots. `GuardedSingletonPrefix.check_of_family_conversion` derives capture typing, constructor typing and recursor-spine alignment from the one family conversion; `family_conversion_of_check` recovers the guard from every original check. The exact generated program and all data indices are retained. Certificate completeness and lowering the guard remain distinct from this local characterization. |

| Recover projection families through an outer type cast | **Lower typed replay proved.** A well-formed fully saturated registered family has a sort typing even when the available typing has an opaque result type. This reconstructs the cast payload's sort typing from a computational family exposure. Uniqueness aligns the outer cast endpoints, giving family conversion and a usable projection field below; the payload path may contain both eta forms. Saturation is explicit. Compatible arbitrary cast erasure and nested cast cancellation are not established. |

| Descend arbitrary indexed prefix checks through their exact family certificates | **Registered replay and the computation-descent interface proved.** `GuardedSingletonPrefixDescent` transports the guard through the renamed residual telescope, reconstructs the lower check from source typing, and preserves the exact generated target under lifting. `PrefixStep.computeDescent` admits this indexed rule to the generic descent interface; finite recovered comparison supplies its guard descent. `FamilyCertificateCoverage` names the remaining local completeness premise, and `prefix_rule_descend` shows it covers the original prefix rule. Coverage itself and global equality completeness remain open. |

| Require computation descent only for sort-typed inferred types | **Recovery, comparison and a concrete cast extension checked.** `TypeComputeDescent` restricts replay to sort-typed sources; the full TypeRecoveryWith descent induction and both recovered comparison modes need only this interface. `TypeHeadCompute` adds outer cast-to-Pi and saturated-family rules without endpoint-equality premises, with raw substitution, exact scope reflection and sort-typed replay. Its recovered comparisons safely guard arbitrary-source compatible K computation. Full reduction still fails even this weaker interface, by the existing captured Pi-target example. This enlarges the available recovery interface, not a proof of head-exposure or comparison completeness. |

| Close arbitrary indexed prefix certificates under finite recovery staging | **Raw weakening and staged descent proved.** `GuardedSingletonWeakening` proves family naturality from provider lengths alone, so generated prefix guards weaken without source typing. `IndexedEtaCompute` combines predecessor computation, recovered K guards and arbitrary indexed PrefixStep under compatible recovered eta. Every finite stage descends and weakens; all previous ComparedEtaCompute stages embed at equal bounds. This closes the staging interface, not family-certificate completeness or full equality coverage. |

| Preserve beta substitution after adding arbitrary indexed prefix computation | **Additive stage bound proved.** `IndexedRecoverySubstitution` types both guard propositions from the source under the residual telescope, transforms their comparison, and identifies the result with the actual substituted generator output. `IndexedEtaCompute.substitution` and `beta_inst` preserve exact targets at argument-stage plus body-stage. The argument must recover its declared type; arbitrary re-synthesis and family-certificate completeness remain open. |

| Feed cast-head type recovery back into indexed computation and eta | **Finite simultaneous closure checked.** `TypeHeadExtension` accepts payload computations from any preceding ordinary stage, while requiring only sort-source replay for its added cast rules. `TypedEtaStep` turns such recovered Pis into ordinary eta steps. `TypedIndexedEtaCompute` retains every prior indexed stage and lets extended type recovery guard K, arbitrary singleton prefixes, and eta annotations. Descent and weakening hold at every finite stage. The cast rules themselves are not arbitrary compatible term rewrites; general guard/head completeness and recoverable substitution for this enlarged model remain open. |

| Substitute through type-restricted cast recovery and its indexed consumers | **Additive finite-stage bound proved.** `TypeComputeSubstitutionTo` requires sort-typed computation sources; recovery and recovered comparison transform with this weaker interface. `TypeHeadExtension.substitution` uses ordinary predecessor replay for cast payloads and sort replay for transitive intermediates. The enlarged indexed stages preserve substitution at r+n when the argument recovers its declaration at stage r, including generated prefix guards and cast-backed eta annotations. Displayed beta contraction is included. Arbitrary argument re-synthesis and global comparison completeness remain open. |

| Restrict the remaining front to rigid diagonal Eq-family propositions | **Equivalent to PropositionFront.** `EqFamilyFrontBarrier` proves reflection of just `Eq Prop P P` versus `Eq Prop P Q` is exactly proposition strengthening. Ambient completeness on these pairs for any descending certificate relation already implies that front. This refutes outer family shape alone as a strict reduction; it does not identify the more structured FamilyCertificateCoverage predicate with PropositionFront, because generated prefixes also provide a typed major and a specific telescope. |

| Require inhabited proposition endpoints and an ambient Eq witness for certificate coverage | **Still implies the original front.** `InhabitedFrontBarrier` proves that reflection of inhabited propositions is equivalent to PropositionFront using the always-inhabited probe P → P. `WitnessedCertificateBarrier` constructs an object Eq witness from any ambient conversion, so WitnessedPropCoverage for a descending certificate relation still proves PropositionFront. These ambient restrictions do not justify a smaller completeness claim. |

| Use the generated family equality witness below the removed binders | **Sufficient for exact prefix descent; global sufficiency remains open.** `WitnessedPrefixDescent` weakens the local descent premise to inhabited propositions whose object Eq witness already exists in the lower context. The generated constructor, major, and family extractor supply all three lower witnesses. `prefix_rule_descend_witnessed` covers every original registered prefix from that premise, without a finite-certificate completeness assumption. The premise itself, its strictness, and a reduction of full strengthening to it remain unproved. |

| Replay closed declaration and projection computation on annotated proof erasures | **Compatible replay and erased-join descent proved.** `ProofErasureComputation` extends primitive replay through beta, finite composition and every syntax constructor. `ProofErasurePrimitives` gives context-independent closed-body erasure, reconstructs visible constructor spines including proof-marked fields, and replays actual closed delta and saturated projection rules. Both primitive rules also simulate forwards, becoming empty erased paths when their results are proofs. Common erased computational targets descend through binder insertion. This allows recursive definitions without normalization; arbitrary pattern iota, proof-major singleton computation, eta repair and full equality coverage remain open. |

| Transfer registered RHS templates through simultaneous proof-erased captures | **Typed substitution and template invariance proved.** `ProofErasureSimultaneous` reflects proofness through arbitrary typed substitutions, then proves erasure/substitution commutation with an agreement condition only on non-proof source variables. That condition survives proof-valued binders. A typed template consequently has the same erased result in different target contexts when its non-proof captures agree. Instantiating this with every generated recursor capture telescope remains open. |

| Replay registered patterns whose constructor shape survives proof erasure | **Visible matching and capture-rule replay proved.** `ProofErasurePatterns` reconstructs the full original match and capture map from every visible erased match. Registered selectors and applications of two captures replay, including the actual quotient-lift rule with its nonzero universe guard and typing checks. Their union with beta/delta/projection computation has erased-join descent. Proof-valued majors do not have visible constructor matches; arbitrary RHS templates, that missing major case, eta and global equality coverage remain open. |

| Instantiate and replay arbitrary stored recursor RHSs after proof erasure | **Typed capture instantiation and visible iota replay proved.** `ProofErasureTemplates` connects the actual args_typing telescope to simultaneous erased substitution, including proof fields and dependent captures. `ProofErasureIota` retains the stored lambda-wrapped RHS as the head of its capture spine, obtaining exact replay without normalizing recursive templates. Concrete enabled checks supply uniform checks, and the enlarged computational fragment has erased-join descent. Proof-valued majors, eta repair and global equality coverage remain open. |

| Recover erased proof-major constructors through canonical extraction | **Typed reconstruction from erased family certificates proved.** `ProofErasureSingleton` shows that every instance of a proof-only field telescope has the same erased family template at fixed erased parameters, even with data indices. Exact family matching or common erased computation validates the bare extracted constructor. Lifted erased family computations descend even with data fields, retaining transports. This is typed equality, not the existing syntactic PatternCompute replay interface. General original family conversions need not yield these certificates; proof-major operational integration, completeness and eta remain open. |

| Permit typed equality witnesses in erased primitive replay | **Compatible descent and canonical Eq integration proved.** `ErasedPrimitiveDescent` reconstructs equal originals below insertion with exactly the required lifted erasure; it does not require syntactic PatternCompute witnesses. Its compatible closure descends. `ProofErasureK` uses this interface for Eq.rec with arbitrary proof majors and common erased endpoint computations, then closes finite predecessor-guarded stages. General singleton primitive integration, eta repair and computation completeness remain open. |

| Preserve erased computation certificates under binder insertion | **Raw same-stage weakening proved.** `ProofErasureWeakening` proves lift/substitution commutation for erased beta, shifts visible matches and every concrete primitive, and weakens nested endpoint guards without increasing ErasedKStage. This supplies the binder stability needed by a later completeness argument. Arbitrary substitution, eta repair and declarative coverage remain open. |

| Extend lower-witness proposition descent to arbitrary typed K endpoints | **Equivalent local fronts proved.** `WitnessedTermDescent` constructs, from a lower Eq A a b witness, a lower Eq witness between the inhabited families Eq A a a and Eq A a b. Rigid family inversion makes witnessed proposition descent equivalent to witnessed descent at arbitrary endpoint types and universes. Compatible K replay now uses only that weaker interface, while the original EndpointDescent API remains a specialization. Together with the existing prefix theorem, one lower-witness front descends both K and all actual registered singleton prefixes. Global equality completeness and strictness relative to PropositionFront remain open. |

| Isolate the lower-witness front as a single canonical Eq proof comparison | **Exact characterization proved.** `ReflexivityProofFront` strengthens only a supplied equality proof's comparison with reflexivity at its fixed left endpoint; it is equivalent to the witnessed term and proposition fronts. `WitnessedKCharacterization` shows ComputeDescent for compatible K is equivalent to the same front: one root Eq.rec with equality-family motive forces the converse. Adding all registered prefix steps does not increase this local assumption. This is a concrete local obligation, not yet a sufficient strictly smaller obligation for full strengthening. |

| Substitute body and argument computations directly on proof-erased syntax | **Same-stage closure proved.** `ProofShapeSubstitution` supplies raw simultaneous substitution and beta commutation. `ProofErasureStageSubstitution` preserves all visible primitives and finite K guards, combines pointwise image computations with body computations without increasing the stage, and specializes to typed original substitutions. Raw shapes need no argument type-recovery premise. Confluence, general singleton integration, eta repair and full equality coverage remain open. |

| Repair erased eta comparisons using an already typed short endpoint | **Head eta reflection and descent proved.** `ProofErasureEtaHead` handles both a retained bound variable and a proof marker at the last application argument. Common endpoint typing supplies the short function's Pi type; exact erased reflection aligns the body function and proof irrelevance aligns the hidden argument. The relation weakens, reflects through insertion, substitutes, and covers typed original function eta modulo whole-proof identity. Descending computational paths may end in this comparison. Recursive eta comparison and full equality coverage remain open; arbitrary erased eta contraction replay is still not asserted. |

| Simulate typed original beta computation forwards through erasure | **Finite forward simulation proved.** `ProofErasureBetaForward` covers applications, projections, both binder forms and beta contraction, including domain changes and whole-proof collapse. This complements exact beta replay and embeds the paths at every erased K stage. It does not supply confluence or declarative completeness. |

| Recurse through erased eta comparisons with separate type modes | **Recursive comparison and descent proved.** `ProofErasureComparison` uses inferred mode for functions and domains, common mode for aligned arguments, and preserves the enclosing mode under lambdas. Eta is admitted only in common mode; universe congruence and computation at every node are included. Both modes descend, weaken and substitute. This extends terminal eta to aligned subterms without discarding annotations or inventing untyped intermediate witnesses. Inferred function-position eta and full declarative coverage remain open. |

| Feed recursive common-type erased comparison back into K computation | **Finite mutual closure and concrete examples proved.** `ProofErasureComparedK` uses predecessor-stage recursive comparisons as guards, descends from source typing, and preserves weakening and substitution. Old common-target stages embed at the same bounds; actual typed guarded K simulates forwards. `ProofErasureComparedExamples` computes the existing eta obstruction at stage one and its typed nested wrapper at stage two, with lifted descent. General singleton integration, inferred function-position eta and declarative completeness remain open. |

| Recover inferred erased eta from a Pi domain rather than complete endpoint types | **Domain-aligned inference and its sharp boundary proved.** `proofErase_eta_head_infer` needs only a Pi typing of the short endpoint plus conversion of the displayed domains. `Compare.etaLams` recovers that typing by inversion and recursively compares domains, so inferred function positions now support lambda-shaped short endpoints. All closure and finite K descent proofs extend. `ProofErasureEtaDomains` proves apparent erased eta between `fun p : P => (fun x : Q => Prop) q` and `fun x : Q => Prop` is valid exactly when P and Q convert; fixed inhabited canonical-Eq and Pi propositions give an explicit failure without domain alignment. Arbitrary short endpoints, general singleton integration and completeness remain open. |

| Retract raw erased certificates instead of substituting typed witnesses into removed binders | **Arbitrary thinning reflection proved.** `ProofErasureRetraction` defines a raw inverse sending skipped variables to the proof marker and proves every substitution-stable raw relation reflects through thinning. Typed erasure commutes with arbitrary Lift', and finite recursive comparisons therefore descend in both modes with unchanged stages. `ProofErasureSingletonPrefix` feeds this into EndpointDescent and replays actual registered prefixes, including data fields and indices, from erased upper family guards. No inhabitant of a deleted binder is required. Declarative certificate coverage and a raw erased singleton primitive remain open. |

| Cover every concrete core pattern under annotated proof erasure | **Full core forward simulation proved.** `ProofErasurePatternForward` shows a non-proof enabled iota source has a non-proof major by the existing large-elimination guard, so the complete original match survives erasure. `ProofErasureCoreForward` extracts closed typed templates from every installed iota equation, covers definitions and quotient capture application, and simulates every finite concrete PatternCompute path and actual ParRed step. Annotation changes and whole-proof collapse are included; no normalization assumption or additional template-coverage premise remains. Singleton prefixes, structure eta and the normal-comparison certificate gap remain separate. |

| Reverse fresh-argument supply instead of descending a singleton guard | **Actual prefix roots proved.** `PrefixFreshAbstraction` shows the earlier generator record is exactly the later record with one residual domain restored. Its fully opened checking context is unchanged. Unique typing aligns that domain with the supplied binder, so actual indexed singleton prefixes reflect from `f↑ #0` to one prefix step of `f`. `QuotPrefixFreshAbstraction` proves the corresponding quotient result, and `PrefixFreshReflection` gives the final normal comparison needed for eta postponement. Arbitrary compatible prefix paths, structure eta, and opaque comparison-domain descent remain open; this is neither strengthening nor a smaller sufficient obligation. |

| Preserve structure eta as a typed erased head comparison | **Full typed head coverage, reflection and recursive integration proved.** `ProofErasureStructureEta` retains registry membership, saturation and the closed never-zero/proof-field guard. Dependent spine comparison aligns each field domain before proof irrelevance; visible projections use exact erased major reflection. Constructor typing recovers its canonical unindexed family. Every actual typed structure eta yields identity or the guarded raw head rule. It substitutes, weakens and retracts, and now occurs in recursive common-mode comparison and finite K guards. Inferred structure eta and global comparison completeness remain open. |

| Contract the ambient fresh binder with the first residual binder | **Exact typed reflection proved.** `PrefixFreshContraction` identifies the two copies by ordinary substitution, including arbitrary major-type witnesses, and proves invariance of the whole UnfoldingCheck. `PrefixFreshFunction` uses uniqueness to align the domains and reflects an actual singleton or quotient prefix on `f↑` under the domain of a given Pi typing of `f`; the output is exactly a lift of the lower generated output. This handles the immediate-function case beneath eta in addition to the previously proved root case. Deeper function spines and argument computation do not automatically meet the matching-domain premise; full compatible reflection and strengthening remain open. |

| Close erased comparisons under unrestricted raw transitivity | **Refuted in both modes with commonly typed outer endpoints.** `ProofErasureTransitivityBoundary` uses a registered unindexed empty structure as an untyped middle shape between any two common-mode shapes. An application wrapper moves the bridge into an argument, producing nontransitivity in either outer mode. Canonical Eq separates the chosen proposition endpoints by rigid Eq/Pi heads. The result is conditional on the empty-structure registration and is not a strengthening counterexample. Composition with an original intermediate typed at the same type remains unrefuted. |

| Supply an existing function spine before reflecting a prefix check | **Actual checked supply and fresh-spine beta joins proved.** `PrefixCheckedSupply` consumes a typed residual argument in the complete UnfoldingCheck and identifies the exact next generator record. `PrefixSpineSupply` iterates this for singleton and quotient prefixes, then uses fresh-function contraction at the longer prefix. An upper prefix inside a function spine beta-specializes to the lift of an actual lower prefix output whenever the spine stops before the major. This is a join, not exact reflection of the unreduced output; supplied-major and argument-position cases remain open. |

| Promote common erased comparison to inferred mode at sort-typed endpoints | **Same-stage mode conversion proved.** `ProofErasureSortMode` excludes root function eta and structure eta by Pi/sort and rigid-family/sort separation. Typed replay preserves both endpoint sort typings through computation, so common and inferred modes coincide on independently sort-typed originals, even without equality of their displayed universe levels. This removes a mode mismatch for existing type certificates; it supplies neither certificates nor composition. |

| Repair erased composition by requiring a commonly typed original intermediate | **Still implies PropositionFront, even with unbounded finite output stage.** `ProofErasureTypedCompositionBarrier` needs only transport of a stage-zero common comparison across beta. For any P ≡ Q, eta-expanding `fun _ : P => Prop` at domain Q gives a common-typed middle term that beta-reduces to `fun _ : Q => Prop`. `ProofErasureProbe` extracts an inferred domain certificate from any finite comparison of these constant-body probes. Retraction then gives PropositionFront. Typed composition is not refuted, but proving even this restricted case would settle the original front; it is not justified as a strictly smaller remaining obligation. |

| Reflect complete compatible prefix paths using the lower-witness front | **Conditional exact replay and fresh-argument reflection proved.** `WitnessedPrefixReplay` retains the actual lower singleton rule and exact lifted output. `QuotPrefixReplay` checks every admissible Prop-source quotient prefix from source typing alone, by opening to five arguments and reabstracting; quotient replay needs no front. `PrefixComputation` combines these with concrete pattern computation, reconstructs all intermediate typings, and reflects arbitrary compatible paths under the witnessed proposition front. `FreshPrefixReflection` then handles finite paths beneath a fresh eta argument, including supplied majors, argument computation and context conversion after beta. The witnessed front is still assumed; full equality coverage, structure eta and opaque normal-domain descent remain open. This is not a smaller sufficient strengthening obligation. |

| Postpone typed function eta across all actual prefix computation | **Conditional finite factorization proved.** `NormalPrefixTransport` combines beta-only spine exposure, actual argument/universe congruence and fresh reflection to transport singleton and quotient prefixes through arbitrary normal comparison and trailing arguments. `PrefixStep` serializes compatible paths body-first under binders. `NormalPrefixSimulation` transports every finite checked path, including changes of binder context. `NormalPrefixFactorization` factors arbitrary typed pattern/prefix/function-eta paths into computation followed by one ordinary normal comparison, under the witnessed proposition front. No normalization or eta computation is introduced in the output path. The front is still unproved, structure eta is excluded, and opaque normal-domain descent remains open; this is neither full strengthening nor a smaller sufficient obligation. |

| Recover types directly on annotated proof erasures | **Core replay and binder descent proved.** `ProofErasureTypeRecovery` stores variable types in an erased context oracle and reconstructs types for retained variables, sorts, constants, lambdas, applications and Pis, with finite computation on recovered types. Application instantiates the raw codomain by the erased argument; source typing supplies its original even when it is a marker. `ProofErasureRecoveryDescent` reconstructs the whole result erasure below any binder block using only oracle agreement at retained variables. Projection recovery, certificate completeness and substitution/weakening closure of the new recovery relation remain open. |

| Guard inferred erased eta by source-based Pi recovery | **Head descent and recoverable forward coverage proved.** `ProofErasureRecoveryEta` reconstructs the short endpoint's Pi below insertion and compares the long domain with its recovered domain using the existing inferred certificate. This permits arbitrary recoverable short shapes, including variables, with independent endpoint typings. Original eta supplies the new head certificate when its displayed Pi is recoverable; an actual Pi lookup gives a concrete variable case. Compatible comparison integration, projection recovery, and coverage of arbitrary typings remain open. |

| Extend computation/ordinary-normal factorization unchanged to structure eta | **Refuted by an actual typed step.** `PrefixStructureBoundary` proves that PrefixCompute and ordinary NormalEq together fix every non-proof variable at a non-function type. Structure eta expands such a variable to a constructor spine. For every well-formed registered unindexed family at a never-zero universe, the fresh-variable context supplies the obstruction; declaration reconstruction proves the expanded typing, and no inhabitant below the binder is required. This is a representation boundary, not a strengthening counterexample. A full factorization must retain structure expansion in computation or admit an appropriate terminal structure comparison. |

| Use conditional eta factorization for inferred-type head recovery | **Pi and constant-family repair below arbitrary insertion proved.** `PrefixEtaHeadExposure` removes function eta from actual pattern/prefix paths exposing a Pi or sort-typed constant spine, then reflects the computational path under the witnessed front. Constant names, equivalent universe lists and arity survive; the original upper annotations need not be scoped below. The resulting lower equations reconstruct Pi and family typings for original terms. This covers all actual indexed prefixes in the stated fragment, but not full paths with structure eta, the witnessed front itself or opaque comparison-domain descent. |

| Retain both eta forms in a final expansion phase | **Typed phase, prefix exchange and head repair proved.** `EtaExpansion` retains actual Pi typings and both structure endpoint typings; it weakens, converts contexts and satisfies the generic prefix argument interface. `EtaPrefixExchange` moves an actual singleton or quotient prefix before arbitrary compatible eta expansions of its arguments, with the earlier result expanding to a normally equal target and no front premise. `PrefixEtaPhase` covers original EtaPar, embeds the eta-only phase in the existing observation model, and proves Pi/family head repair for computation–eta–normal phases; lower replay still uses the witnessed front. Global postponement of arbitrary FullReduction interleavings remains unproved, especially core contractions consuming eta-created constructors. Closed structure equations remain a candidate tool for that interaction. This is not full strengthening or a smaller sufficient obligation. |

| Permit convertible types in erased variable oracles | **Typed-oracle recovery descent proved.** `ErasedOracleTyping` requires an original typed representative for each retained variable's assigned type, without requiring the literal lookup annotation. `cons_convert` keeps an oracle using the right binder's domain valid in the left binder's context. Generalized recovery and Pi reconstruction descend with this weaker invariant; the previous exact-oracle interfaces remain specializations. This supplies the context alignment needed by compatible recovered eta, not certificate completeness. |

| Make recovered inferred eta compatible under separate endpoint oracles | **Recursive comparison, block descent and same-stage weakening proved.** `ProofErasureRecoveredComparison` retains the earlier raw comparison and adds recovered eta at arbitrary compatible positions. Each binder extends its own endpoint oracle; typed oracle conversion validates both in the lower left context. Recovered eta's domain guard itself uses the new recursive comparison. Symmetry, mode promotion and all syntax constructors are supported. `ProofErasureRecoveredWeakening` preserves recovery and comparison under canonical context insertion, and a nested variable-eta example checks inferred mode beneath a lambda. Projection type synthesis, arbitrary substitution/thinning, feedback into K guards and full equality coverage remain open. |

- **Factor typed erased replay through arbitrary thinning:** checked. Block
  primitive descent plus raw substitution stability gives arbitrary-thinning
  primitive descent by induction on the number of inserted variables. A typed
  factorization constructs each intermediate context using lower declarations,
  avoiding context strengthening. Compatible computation and every finite
  compared-K stage inherit the result. This removes a transport limitation;
  contextual recovery/comparison and completeness remain separate obligations.

| Exchange root contractions with finite typed eta paths | **Constructor/lambda exposure and root exchanges proved.** `EtaConstructorExposure` classifies every finite eta path exposing a constant spine: the head either existed already or comes from registered structure eta, with every final field expanding from a projection of the original source. This gives projection exchange. `EtaIotaExchange` handles registered structure-recursion roots after arbitrary eta paths in the major and supplied arguments, deriving closed unfolding admissibility at the actual recursor universes from source typing. `EtaLambdaExposure` handles arbitrary eta paths in function position before beta, and `EtaPrefixRoot` covers actual singleton/quotient roots using their nonempty checking telescopes. All these root exchanges need no canonical Eq or front. Compatible simulation, whole-path phase composition, and opaque-domain descent remain unproved; this is not strengthening or a smaller sufficient obligation. |

- **Retained typed oracles under arbitrary thinning:** checked. The oracle can
  retain any assigned variable type convertible to its literal lookup type;
  binder extension preserves distinct endpoint annotations. Recovery reconstructs
  exact lower type erasures through arbitrary `Lift'`, then compatible recovered
  comparison descends in both modes. Same-stage weakening follows by factoring
  the thinning into single insertions. The concrete relation now supplies guarded
  K and singleton-prefix descent. Equality completeness and recursive feedback
  into erased computational stages remain open.

- **Does contextual recovered eta remove the typed composition barrier?** No:
  checked `RecoveredCompare.probe_inv` extracts inferred domain comparison from
  constant-sort lambda probes with arbitrary endpoint oracles. Recovered head
  eta is excluded by the probe body, and compatible computation preserves it.
  Typed forward beta transport into the stronger relation, even with any finite
  output stage, still implies PropositionFront. This is not a smaller front.

- **Exact contextual recovery after arbitrary typed substitution, despite proof
  erasure:** refuted at every finite output stage. The extra variable can be a
  proposition, so it survives erasure in the selected captured Pi. Substituting
  a correctly typed scoped identity leaves an output erasure outside the thinning
  image, contradicting checked recovery descent. The identity recovers its plain
  Pi, to which the selected captured type beta-reduces. Re-synthesis remains live.
- **Substitution with exactly recoverable erased images:** checked. An oracle
  invariant requiring each image to recover its substituted assignment extends
  under binders. It preserves recovery and both comparison modes at the same
  stage, including one-variable beta instantiation. This is a restricted lawful
  interface, not a claim about arbitrary typed arguments or proof markers.

| Move finite compatible eta before ordinary normal comparison | **Full exchange and terminal composition proved.** `EtaStep` serializes finite typed eta with original binder contexts. `NormalEtaRoot` reconstructs structure expansion at the normally related left endpoint; `NormalEtaSimulation` handles every compatible position and extensional comparison, giving normal–eta → eta–normal without a front. `EtaNormal` is therefore transitive and compatible, and `PrefixEtaCompatibility` proves every constructor closure plus terminal-phase appending for the three-phase representation. Moving later computation before eta remains open, as do the witnessed front and opaque-domain descent. |

| Test selective contraction after structure eta duplicates its major | **Full three-phase obstruction checked under explicit structure/typing assumptions.** `EtaDuplicationPhaseBoundary` proves an actual FullReduction from c v v to c v (proj_1 (c v v)) has no PrefixEtaNormal representation when the repeated variable is sort-typed and the registered zero-parameter, two-field family is non-propositional. Head-beta exposure excludes arbitrary eta-created lambda intermediates; constructor rigidity fixes the initial computational phase. A never-zero family universe derives the expanded typing and non-propositionality. Both component phases are representable with a commonly typed middle, so typed phase transitivity also fails. This is a conditional factorization obstruction, not a constructed canonical-Eq strengthening countermodel. |

- **Recover dependent projection types by a closed erased field template:**
  checked the source-typing interface, including indexed families. The constructor
  parameter walk follows from the family's actual typing and declaration parameter
  agreement. Earlier projection fields instantiate the closed constructor context.
  Erasure need only agree on retained variables, so proof-valued fields require no
  proofness mask or synthetic inhabitant. A non-proof source projection and a
  recovered major family supply the exact raw result recipe. Integration into
  erased recovery and its transport laws remains the next step toward full syntax.

- **Integrate dependent projections into erased recovery:** checked. The new
  projection rule recovers its major at a registered family and instantiates the
  closed erased field template. Source typing supplies all dynamic checks,
  including indexed-family arity and non-proof universe guards. Exact recovery
  descends through arbitrary thinning and remains stable under weakening and
  recoverable-image substitution. A lookup-major example checks the entire
  thinning path. All retained syntax constructors now have rules; existence of
  suitable computational head certificates remains open. Both the composition
  and exact-substitution obstructions survive the enlarged relation.

| Complete computation after eta of an existing constructor | **Finite exact joins proved with matching parameters and levels.** `ProjectionPathSpecialization` classifies every finite prefix path from a constructor projection: its major arguments compute pointwise until the field is selected, after which only that original field computes. `ConstructorEtaCompletion` assembles the independent field joins for arbitrary parameters, arbitrary fields and any field count. No normalization or computational-confluence premise is used. `CompletedEtaPhase` preserves Pi/family head repair through a further right computation, still assuming the witnessed front for lowering. |

| Replace exact three-phase endpoints by arbitrary right computational completion | **Conditional obstruction checked, even with a computationally fixed target.** `EtaParameterCompletionBoundary` uses structure eta at a converted parameter: an outer one-parameter, one-field constructor changes its nested constructor parameter to a variable, then projects its field. `EtaAtomicConstructorReflection` forces all atomic variable arguments back before terminal eta, while rigid computation cannot turn the original nested constructor into a variable. Never-zero registered inner/outer families derive the actual converted source typing and both expansion typings from the canonical source typing. Thus this FullReduction has no CompletedEtaPhase. No canonical-Eq environment is constructed and strengthening is not refuted. |

| Allow eta on both sides of a computational join | **Head repair and individual full-step coverage checked; finite-path composition remains live.** `SymmetricEtaHeads` and `SymmetricPrefixEtaPhase` preserve Pi/family exposure and lower type repair (still assuming the witnessed front). Both prior selective-projection and converted-parameter obstructions have symmetric phases. `SymmetricEtaAlgebra` proves terminal eta/normal composition through a typed middle by exact eta confluence. `SymmetricPrefixCompatibility` supplies compatible constructors; `SymmetricFullStep` covers every actual full step. Mixed composition must account for the closed equation collection: the neutral structure-readout boundary below excludes it conditionally when a needed recursor equation is absent. General finite FullReduction coverage with the enlarged collection and opaque-domain descent remain open; this is not a smaller sufficient strengthening obligation. |

- **Characterize erased recovery at some output:** checked. For every typed
  non-proof source, existence is equivalent to three local clauses selecting
  sort, Pi, and family outputs from already recoverable immediate subterms.
  Pi formation forces the sort clause, witnessed by a Pi with the tested source
  as domain. Under these explicit unproved clauses, ordinary typed substitution
  re-synthesizes an output convertible to the substituted old type; exact chosen
  output recovery is not needed. This is a completeness characterization, not a
  smaller sufficient strengthening front.
- **Use re-synthesis to obtain unrestricted substitution of recovered
  comparisons:** retains the full front. Checked that even one typed binder
  instantiation of an inferred stage-zero certificate, allowing any finite
  output stage, implies PropositionFront. Instantiate a variable's recovered
  eta certificate with a constant-body lambda at a converted Pi type. Inferred
  lambda comparison reflects the displayed domains, including every recovered
  eta case. Exact image recovery in the existing substitution law therefore
  cannot simply be replaced by ordinary argument typing as a smaller lemma.

- **Use endpoint types to check common-mode erased lambdas:** checked.
  `CheckedCompare` imports the original BiNormal distinction into contextual
  proof-erased comparison: common-mode lambda domains follow from supplied
  endpoint type conversion, while bodies compare under the two retained
  oracles. A recovery rule aligns inferred endpoint types before checking.
  Block descent, symmetry, promotion, weakening and recoverable-image
  substitution hold. Common constant-body probes now compare without a domain
  certificate, strictly enlarging the earlier relation; its common-probe
  extraction obstruction therefore does not transfer unchanged. Inferred
  lambda comparison still reflects domains, and unrestricted inferred typed
  instantiation still implies PropositionFront. General common-mode
  composition and declarative coverage remain open.

- **Feed common-type lambda checking into recursive erased K guards:** checked.
  The oracle-free `RawCheckedCompare` fragment retains arbitrary raw
  substitution, embeds in contextual checking under any oracles, and descends.
  `ErasedRawCheckedKStage` adds predecessor-stage checking guards and includes
  every old compared-K stage at the same bound. Weakening, substitution,
  arbitrary-thinning comparison descent and actual typed forward K simulation
  hold. An Eq.rec source with constant-body lambda endpoints computes at stage
  one without an input domain comparison; source typing supplies their common
  type. No general comparison composition, arbitrary singleton primitive, or
  declarative completeness is claimed.

| Strengthen the eta/eta peak to an exact eta-only diamond | **Checked.** `EtaParallelDiamond` joins two parallel eta expansions by one parallel step on each side. Root copies replay at the opposite typed endpoint, including differently parameterized structure expansions; compatible binder bodies convert through the original domain. `EtaFiniteConfluence` derives a strip lemma and exact finite typed eta confluence. No computation, normal comparison, canonical Eq or front is needed. |

- **Reconstruct BiNormal certificates below thinning with a size bound:**
  checked. `certificate_descend` produces a certificate at the original mode
  with index at most the original index, using the same common-type/non-proof
  replay premise. Fresh-spine inversion and this bound replace an eta-both
  node by a strictly smaller inferred certificate plus promotion. No front or
  canonical-Eq assumption is needed.
- **Prove common-mode composition first for computation-free BiNormal:**
  refuted, even with all three original terms at one type in the empty context.
  Common checking relates constant-body probes at convertible domains; eta
  expansion of the second probe is a second normal certificate. A composite
  would force a normal certificate between the domains. Choose Prop and its
  beta-expanded copy: normal sort/app separation excludes that certificate.
  The two input indices are 1 and 2, and every finite output index is excluded.
  The new raw checking relation repairs the exact pair by beta computation, so
  this refutes the computation-free intermediate plan, not its computational
  replacement. General computational common-mode composition remains open.

| Compose symmetric phases without completing structure recursor equations | **Conditional obstruction checked.** `NeutralRecursorFixed` fixes actual nonzero-source recursor spines with fixed, non-constant-headed arguments. `SymmetricNeutralBoundary` reflects sort-typed projection heads and fixes projections of variables. `StructureReadoutBoundary` combines these with an actual checked identity-branch iota rule: eta/iota/beta reaches a projection, but no symmetric phase connects the endpoints; the two input phases and all three terms are typed at the same sort. Registration, matching, checks, argument fixedness and typing remain explicit; no example environment is constructed. |

| Complete the neutral readout using the existing closed structure program | **Checked exact repair.** `StructureEtaReadout.suppliedBody_eq_eta_rhs` identifies the program with iota on the exact eta expansion, using the registered rule's independence from constructor parameters. The identity-branch program then computes directly to the original major's field projection by beta. The enlarged closed equation collection repairs this root obstruction without a front, but its general mixed phase composition remains unproved. |

- **Admit recursive eta in checked erasure using a recovered domain sort:**
  checked. A synthetic fresh argument cannot be assigned a proof marker merely
  by choice; recovering the displayed domain at a literal sort determines its
  exact erasure. The new common-mode eta rules descend and preserve symmetry,
  weakening and exactly recoverable substitution. Typed forward eta follows
  from any-output recovery existence, with whole-proof endpoints collapsing
  together. Inferred lambda-domain reflection and its full-front instantiation
  barrier survive. Concrete recovery existence and computational composition
  remain open; this is not a smaller sufficient front.

| Decompose arbitrary finite projection paths before completing eta | **Checked.** `ProjectionComputationTrace` retains either a major-only path with the projection intact, or the first saturated constructor exposure, selected field and full subsequent field path. No source typing or confluence is assumed. A fixed nonconstructor major consequently has fixed projections. |

| Absorb computation after eta of a fixed neutral or empty structure | **Checked root cases.** `NeutralEtaCompletion` shows that fixed projected fields leave only parameter computation. Actual family-type conversion validates those computed parameters for a new eta root of the original major, using the unchanged closed admissibility certificate. This covers computationally fixed neutral majors (including variables), and every zero-field structure with no major-fixedness premise. Duplicated majors that compute differently and compatible substitutions remain outside these results; general mixed composition is still open. |

- **Treat erased sort recovery as structural inference:** ruled out as a
  simplification by an exact checked characterization. For substitution-stable
  computation with typed descent, its sort clause is equivalent to universe
  head exposure on original types. A variable at an arbitrary declaration tests
  necessity; raw retraction removes it without an inhabitant. Canonical-Eq
  confluence gives full universe exposure, making the missing clause exactly
  repair of full reductions ending in a universe. Recovery existence therefore
  already implies literal-sort strengthening. No reduction of the full
  proposition front to this fragment is known.
- **Use an ambient sort witness just to classify recursive eta's fresh argument:**
  checked and needs no computational recovery. Equal erasures of independently
  sort-typed terms have equivalent universe levels. Comparing a typed ambient
  representative with the weakened lower domain transfers its sort below, then
  determines the synthetic eta body. This avoids making the full sort-exposure
  premise a prerequisite for eta classification. Integration into a contextual
  certificate is still open; the existing raw checked eta rules continue to use
  recovered sorts.

| Select closed structure equations from the actual registry before proving computational joins | **Determinism and the saturated iota overlap checked.** `RegisteredStructureEquations` restricts the previous sound collection by actual recursor lookup. Fixed-name, fixed-universe unfoldings have literally equal programs, using metadata and pattern uniqueness; soundness, constructor rigidity and supplied computation remain valid. `StructureUnfoldingCriticalPair` joins the already unfolded program to direct iota by beta/projection computation alone. Overlaps with actual singleton prefixes, base equations, equivalent-universe closure and arbitrary compatible reductions are still needed for augmented confluence; none is assumed. |

| Join a closed structure unfolding against an actual singleton prefix | **Disjoint, checked even at equivalent universes.** `StructurePrefixDisjoint` realizes the uniform ordinary iota check using the typed reconstruction in a fresh complete recursor telescope. That enabled guard contradicts the singleton prefix's large-target/zero-source guard. No caller inhabitant or strengthening is required. Registry-selected structure equations additionally exclude the registered quotient head. This removes these root overlaps; compatible peaks, base collection overlap and mixed phase composition remain open. |

| Make the actual stored/structure declaration union deterministic | **Checked.** `DeclarationDeterminism` identifies each stored bare-constant equation with its definition registry entry and excludes the quotient equation's lambda left side. Actual installed iota-head separation excludes a stored definition at each selected structure recursor head. The union is literally functional at fixed universe syntax. |

| Use complete developments for recursive closed beta/delta computation | **Checked base confluence.** `DeclarationConfluence` proves parallel substitution stability, a triangle through complete development, and exact finite confluence for any deterministic closed definition collection. It instantiates the stored/selected-structure union without typing, normalization or a front. Projection/iota/prefix compatible peaks and equivalent-universe closure remain outside this theorem, so it does not yet supply general phase composition. |

| Extend raw complete-development confluence through constructor projections | **Checked.** `ProjectionParallel` and `ProjectionConfluence` prove exact finite beta/delta/projection confluence for deterministic closed definitions whose constructor heads do not unfold. Spine preservation and metadata uniqueness reduce the new projection overlaps to the same smaller original field. The actual stored/selected-structure collection satisfies the premises. Ordinary iota, singleton prefixes, universe closure and mixed eta composition remain to be handled. |

- **Carry sort witnesses in erased contexts rather than recover their types:**
  integrated and checked. Equal erased contexts have convertible well-formed
  realizations. `ContextCompare` uses contextual domain-sort witnesses for
  recursive eta and sorted lambda/Pi comparison, with both bodies interpreted
  in one binder context. It descends through block insertion, covers every
  `BiNormal` certificate, and strictly includes that fragment by the existing
  beta/probe witness. Its oracle-free base and absence of recovered inferred
  eta permit ordinary typed simultaneous substitution, single-binder
  instantiation, arbitrary typed weakening and same-argument beta transport.
  None of these needs recovery completeness. General computational composition,
  substitution of distinct compared arguments, and declarative coverage remain
  open. Existing indexed guards still use their original raw comparison base;
  no contextual-guard completeness is claimed.

| Infer every typed structure/iota overlap from the registry and source typing | **Checked.** `TypedStructureCriticalPair` derives the competing pattern's major offset, constructor and arity, then simulates its contraction using closed delta/beta/projection. Capture computation and arbitrary competing projection paths are covered. The selected collection also preserves every rigid head, including ordinary iota constructors. |

| Eliminate declaration/pattern overlaps before attempting ordinary computational confluence | **Checked reduction of the presentation.** `SeparatedPatternRoots` and `SeparatedPatternComputation` retain only roots whose heads have no closed unfolding at their exact universes. Stored constant rules and enabled structure rules are simulated by beta/delta/projection. Every typed finite ordinary-pattern path translates with identical endpoints; the restricted presentation is substitution-stable. Its raw confluence would imply typed ordinary-pattern confluence, but that remaining theorem, indexed prefixes, universe closure and mixed eta composition are still open. No smaller sufficient strengthening front is claimed. |

| Prove ordinary-pattern confluence after removing closed-delta overlaps | **Checked.** `SeparatedParallel`, `SeparatedPatternMatching` and `SeparatedConfluence` establish raw parallel and finite confluence of the separated presentation. Fixed pattern positions exclude delta, proper subpatterns exclude competing rules by pattern uniqueness, and strict capture subterms provide the induction. Typed path translation gives exact confluence of the original stored/selected-structure ordinary-pattern relation. Actual prefixes, equivalent-universe closure and mixed eta composition remain open; no strengthening front is assumed or proved. |

- **Apply a contextual common-mode function comparison without inferred-mode
  promotion.** Checked in `ProofErasureContextApplication`: both functions may
  receive the same typed argument, even with recursive computations, contextual
  eta-body certificates and distinct displayed lambda domains. Typed body
  substitution and beta contraction cover lambda/eta cases; typed replay covers
  computation. Distinct compared arguments and general composition remain open;
  this is not claimed to be a smaller sufficient strengthening front.

- **Unify the distinct-argument and computational-transport gaps under typed
  contextual composition.** Checked conditional reduction in
  `ProofErasureContextMixedApplication` and `ProofErasureContextComposition`.
  Inferred function application to distinct compared arguments is unconditional.
  Common function application, transport to typed computation targets, and
  paired-body instantiation follow from `ContextCommonComposition`. This law
  remains unproved, and no strict reduction from PropositionFront is claimed.

| Compare generated prefix programs through a shared syntactic template | **Checked, then strengthened to direct congruence.** `PrefixProgramJoins` gives a common zero-prefix beta ancestor, even for indexed singletons, and exact separated-computation joins. `PrefixProgramCongruence` instead generates at fresh variables of the supplied arity: simultaneous substitution literally recovers each entire RHS. Any weakening-stable congruence relation on supplied arguments therefore relates the full programs, including dependent lambda domains. No check or typing of the fresh template, confluence, canonical Eq or strengthening front is required for this congruence. |

| Remove residual normal-domain comparison from prefix argument exchange | **Checked.** `PrefixArgumentExchange` supplies the congruence/replay interfaces for finite actual-prefix computation and instantiates the full-program theorem for both computation and typed eta expansion. Actual singleton and quotient checks replay after argument changes, and their outputs are directly related. Backward eta/root exchange is now exact, without a NormalEq remainder. General prefix confluence, equivalent-universe closure and arbitrary eta/computation composition remain open; this is not yet a smaller sufficient front. |

- **Derive contextual common composition from primitive descent and substitution
  closure alone.** **Refuted** by `ContextPrefixWitness.no_uniform_composition`.
  Two closed partial Eq.rec applications with different motives share a type
  and compare through the same lambda, but fixed-spine inversion forces any
  direct comparison to equate the unequal motives. The beta/full-K fragment
  has both primitive properties. This refutes the generic certificate law,
  not strengthening; composition for richer fragments remains to be tested.
- **Integrate indexed prefix computation into the erased contextual relation.**
  Live. The checked partial-recursion counterexample identifies an exact missing
  operation already supported by the original staged prefix model. Add typed
  descent and substitution-stable erased prefix rules before retrying generic
  composition. Do not assume the new contextual sort witnesses alone solve it.

| Move an entire ordinary path past an actual unsaturated prefix root | **Checked.** `PrefixOrdinaryExchange` excludes stored and selected-structure delta at the checked head and exact universes. Prefix arity excludes ordinary pattern roots at every shorter spine, so ordinary paths only compute supplied arguments. Full-program congruence replays the actual prefix and yields an ordinary residual path with the same endpoint. This includes indexed singletons and quotients. |

| Strengthen the existing core complete-development triangle to literal endpoints | **Checked.** `ExactCoreTriangle` proves `ParRed.triangle_exact` and an exact typed parallel diamond. Smaller capture reductions, typed check transport and dependent-context conversion suffice; the existing triangle's NormalEq remainder is unnecessary for core computation itself. No normalization, canonical Eq or front is assumed. |

| Remove normal comparison from mixed prefix/core diamonds and prefix self-peaks | **Checked.** `ExactPrefixCoreDiamond` gives an exact DeltaPar/ParRed diamond and commutation of both finite closures. `ExactPrefixPeaks` gives exact joins after one further DeltaPar step and core-only paths on each side, including different contraction arities joined by beta supply. Full-program congruence replaces every generated-domain normal comparison; no proof-type collapse is used. |

| Assemble exact confluence of the original computational presentation | **Checked.** `ExactComputationalConfluence` applies the existing decreasing-diagram criterion to core parallel reduction and actual prefix/projection parallel reduction. Their finite union `PrefixCoreReduction` is confluent from every typed source with a literal common endpoint. This includes indexed singletons and recursive core definitions without normalization or canonical Eq. Eta, universe equivalence and extra closed structure equations remain outside this relation; no full strengthening result or smaller sufficient front is claimed. |

- **Erase the canonical Eq.rec prefix before its proof major.** **Checked** in
  `ProofErasurePrefixK` and its finite stages. Source typing recovers the exact
  residual equality domain; raw endpoint checking supplies lower conversion.
  The step descends, substitutes and weakens. It repairs both closed partial
  recursors from `ContextPrefixWitness` at stage one, including a raw checking
  guard usable by later K steps. Other indexed prefixes and general composition
  remain open; arbitrary contextual guards have not been added.

- **Replace full K by proof-major prefix unfolding and beta.** **Checked exact
  equivalence** in `ProofErasurePrefixOnly`. Both primitive presentations have
  the same finite computations, raw checking guards and contextual comparisons
  at every stage. Prefix-only primitives retain descent and substitution. This
  removes one redundant critical overlap, but does not settle guard transport,
  general composition or the full strengthening goal.

| Extend exact computational confluence to the selected structure programs | **Checked.** `SeparatedPrefixDiamond` gives an exact DeltaPar/separated-parallel diamond over the actual stored/structure collection, including both projection presentations. `SeparatedPrefixPaths` extends this to finite ordinary paths. `AugmentedComputationalConfluence` combines that exchange, ordinary confluence and exact prefix self-peaks by decreasing diagrams. The finite augmented union is confluent from typed sources, with no canonical Eq or strengthening premise. The remaining eta/computation composition is not supplied by this result. |

| Transfer augmented confluence to the existing compatible PrefixCompute relation | **Checked.** `PrefixConfluence` derives constructor saturation from projection source typing, embeds typed DeltaPar steps in PrefixCompute, and embeds every PrefixCompute path in the finite augmented union. `PrefixCompute.confluent` supplies exact joins for the relation already used by symmetric eta phases, without canonical Eq or a front. General eta/computation composition remains open. |

| Align independently computed copies of a neutral structure major by finite confluence | **Checked.** `NeutralEtaConfluence` joins every finite family of typed-source reducts. If the major cannot expose its constructor, projection traces retain each independently computed copy; their common reduct reconstructs one eta root after computation on both sides. This removes the prior fixed-major premise without normalization or a front. A complementary exact computational join handles any constructor exposure at the eta root's exact parameters and universes. Constructor exposure at converted parameters/universes and general mixed phase composition remain open. |

- **Transport raw endpoint guards forward through beta without typed sources.**
  **Refuted** by `ProofErasureGuardBetaBoundary`, for every primitive relation
  whose sources have computational roots, hence at every finite enriched K/prefix
  stage. The marker eta guard compares `λ x. (λ y. y) proof` with `λ y. y`;
  beta leaves `λ x. proof`, which cannot compare with the retained-variable
  identity. `expanded_not_typed` proves the bad endpoint has no typed original.
  A typed-source transport theorem remains live.
- **Prove unrestricted raw confluence of the prefix-only presentation.**
  **Refuted** already for one prefix stage over beta. In
  `ProofErasurePrefixRawConfluenceBoundary`, contracting the guarded prefix first
  reaches a fixed lambda; reducing its endpoint first reaches a distinct fixed
  prefix whose guard is impossible. The branches have no common endpoint.
  This does not refute typed-erasure confluence or strengthening.
- **Transfer original exact computational confluence to erased prefix stages.**
  Live, with an explicit missing bridge: typed replay must produce actual
  generated prefix computation, not only `IsDefEq`. Canonical Eq supplies its
  registry entry, but the entry's generated program must still be identified
  with the canonical proof-domain lambda used by the erased rule. The new raw
  counterexample prevents dropping typed-source invariants in this transfer.

- **Repair the raw marker eta/beta obstruction using typed erasure support.**
  **Checked locally** in `ProofErasureTypedEtaBeta`. Substitutions fixing all
  retained variables fix a typed erasure; images of proof variables are arbitrary.
  Consequently `(erase(body).liftN 1 1).inst etaArgument(u) = erase(body)` for
  the body's typed binder domain at sort `u`. Root beta in a lambda eta guard
  restores the same erased body, and common lambda checking accepts the residual
  even with a distinct outer annotation. General typed guard transport remains
  open; no confluence or strengthening conclusion is asserted.

| Reduce constructor-exposing structure-eta overlaps to parameter phase certificates | **Checked.** `StructureEtaParameterReduction` joins every independently computed field using a computational constructor exposure at arbitrary parameters and universe syntax. Typing supplies the universe comparison; only pointwise symmetric phases for constructor/output parameters remain. `SymmetricSpineCompatibility` assembles these without assuming mixed transitivity. This closes all parameterless roots. `StructureEtaProofParameters` additionally closes every root whose original parameters are proofs, using typing-derived conversion and normal proof irrelevance. Data-valued parameter certificates and full compatible composition remain open; no smaller sufficient strengthening front is claimed. |

- **Transfer exact ordinary confluence through typed erasure.** **Checked** in
  `ProofErasureCoreConfluence`, for the actual stored-definition and selected
  structure collection. Both raw branches replay to original computations;
  original confluence and forward erasure give a literal raw join. Reducts retain
  reconstructed typed representatives. Common-reduct endpoint guards transport
  through independent ordinary computation. No canonical Eq or front is needed.
- **Transport displayed function eta through arbitrary ordinary computation.**
  **Checked** in `ProofErasureCoreEtaTransport`. Typed classification forces a raw
  eta guard's marker/variable choice to match its actual domain sort. Lambda
  inversion separates annotation and body paths. Typed confluence joins the
  opened body against the independently computed short function, and contextual
  recursive eta closes the residual pair. This covers both raw EtaHead cases,
  whole-proof collapse, and guards with arbitrary earlier core computations.
  The output is contextual comparison, not necessarily a raw K guard. General
  recursive-comparison transport and indexed-prefix computation remain open.

- **Strengthen core eta transport from contextual to raw checking guards.**
  **Checked** in `ProofErasureCoreRawEtaTransport`. Replay at the opened typed
  function followed by `PatternCompute.fresh_application` reflects its entire
  computation into the short function. The residual is displayed eta or two
  lambdas sharing an erased body; both are raw checking guards and can follow
  any computation of the short endpoint. Typed core confluence aligns that path
  with the independent short path. This covers arbitrary earlier core paths and
  recursive eta bodies witnessed by literal common reducts.
- **Close prefix versus core-argument peaks for join/eta endpoint guards.**
  **Checked** in `ProofErasureCorePrefixPeaks`: a typed non-proof five-argument
  Eq.rec prefix whose endpoints have a core join or displayed-eta guard forms a
  literal commuting square at prefix-only stage one. All five arguments may
  compute independently, including the data used in the generated annotation.
  Guards are transported as raw checking certificates. General recursive guards
  and higher-stage prefix interactions remain open; this is not full confluence.

| Recover data-parameter phases from a family phase using head beta | **Checked.** `NormalSortHeadBeta` mirrors finite head beta through NormalEq when the whole source is sort-typed, carrying pending arguments through eta cases without reducing under lambdas. `SymmetricFamilyArguments` retains eta paths from both original family spines and extracts pointwise EtaJoin or PrefixEtaJoin, including data arguments and differing universe syntax. `StructureEtaFamilyPhase` uses this to discharge the parameter premise of the constructor-exposing eta/computation overlap from a phase between its family instances. Arbitrary typing-derived conversion still does not provide that family phase; general mixed composition and strengthening remain open. |

- **Retain raw guards when common-compared functions are applied.** **Checked**
  in `ProofErasureRawApplication`: both raw comparison layers, in either input
  mode, preserve common raw checking under a shared typed argument. Lambda bodies
  substitute directly; displayed eta applications actually beta-compute to the
  short application; typed replay handles arbitrary computation nodes. This
  works for any substitution-stable primitive relation with typed descent,
  including all finite prefix/K stages, without contextual composition.
- **Use computationally joined arguments to avoid comparison transitivity.**
  **Checked** in `ProofErasureRawJoinedApplication` and
  `ProofErasureRawJoinedSubstitution`. Common-compared functions accept distinct
  arguments with a literal erased join. Paired typed bodies instantiate at such
  arguments with raw certificates in either mode, at the same prefix-only stage.
  Exact erasure equality handles proof captures and dependent result proofness.
  Arbitrarily compared arguments without a literal join remain outside these
  results; no general transitivity or smaller sufficient front is claimed.

| Keep deterministic closed equations while transporting equivalent universes | **Checked.** `Definitions.LevelCompatible` permits structurally level-equivalent unfolding results instead of requiring identical raw results. Stored definitions satisfy it directly. `StructureLevelCompatibility` transports closed proof-field contexts, projection admissibility, concrete guards, and selected programs, proving it for the actual stored/structure union. Normal beta/delta, pattern, and checked-prefix simulations now have compatible variants, with existing interfaces retained. `RegisteredNormalSimulation` instantiates pattern transport unconditionally and prefix/function-eta transport under the witnessed front on exactly the equation collection used by computational confluence. This removes the previous level-saturation mismatch; structure-eta composition and the front itself remain open. |

- **Obtain full typed equality coverage by increasing current raw K/prefix stages.**
  **Refuted** in `ProofErasureRecursiveEtaBoundary`. In the well-formed context
  `g : (Prop → Prop) → Prop`, the equal pair `λ x. g (λ y. x y)` and `g` has
  literal non-proof erasures fixed by every stage. No raw checking constructor
  can compare them: the outer eta is recursive, not displayed head eta.
  Contextual comparison accepts the pair without computation. This persists
  for every closed-definition collection and every finite stage, so further
  stage iteration cannot make the current raw guard language complete. A
  contextual or suitably annotated recursive guard extension is required.

- **Carry contextual eta guards inside context-indexed computation.** **Checked**
  in `ProofErasureScopedComputation`, `ProofErasureScopedComparison`, and
  `ProofErasureScopedTransport`. Primitive occurrences retain their erased
  ambient contexts; binder bodies extend by the source domain. Both computation
  and recursive comparison descend through arbitrary inserted blocks. Typed
  context substitutions preserve every constructor, including changed domains.
  Earlier comparison layers embed whenever their primitives have contextual
  simulations. No transitive intermediate representatives are assumed.

- **Feed recursive contextual comparisons back into finite prefix stages.**
  **Checked** in `ProofErasureScopedPrefixStages` and `ProofErasureScopedCoverage`.
  Guards decrease the stage; every stage has typed block descent, same-stage
  substitution and weakening. Existing prefix-only primitives and full K paths
  embed without stage growth. Full K with new recursive guards factors through
  prefix unfolding and beta. `ProofErasureScopedEtaRepair` accepts the previously
  rejected nested-eta pair and executes a concrete typed constant-motive prefix
  at stage one. This repairs that coverage gap, but neither general composition
  nor declarative completeness follows. Recursive structure-eta coverage and
  arbitrary paired substitution are additional cases to investigate.

| Absorb reparameterized constructor eta as an explicit field-preserving root | **Checked root completion and computation transport.** `ConstructorParameterChange` records two commonly typed saturated constructors with identical fields, potentially different data parameters and universes, and an actual projection-admissibility certificate. The rule is derived by one structure eta followed by field projections, is symmetric, and transports subsequent finite PrefixCompute by computing the same fields on the left. `StructureEtaParameterCompletion` reduces every structure-eta root followed by arbitrary computation to an existing symmetric phase or exactly this residual root, with no parameter-phase assumption. Compatible terminal composition is a separate task; this is not a smaller sufficient strengthening front. |

| Extend the terminal phase by derived constructor parameter changes while preserving head repair | **Checked head-repair interface and all structure-eta root overlaps.** `TypedReconstruction` is the finite compatible closure of existing typed eta and ConstructorParameterChange. It is sound and embeds in the existing head-observation model because each new root is eta followed by ordinary projection computation. `ReconstructionHeads` and `PrefixReconstructionPhase` retain Pi/family exposure and the existing witnessed-front lower type repair. Every structure eta followed by arbitrary finite computation has the extended phase without parameter certificates. General terminal composition and mixed compatible postponement remain open; normal transport of the new root may need head beta computation, so eta-only terminal composition cannot simply be reused. No strengthening conclusion or smaller sufficient front is claimed. |

- **Allow recursive comparisons inside structure-eta fields.** **Checked** in
  `ProofErasureStructureFields` and `ProofErasureScopedStructureCoverage`.
  `ScopedCompare.structFields` replaces literal visible-projection tests with
  recursive common-mode guards. Original source typing reconstructs the family
  parameters and projected constructor below insertion; dependent spine alignment
  supplies each field's common type. Proof fields are skipped soundly. Typed
  substitution, all-stage descent, and previous inclusions still hold. A one-field
  structure with a function field checks function eta inside structure eta, with
  the modified constructor typing reconstructed from the ordinary expansion.
  General composition is not supplied by this additional recursive rule.

| Transport normal comparison across compatible constructor parameter changes | **Checked for one compatible step.** `NormalParameterTransport` exposes a left constructor by head beta and retains its normal-related fields in one derived parameter root. `ReconstructionTransport.fresh_beta_reconstruction` reflects only beta at a fresh argument and leaves reconstruction under a typed lambda. `NormalParameterSimulation.normal_parameter_step` covers all normal constructors and compatible positions as beta, reconstruction, normal. Finite iteration still requires mixed postponement; structure eta's duplicated major prevents assuming directed compatible beta exchange from the head-only result. No strengthening consequence is claimed. |

- **Preserve scoped function guards under shared-argument application.**
  **Checked** in `ProofErasureScopedApplicationSupport` and
  `ProofErasureScopedApplication`. Typed substitution handles common lambda
  bodies and recursive eta; computation replays at the common Pi type; saturated
  structure constructors are excluded by rigid-family inversion. Every finite
  contextual prefix stage supports the result without increasing its bound.
- **Use joined arguments with recursive scoped function guards.** **Checked**
  in `ProofErasureScopedJoinedApplication`. Literal scoped computational joins
  supply typed argument representatives with equal erasures, including prefix
  computations. Inferred function guards also accept arbitrary common-compared
  arguments. Arbitrary common function guards with merely compared arguments
  still need a composition or paired-substitution argument.
- **Consume recursive structure guards by projection.** **Checked** in
  `ProofErasureScopedStructureProjection`: the source's saturated constructor
  computes to the selected field, whose smaller recursive guard compares it
  with the short major's projection. Typed replay handles proof collapse and
  excludes a hidden field when the original projection is a non-proof. Every
  finite contextual stage supports this root case at the same bound. General
  projection closure for arbitrary scoped certificates is not yet proved.

- **Close projection over arbitrary scoped certificates.** **Checked** in
  `ProofErasureScopedProjection`. Primitive-free base certificates are flattened
  into atomic leaves and explicit compatible/computational constructors, with
  the old `ScopedCompare.base` interface retained as a proved embedding.
  Projection typing excludes lambda-headed function eta and identifies an exposed
  constructor's actual family and valid field index. Recursive structure guards
  then select their smaller field guard; computation replays and projects.
  Every finite contextual prefix stage preserves the comparison at the same
  bound. Only one original projection typing is required. This closes general
  projection congruence, not arbitrary paired substitution or transitivity.

- **Replay manual canonical Eq prefixes as actual generated prefix computation.**
  **Open metadata bridge.** `HasCanonicalEq.recursorRegistration` supplies the
  installed entry and index count. Applying `PrefixCompute.confluent` still
  requires identifying `singletonUnfolding`'s generated telescope, captures,
  and RHS with the manual before-major lambda. `eqRecBeforeMajor_simAt` proves
  declarative equality only. Registration alone does not supply those identities;
  no impossibility result or computational replay theorem is claimed here.
- **Compute substituted images beneath dependent scoped binders.** **Checked**
  in `ProofErasureScopedSubstitutionImages`. A typed source substitution and its
  retained-variable agreement suffice to extend pointwise raw computation
  through any typed template. Binder bodies compute under the source-substituted
  domain. Computed image outputs need no separately supplied representatives.
- **Reconstruct a dependent substitution from computed raw images.** **Checked**
  in `ProofErasureScopedSubstitutionRealization`. Induction on the finite source
  context replays retained images and builds a related typed output map; erased
  proof variables impose no image agreement. Consequently contextual
  substitution interpretations are closed under pointwise scoped computation.
- **Close paired scoped substitution for computationally joined images.**
  **Checked** in `ProofErasureScopedJoinedSubstitution`, both for one binder and
  simultaneous dependent substitutions. All comparison modes and finite prefix
  stages are preserved. `ProofErasureScopedSubstitutionSquare` also constructs
  all four edges commuting a typed template computation with pointwise image
  computation, with an identical raw output. These laws do not establish
  paired substitution for merely compared images or general confluence.

- **Reindex scoped paths when a binder annotation computes.** **Checked** in
  `ProofErasureScopedContextConversion`. Actual original context conversion
  interprets the identity raw substitution, so both scoped computation and
  comparison retain their endpoints and modes in the converted erased context.
- **Invert finite scoped lambda computation without typing its raw body.**
  **Checked** in `ProofErasureScopedBinderComputation`. Only the annotation has
  a supplied original sort typing. Replay of annotation paths provides the
  context conversion needed to concatenate later body paths in the initial
  binder context. All finite contextual prefix stages satisfy the head test.
- **Join head beta against finite function and argument computation.**
  **Checked** in `ProofErasureScopedBetaExchange`. Lambda inversion and the
  dependent substitution square produce a literal common contractum. The
  competing residual is one beta step, with no confluence premise and no stage
  growth. This handles computationally related arguments, not arbitrary
  common-compared arguments in a comparison derivation.
- **Retain computed eta bodies instead of reflecting them into the short
  function.** **Checked** in `ProofErasureScopedEtaResidual`. A domain-sort
  witness suffices: arbitrary finite computation of its expanded lambda leaves
  a recursive scoped guard against the unchanged short raw function. Computed
  annotations are replayed and the body path is converted to their context.
  This holds at all finite prefix stages, without original representatives of
  the raw body/function or a computational-confluence premise. Independent
  computation of both endpoints and arbitrary recursive-body guard transport
  remain open; earlier raw eta/probe barriers do not themselves decide them.

- **Invert scoped computation of rigid constructor spines.** **Checked** in
  `ProofErasureScopedSpines` and `ProofErasureScopedRigidRoots`. Visible matching
  preserves its stored pattern head; rigid heads exclude those rules. Canonical
  Eq.rec's installed pattern also excludes K prefixes at rigid heads. If the
  chosen delta collection does not unfold the constructor, every finite scoped
  path retains its name, universes and arity and gives pointwise argument paths.
  Soundness of arbitrary delta equations alone is not used as constructor
  rigidity. The actual stored/registry-selected collection has the needed fact.
- **Retain structure-eta fields after computing the expanded constructor.**
  **Checked** in `ProofErasureScopedStructureResidual`. Every initially visible
  field is a projection of the unchanged short major; its extracted computation
  supplies the recursive field guard in the reverse comparison orientation.
  Proof-marker fields remain markers, and computed parameters retain their
  length. Raw residuals require no original endpoint representatives. The typed
  wrapper handles whole-proof collapse. All finite contextual prefix stages are
  preserved, including for the actual stored/selected structure definitions.
- **Join projection iota against finite constructor-major computation.**
  **Checked** in `ProofErasureScopedProjectionExchange`. Both orders reach the
  selected output field, using the extracted pointwise field path and one final
  projection primitive. No endpoint typings or confluence premise are supplied.
  This does not establish transport of arbitrary recursive field comparisons
  through independent computations of both fields.

- **Use contextual erased guards for all generated singleton prefix layouts.**
  **Checked** in `ProofErasureScopedSingletonPrefix`. A block insertion extends
  through the generated residual telescope at depth `k + domains.length`.
  Both transported and requested families are typed propositions below, so
  scoped comparison descends their guard and rebuilds the actual lower
  `UnfoldingCheck`. The result is an actual `PrefixUnfold` with exactly renamed
  output, including data-field and indexed singleton layouts. At every finite
  scoped K stage, family-certificate coverage consequently gives actual lower
  `PrefixCompute` replay. **Still open:** coverage of ambient family guards and
  an erased primitive encoding all such prefixes. The theorem does not extend
  the raw stage or prove arbitrary-thinning replay, and is not a smaller-front
  result.

- **Identify the manual canonical K prefix with the actual generated program.**
  **Checked**, closing the earlier metadata gap, in `CanonicalEqPrefixMetadata`,
  `CanonicalEqPrefixGeneration`, and `CanonicalEqPrefixReplay`. The installed
  recursor type fixes universe arity 2, major offset 5, motive position 2 and
  target parameter 0. A fresh typed equality-proof major forces source sort
  Prop. Singleton compilation then fixes one family, one constructor, two
  parameters, identity restoration, and exactly the canonical iota equation.
  Its four captures force an empty field layout. The actual generator returns
  the explicit one-domain program with Eq.refl constructor and four captures;
  its RHS is literally the manual K-prefix lambda. Endpoint conversion checks
  that actual program, and canonical Eq supplies its registry entry without an
  additional metadata hypothesis. This removes an operational replay gap; it
  does not supply general family-certificate coverage or raw prefix confluence.

- **Replay complete scoped stages through actual original prefix computation.**
  **Checked** in `ProofErasureScopedOperationalReplay`, using the newly identified
  actual Eq.rec program. The generic compatible replay theorem reconstructs
  typed intermediates and handles annotations and bodies in their source
  contexts. Every finite scoped K stage replays to `PrefixCompute` with exactly
  the same erased target. For an abstract Params presentation, agreement with
  the environment's registry is required only at Eq.rec; actual environment
  Params satisfies this by reflexivity. Original prefix confluence can now be
  applied to the reconstructed paths. **Remaining:** its joins can use general
  indexed singleton prefixes absent from the raw stages, so raw confluence and
  recursive guard transport do not follow from operational replay alone.

- **Type the actual generated captures before checking their family guard.**
  **Rejected proof attempt:** `transportedFields_typed` types the cast-bearing
  `transportedFields` list, while `singletonUnfolding` captures the bare
  `occ(...).2` list. They are not definitionally the same. In a data slot, the
  bare field is the selected index; its declared field type may require the
  alignment supplied by the family guard. No unconditional capture-typing
  theorem was proved; the unproved scratch module was removed. This finding
  rejects that inference, not a general impossibility theorem for every layout.
- **Describe the exact erased output of arbitrary checked singleton prefixes.**
  **Checked** in `ProofErasureSingletonSlots`, `ProofErasureTelescope`, and
  `ProofErasureSingletonPrefixBody`. Typed bare fields erase to a raw slot vector
  selecting retained indices and replacing proof slots by markers. The vector
  commutes with arbitrary raw substitution. The actual checked captures feed
  the fixed closed equation-body template; a non-proof output retains the exact
  residual annotations, each erased in its preceding-binder context. Mixed
  dependent data/proof layouts and indexed families are included. The check is
  retained where it supplies bare-field typing. Uniform reconstruction of the
  erased residual telescope from raw inputs remains to be proved.

- **Represent both singleton family guards by fixed erased occurrence templates.**
  **Checked** in `ProofErasureSingletonFamilyTemplate` and
  `ProofErasureScopedSingletonTemplates`. Unlike bare fields, the cast-bearing
  transported family is typed in the generic parameter/index/major telescope.
  Both it and the requested family therefore erase by substituting erased
  parameters and indices into fixed templates; the major contributes a proof
  marker. Equal erased providers give identical endpoints across arbitrary
  well-formed occurrence contexts, without relating the major proofs. The raw
  scoped template guard is equivalent to the original contextual generated
  family guard under the erased residual telescope. This identifies a uniform
  guard interface but does not prove guard coverage or define a complete
  general-prefix stage.

- **Compute residual telescope erasures by supplying the erased declaration.**
  **Checked** in `ProofErasurePrefixTelescope`. Typed supply commutes with raw
  substitution; typed Pi peeling retains each contextual annotation. Actual
  generated prefixes use a context-independent closed initial type. Equal
  erased supplied arguments determine erased residual domains and results
  across unrelated well-formed contexts, before checking any family guard.
- **Determine opened fresh proof markers from the erased context.** **Checked**
  in `ProofErasurePrefixArguments`. A semantic selector using proofness in a
  well-formed realization is independent of the realization by context-erasure
  reflection and context conversion. Raw opening computes the exact provider
  vector from erased ambient context, residual domains and supplied arguments.
  This is a mathematical selector, not an executable propositionhood decision.
  General primitive construction and recursive guard coverage remain next.

- **Turn the uniform templates into a general raw singleton primitive.**
  **Checked** in `ProofErasureSingletonCode` and
  `ProofErasureScopedSingletonPrimitive`. Fixed declaration metadata and arity
  determine raw telescope, providers, guard and output. One arbitrary generated
  prefix certifies only structural feasibility. Every typed realization of the
  raw input reconstructs its own actual checked prefix from the recursive family
  certificate, with exact erased output. Block descent holds for arbitrary
  inserted binders, indexed families and dependent data/proof fields.
- **Replace Eq.rec-only finite stages by general certified singleton stages.**
  **Checked** in `ProofErasureScopedSingletonStages`: all finite stages descend
  and replay operationally, including compatible computation. A checked original
  prefix erases forward at the next stage when its family guard has a preceding
  certificate. Guard coverage, substitution stability, and transfer of original
  confluence joins are still unproved; this is not a sufficient-front reduction.
- **Transport the semantic fresh-variable selector under typed substitutions.**
  **Checked at typed sources**, using the realized residual telescope and the
  typed-source wrapper described below. The unrestricted raw primitive still
  allows sources without an explicit typed realization; no impossibility claim
  or checked counterexample for its global substitution law is established.

- **Lift simultaneous substitution through actual generated programs.**
  **Checked** in `PrefixUnfolding/Simultaneous`: literal supply, telescope,
  constructor, captures and scoped RHS commute exactly. Generation itself
  requires no typing or guard. This supplies the missing simultaneous version
  of the earlier one-variable naturality theorem.
- **Transport fresh proof markers using a realized residual telescope.**
  **Checked** in `ProofErasureTelescopeSubstitution`: typed substitution and
  retained-variable agreement extend through every binder, proving exact
  annotation, fresh-variable and raw-opening transport. Together with both
  typed family endpoints, `ProofErasureSingletonGuardSubstitution` transports
  the recursive family certificate before checking bare fields. No claim about
  unrealizable raw contexts is needed or proved.

- **Require existence of a typed source realization for the general raw primitive.**
  **Checked** in `ProofErasureTypedSingletonSubstitution`: the fixed code, guard
  and output remain unchanged; source realizability enables exact simultaneous
  substitution under every interpreted context map. Actual checked prefix
  sources satisfy it automatically. This avoids relying on any unproved global
  property of the semantic selector at unrealizable raw contexts.
- **Build general finite stages with descent, replay and substitution together.**
  **Checked** in `ProofErasureScopedTypedSingletonStages`. Guards recurse into
  the previous stage; every stage is substitution-stable and has exact original
  operational replay and block descent. Forward erasure admits all actual
  checked singleton layouts with preceding family certificates. Coverage of
  those certificates and raw confluence are the remaining substantive tasks;
  no strengthening or sufficient-front result follows yet.

- **Transport joined-body eta through contextual computation on both sides.**
  **Checked conditionally** in `ProofErasureScopedEtaConfluence`. Exact typed
  confluence for the same relation joins the computed body and opened short
  function. Replay of the changing annotation supplies the context conversion
  needed for the residual eta rule. Earlier computations before displayed eta
  are included. `ErasedScopedTypedConfluent` names the still-missing confluence
  obligation for general singleton stages; this does not establish arbitrary
  recursive guard transport or allow a guard's stage to increase.
- **Join different certified prefix lengths without constructing a generic guard.**
  **Checked unconditionally relative to primitive descent** in
  `ProofErasureScopedSingletonSupply`. Both existing certificates replay at the
  same original source. Checked spine supply beta-reduces the shorter output
  applied to the tail to the longer output. The final theorem applies directly
  to typed raw primitives, recovers the shared original from the longer source's
  realizability witness, and allows different recursive guard relations. No
  zero-prefix typing, new family certificate, or computational confluence is
  required. Argument-computation overlaps and complete guard coverage remain.

- **Rebuild directed original program congruence from lambda supply.**
  **Redundant:** `PrefixProgramCongruence.singleton_substitution_template` and
  `singleton_program_congr` already give the stronger result for all
  weakening-stable congruence relations, including every residual annotation.
  The experimental duplicate was removed; the new erased bridge reuses those
  checked results. A generic syntax template still does not supply its own
  family-guard certificate.
- **Compute the prescribed raw singleton output after ordinary argument computation.**
  **Checked** in `ProofErasureSingletonCoreResidual`. Replay reconstructs the
  changed original arguments and occurrence check, original full program
  congruence computes the output, and forward erasure identifies the new raw
  telescope and exact prescribed output. Its residual-root constructor still
  explicitly requires the new family guard. This isolates guard transport from
  output computation without assuming guard completeness.
- **Transport joined family guards and close general prefix/core argument peaks.**
  **Checked** in `ProofErasureSingletonJoinedGuard`. Both typed family endpoints
  compute by fixed-template specialization of the opened providers. Conversion
  between old and new residual telescopes preserves the target erasures; typed
  core confluence preserves their existing common reduct. The final theorem
  builds all four sides of the square for arbitrary raw core argument paths,
  with both prefix edges at general singleton stage one and both horizontal
  edges in the core relation. Arbitrary indexed/dependent layouts and whole-proof
  sources are included. Recursive contextual guards beyond common-reduct
  certificates, and computations using higher singleton stages, remain open.

- **Close a recursive core-stable fragment rather than only top-level joined guards.**
  **Checked** in `ProofErasureCoreRecursiveTransport`: typed join and head-eta
  leaves, rigid constant spines with recursively compared arguments, lambda
  congruence/common checking, symmetry, and typed computation before a recursive
  certificate all have two-sided residual raw checking certificates. Rigidity
  excludes primitive contractions at each spine; finite computation is inverted
  pointwise. This admits eta inside nested indices without assuming that those
  indices have literal common reducts. It does not cover arbitrary reducible
  function positions, projections, Pi congruence, or recursive structure eta.
- **Use recursive residuals in the full singleton/core argument square.**
  **Checked** in `ProofErasureSingletonRecursiveGuard`. The original family
  endpoint transport is factored into `Valid.family_core_transport`, retaining
  the previous joined-guard result. The recursive fragment supplies the new
  transport instance, with both prefix edges still at stage one. The output
  guard is a raw/scoped comparison, not necessarily another `RecursiveGuard`;
  this is not closure sufficient to iterate a full stage-confluence argument.
  Complete guard coverage and higher-stage computation remain unresolved.

- **Apply a displayed/computed eta function guard to merely compared arguments.**
  **Checked** in `ProofErasureScopedEtaApplication`. Contract the long application
  first, then compare the two arguments beneath the identical short function.
  Typed replay extends the result to finite computations before the displayed
  eta pair. Arguments need no literal common reduct; the output permits either
  mode. This does not solve paired substitution into arbitrary lambda bodies.
- **Cover a single eta expansion at any compatible position.** **Checked** in
  `ProofErasureScopedEtaStep`. Shared-argument application consumes function
  eta; inferred reflexive functions accept an expanded argument; projection
  closure consumes structure eta. Common lambda checking and sorted Pi rules
  handle annotation changes and dependent bodies with context conversion.
  Every finite general singleton stage, including zero, supports the certificate
  at the same bound. Finite eta paths still need composition, and arbitrary
  computation after the certificate is not covered by this theorem.
- **Reduce all common function application to one explicit paired-body law.**
  **Checked conditional reduction** in `ProofErasureScopedPairedApplication`.
  `ScopedPairedInstantiation` requires compared bodies at one common type in
  one binder context and compared arguments at its domain. Assuming that law
  and primitive descent, every scoped comparison constructor applies to distinct
  compared arguments. It is needed only for lambda and recursive eta bodies;
  literal eta, inferred forms, symmetry and computational wrappers are handled
  directly. The law itself is unproved, and neither its sufficiency for the full
  goal nor strict weakness relative to PropositionFront is claimed.

- **Prove common paired instantiation uniformly from descent and substitution stability.**
  **Refuted** in `ProofErasureScopedLoopBoundary.no_uniform_paired`. In the
  beta-only instance, use the admitted recursive type `D ≡ D → Prop` and its
  beta-normal unfolded Pi `D'`. The diagonals `λ z : D, z z` and
  `λ z : D', z z` share a type and a common-lambda certificate, but substituting
  them into the identical body `z z` produces loops whose comparison would
  require comparing `D` and `D'`. Beta fixes both loops, and the app/Pi domain
  heads cannot compare. Every context and argument is typed; the construction
  is realized in a well-formed extension preserving canonical Eq. This refutes
  a closure theorem for the chosen fragment, not strengthening.
- **Use the actual installed equation to repair that paired-substitution test.**
  **Checked** in `ScopedLoopBoundary.delta_repair` and `erased_delta_repair`.
  Delta/beta computation changes the two diagonal annotations from `D` to
  `D → Prop` while retaining the looping bodies. Both original and erased core
  paths are checked. Thus the beta-only counterexample does not refute paired
  instantiation for the full core relation. Future attempts must use equation
  coverage and account for annotation conversion hidden by common lambda
  checking; a uniform structural proof from descent/substitution is impossible.

- **Read diagonal annotations despite arbitrary finite computation.** **Checked**
  in `ProofErasureScopedLoopReadout`. Computation preserves the self-application
  body and two diagonal heads while changing, discarding, or duplicating their
  annotations. A scoped loop comparison in either mode recovers a common-mode
  comparison of the original annotations. No normality/fixedness premise is
  used, so installed recursive equations no longer invalidate this readout.
- **Test the actual ordinary core with canonical-Eq casts.** **Refuted closure**
  in `ScopedCorePairedBoundary.canonical_core_paired_failure`. The unfolded
  recursive Pi `P` satisfies `P ≡ P → Prop`. Cast `P` reflexively along a fresh
  free equality proof. Its diagonal lambda shares a type and common-body check
  with the original diagonal. Paired instantiation would compare their loops,
  hence the two domains; typed scoped Pi exposure would then force a core Pi
  reduct of the cast. Actual core replay into the existing head model forbids
  that reduct. The environment is well formed and preserves canonical Eq;
  every installed definition and registered structure equation is included.
  This refutes stage-zero paired instantiation, not strengthening.
- **Repair the full-core counterexample with one singleton-prefix layer.**
  **Checked** in `ErasedCore.reflexive_cast_stage_one` and
  `ErasedCore.cast_loop_stage_one`. The endpoint guard is reflexive at stage
  zero; a contextual K prefix and beta remove the cast at stage one. Compatible
  computation changes both loop annotations without normalizing the loop.
  Thus this witness does not refute positive stages or the union of finite
  stages. A general paired-substitution proof must account for hidden domain
  conversions that can demand additional singleton computation. Whether a
  fixed positive stage suffices, whether an increased finite stage suffices,
  and how such closure would yield full coverage/confluence remain open.

- **Allow arbitrary finite output stages in common paired instantiation.**
  **Necessary coverage test checked** in `ProofErasureScopedFinitePaired`.
  Stage-zero body and argument certificates suffice for the test; no bound is
  imposed on the output stage. Function-result recursive loops expose every
  conversion of their annotations at some output stage, including computations
  throughout the certificate. This leaves finite-stage closure itself open.
- **Retain an arbitrary proposition in a recursive family to test the cost of
  finite paired closure.** **Front implication checked, but its interpretation
  is superseded by logical collapse below.** `RecursiveProbeEnvironment` admits
  `R P := R P → (P → Prop)` in an actual well-formed extension preserving Eq.
  `parameter_injective` reads `P` from equality of family applications by Pi
  injectivity and substitution of the diagonal inhabitant. Consequently
  `ProofErasureScopedFinitePairedFront` derives PropositionFront from the finite
  paired law, also for the actual general singleton stages. This is NOT evidence
  of a new irreducible obligation: the same environment has the front without
  the law, as proved independently in `RecursiveFunctionInhabitants`.
- **Exploit canonical Eq after the negative universe recursion, rather than
  using that recursion only to obstruct normalization.** **Proved positive
  fragment** in `RecursiveTypeInhabitants`. `D ≡ D → Prop` yields, for every
  proposition `T`, a Curry proposition `Q ≡ Q → T`, hence a term of `T` by
  diagonal self-application. From inhabitants of all propositions, canonical Eq
  casts the identity on any type `A` from `A → A` to `A`. Every type is therefore
  inhabited in each well-formed context. Substitute an actual inhabitant of the
  removed binder to prove PropositionFront. `canonical_recursiveDomain_front`
  applies to the exact recursive extension used by the full-core counterexample.
  Thus that certificate-closure failure coexists with a proved proposition front.
- **Check whether retaining a function-result parameter avoids that collapse.**
  **No, for the universe-valued result used here.**
  `RecursiveType.inhabit_prop_function` proves the Curry construction for
  `D ≡ D → (P → Prop)` whenever `P` is inhabited. Choose a reflexive Eq proposition
  as the parameter of `R`; `canonical_recursiveProbe_front` proves the front in
  this second actual extension too. The finite paired-law implication is retained
  with this explicit limitation, not advertised as a hardness/equivalence result.
- **Use a fixed data result instead of a universe result for the next recursive
  closure test.** **Open, not yet implemented.** A family returning `P → Unit`
  would retain the proposition parameter while avoiding the particular Curry
  construction above; its loops must remain non-proofs. Do not assume this gives
  a consistency or strictness result. More generally, distinguish genuine
  comparison repair from cases where negative recursion supplies inhabitants
  of the deleted context. Arbitrary nontermination alone does not justify the
  universal-inhabitation argument.
- **Test finite-stage composition using a commonly typed empty-structure
  intermediate.** **Refuted for the current ScopedCompare at every stage.**
  `ProofErasureScopedUnitBoundary` proves that constant/projection-headed
  primitive steps fix variables, so scoped comparisons of two variables force
  their indices equal. Distinct variables of a positive-universe registered
  empty structure nevertheless have an original unitLike equality, and each
  compares at stage zero with the same constructor at their common original
  type. This is not the earlier untyped-intermediate obstruction. More stages
  alone cannot give full composition/coverage. It does not refute the finite
  paired-instantiation law or canonical-Eq strengthening.
- **Recover a family type to justify neutral empty-structure equality below
  insertion.** **Checked root repair** in `ProofErasureScopedUnitGuard`.
  TypeRecovery reconstructs the exact lower family and parameters, and common
  endpoint typing permits unitLike. Variable lookup supplies this guard in the
  two-neutral example; `scoped_unit_guard_strict` exhibits its strict extension
  over every old stage, conditional on a closed registered empty structure.
  This is certificate-extension strictness, not a strictly smaller front.
- **Extend the recovered-family repair to arbitrary structure fields.**
  **Checked sufficient root rule** in `ProofErasureNeutralStructure`. Both
  majors expand at the recovered lower family. Dependent-spine comparison aligns
  each field's type before applying the recursive premise; existing scoped
  certificates on raw projections suffice, with proof projections handled by
  irrelevance. Neither major needs a constructor head. Integration into the
  recursively closed comparison, substitution stability of recovery, and full
  coverage/composition remain open. The sufficient all-projection premise is
  not claimed complete for mixed proof/data fields.
- **Use the carrier already present in an Eq prefix instead of recovering an
  endpoint's selected type.** **Checked and integrated for empty structures.**
  `ProofErasureUnitPrefix` admits a prefix whenever its explicit carrier is a
  registered unindexed zero-field family. Typed-source inversion reconstructs
  the lower carrier and endpoint typings; unitLike supplies equality. The raw
  rule substitutes unconditionally and replays through the actual registered
  singleton program. This avoids the known exact-recovery substitution failure
  at this guard, without asserting that recovery itself is substitution-complete.
- **Feed carrier-based unit prefixes into general singleton computation.**
  **Checked** in `ProofErasureUnitSingletonStages`: every old typed singleton
  stage embeds at the same bound; new stages preserve typed context substitution,
  block descent and exact operational replay. Both partial prefixes and fully
  applied Eq recursors over explicit empty-structure carriers compute at stage
  one. `unit_neutral_sort_exposure` constructs a typed type-valued recursor in
  [S, S] which computes to Prop even though ScopedCompare cannot compare its
  two neutral indices at any augmented stage. This is forward coverage, not a
  proof that no old computational path reaches Prop. The comparison language
  itself still lacks the neutral rule. General structure carriers with recursive
  fields are a live extension: the displayed carrier may similarly avoid
  endpoint type recovery, but field guards and stage transport must be proved.
- **Extend explicit-carrier Eq guards to individual proof fields.** **Checked**
  in `StructureProofField`: a closed specialized constructor-telescope
  certificate for one field is equivalent to proofness of that projection at
  any typed expansion. The converse uses universe uniqueness after telescope
  instantiation, not inverse substitution. Mixed data/proof records can skip
  exactly their proof fields with certificates unchanged by substitution.
- **Carry field types recursively through neutral structure comparison.**
  **Checked and integrated** in `ProofErasureStructureCarrier`,
  `ProofErasureStructurePrefix` and `ProofErasureStructureSingletonStages`.
  Merely delegating every data field to ScopedCompare would leave nested empty
  structures unsupported. The new finite inductive guard instead uses closed
  projection-type recipes as recursive carriers; proof fields are skipped.
  Ordinary scoped checking, symmetry and computation of the carrier are also
  admitted. All cases descend with common lower endpoint types and survive typed
  context substitution. Actual registered Eq prefixes use these guards in the
  general singleton stages, with exact operational replay. Old typed singleton,
  unit-augmented and scoped K-prefix stages embed at the same bound.
- **Exercise nested data fields and mixed proof fields.** **Checked** in
  `ProofErasureNestedStructureExample`. A registered outer structure with one
  empty-structure data field admits a guard for arbitrary neutral majors. In
  the actual context [Outer, Outer], a typed constant-motive Eq recursor exposes
  Prop at stage one despite all-stage failure of direct variable comparison.
  The theorem assumes the displayed registered structures and closed typings;
  it does not construct an environment extension. A separate mixed schema with
  P : Prop and h : P compares the first field and skips the second.
- **Determine whether the new carrier guard directly enlarges proposition
  comparison.** **No at a literal universe carrier.**
  `StructureCarrierGuard.sort_checked` reduces every such guard to the existing
  ScopedCompare at the same computational relation. Primitive-head exclusion
  fixes the universe, ruling out the structure constructors. Any benefit for
  the proposition front must therefore come through richer computation, not
  terminal carrier syntax alone. Complete exposure/guard coverage and
  comparison composition remain live obligations; no smaller sufficient front
  or solution of strengthening is asserted.
- **Retest recursive annotation alignment with a fixed data result.**
  **Actual admitted family checked** in `RecursiveDataEnvironment` and
  `RecursiveDataTyping`: R P := R P → (P → S), for an existing monomorphic
  data constant S. The actual mutual-definition extension preserves WF and
  canonical Eq; Pi injectivity recovers P from equality of family applications
  by substituting the diagonal inhabitant. If S is registered, the literal Pi
  body used by the earlier Curry collapse cannot have type S. This excludes
  that construction only; consistency and other collapse mechanisms remain open.
- **Compare recursive outputs through subsingleton result carriers.**
  **Checked and integrated** in `ProofErasureSubsingletonCarrier` and
  `ProofErasureStructureCarrier`: empty structures and dependent functions into
  certified carriers admit equality of any common-typed endpoints. The shape
  certificate survives arbitrary raw substitution and reflects below insertion.
  For S an empty structure, P → S certifies the non-proof loop results without
  requiring comparison of their internal recursive annotations. The actual
  extension example is checked in `RecursiveDataExample`. This demonstrates a
  repair for this test, not inequivalence of its annotations.
- **Close paired instantiation using a subsingleton result certificate.**
  **Restricted carrier-aware law proved** in `ProofErasureSubsingletonPaired`.
  A carrier comparison of the arguments and a structural subsingleton certificate
  for the dependent result suffice; body comparison is unnecessary. The result
  is a StructureCarrierGuard, deliberately not the older ScopedCompare output.
  It therefore does not prove ScopedFinitePairedInstantiation or general paired
  closure. Literal universes still reduce to ordinary scoped checking, so the
  general proposition front remains open.
- **Extend recursive carrier comparison to general functions.** **Checked**
  in `ProofErasureStructureCarrier` and `ProofErasureFunctionCarrier`. A displayed
  Pi carrier compares the actual fresh applications recursively; a domain-sort
  witness selects a variable or proof marker. Descent extends both contexts
  beneath insertion, with proof-valued functions handled by irrelevance. Endpoint
  computation and lambda-body coverage are integrated. Typed substitution and
  the actual singleton stages still hold. This needs no subsingleton codomain.
- **General paired substitution with computationally joined carrier arguments.**
  **Checked for arbitrary dependent result carriers** in
  `ProofErasureCarrierJoinedSubstitution`, including simultaneous substitutions
  and a same-stage singleton instance. The left carrier and both endpoints
  compute along the common raw image map, whose context interpretation comes
  from typed replay. Distinct proofs are a direct corollary. This extends the
  previously checked scoped joined law to recursive carrier outputs.
- **Obtain full paired closure by wrapping scoped comparison in recursive
  structure/function carriers.** **Refuted** in
  `ProofErasureCarrierPairedBoundary`, uniformly over every actual singleton
  stage. In a context with x,y : S and f : S → Prop, for positive empty structure
  S, the body f z has a reflexive carrier guard and x,y have a subsingleton
  carrier guard. Their instantiated outputs f x and f y have no carrier guard
  at any stage: the Prop carrier reduces to ScopedCompare, variable-headed
  applications cannot compute, and application checking forces x=y syntactically.
  The originals are equal by unitLike and application congruence; this is a
  certificate-closure counterexample, not a strengthening counterexample.
  More singleton stages cannot repair it. A live next direction is carrier-aware
  application checking with a domain justified below insertion, while avoiding
  the already-refuted exact-type-recovery substitution requirement.
- **Use one recovered function domain to check application arguments by their
  carriers.** **Root descent and strict local repair checked** in
  `ProofErasureCarrierApplication` and its example module. Inferred comparison
  aligns the functions; recovery of one function supplies the actual lower Pi
  and argument domain. A carrier comparison then licenses application
  congruence. The exact three-variable neutral counterexample receives a
  lookup-only root certificate, while the previous carrier relation still fails
  at every singleton stage. This is a separate root relation, not yet integrated
  into the recursively substitution-stable singleton stages.
- **Re-synthesize a domain and argument guard together after substitution.**
  **Precise open obligation and conditional transport checked** in
  `ProofErasureCarrierDomainResynthesis`. Neither the recovered domain nor
  codomain must equal its old substituted syntax; the new domain must support
  the transported argument guard. The captured-Pi identity test accepts the
  ordinary re-synthesized domain although exact recovery of its assigned type
  remains impossible at every old compared-K stage. This repairs that test,
  not arbitrary substitution. Ordinary-core CarrierDomainResynthesis is refuted
  below; higher-stage variants remain open. None is claimed sufficient for
  strengthening or strictly smaller than the proposition front.
- **Test the strength of joint domain re-synthesis using reflexive arguments.**
  **Necessary Pi recovery and positive Pi exposure proved** in
  `ProofErasureCarrierResynthesisStrength`. Substituting any non-proof function
  for a fresh function variable forces recovery of a Pi whenever an argument
  is available, even with a reflexive carrier guard. Two fresh binders plus raw
  computational retraction then expose any positive-universe type convertible
  to a Pi, without assuming its domain inhabited below. Joint re-synthesis is
  therefore not merely a structural substitution lemma.
- **Use ordinary-core recovery with arbitrarily strong carrier comparisons.**
  **Refuted** in `ProofErasureCarrierResynthesisBoundary`. In every WF
  canonical-Eq environment, a free reflexive equality proof permits a Pi cast
  which ordinary core cannot expose. Necessary Pi exposure contradicts this
  checked boundary, independently of the comparison primitive relation. No
  recursive extension or registered empty structure is required. A compared-K
  stage-one recovery theorem repairs variable declarations at these reflexive
  Pi casts, so this does not refute later-stage or finite-stage re-synthesis.
- **Permit joint recovery and carrier re-synthesis at an existential later
  stage.** **Open law; conditional application transport checked** in
  `ProofErasureCarrierFiniteResynthesis`. The new domain, codomain, and guard
  share a later stage; monotonicity moves the substituted function comparison
  to that bound. The concrete finite-stage law, general exposure/guard
  adaptation and recursive integration remain unproved. The stage-one cast
  repair is a witness repair, not finite-stage completeness or a smaller front.
- **Test whether existential output stages remove the exposure requirement.**
  **No: finite Pi recovery/exposure is still necessary**, checked in
  `ProofErasureCarrierFiniteStrength`. The fresh-variable/reflexive-argument
  test now selects an output stage, and raw retraction preserves that stage.
  In every WF canonical-Eq environment, finite joint re-synthesis is false if
  recovery remains ordinary core at every stage, regardless of how comparison
  primitives grow. Both sides of the staged interface must therefore be tested.
- **Adapt subsingleton argument guards through a beta join of domains.**
  **Checked** in `ProofErasureCarrierDomainJoin`. Structural subsingleton
  certificates survive arbitrary beta paths: empty structure heads and arities
  remain, while dependent Pi codomains recurse. A different recovered domain
  computing to the same reduct inherits the argument guard. The application
  transport lemma combines this with typed contextual substitution of the
  function comparison and a supplied new Pi recovery. It does not construct
  the new recovery or the join, nor cover arbitrary structure/function guards.
- **Check old compared-K recovery against the newer neutral-unit guards.**
  **Refuted as a recovery family for finite joint re-synthesis**, checked in
  `ProofErasureNeutralKNormal`, `ProofErasureNeutralKCore`, and
  `ProofErasureNeutralKExample`. Every core-normal shape whose full Eq recursors
  have distinct bare-variable endpoints stays literally fixed at every old
  compared-K stage. Canonical registration excludes iota at shorter prefixes;
  the erased proof major excludes visible constructor matching at the full root.
  A typed constant-motive recursor over two variables of a positive closed empty
  structure is equal to a Pi and exposes it at new unit stage one, while all old
  stages leave its entire erasure fixed. This includes motive annotations and all
  stored/selected core equations. Finite Pi-exposure necessity therefore refutes
  joint re-synthesis with this old recovery family, for arbitrary comparison
  stages. This is a certificate-family refutation, not a strengthening counterexample.
- **Replace old recovery computation with contextual carrier computation.**
  **Descent and strict local improvement checked; completeness remains open.**
  `ProofErasureScopedRecovery` retains all syntax-directed recovery rules and
  runs conversion in the actual context, extending it beneath binders. Old raw
  certificates embed under contextual simulation. Arbitrary block descent and
  the carrier-aware application root are checked in `ScopedRecoveryDescent`
  and `ScopedCarrierApplication`. `ScopedRecoveryExample` recovers a Pi at new
  structure stage one for a typed variable for which no old compared-K stage
  recovers any Pi, including with the actual core equation collection.
- **Preserve exact selected types using the richer contextual recovery.**
  **Refuted for every computation family admitting contextual descent.** The
  captured-Pi identity example still fails: descent would make its fresh-variable
  annotation a lift of lower syntax. Joint re-synthesis must still choose a new
  recovered domain and its argument guard together. `ScopedCarrierResynthesis`
  states this open finite law and proves its conditional application transport.
- **Reuse raw retraction for contextual recovery's exposure necessity.**
  **Not justified.** The finite scoped law forces Pi recovery with an available
  argument, and Pi exposure in the context extended by a function and argument
  binder. Arbitrary raw proof-marker substitution need not interpret a typed
  context substitution. The checked necessity theorem keeps those binders;
  lower-context computational exposure requires a separate argument.
- **Integrate recovered applications into recursive computational guards.**
  **Descent, operational replay and a concrete exposure repair checked.**
  `ProofErasureApplicationComparison` retains the full scoped checking grammar
  and adds an application rule with contextual Pi recovery, recursive inferred
  function comparison and an argument carrier guard. Old comparison and local
  recovered roots embed. `ApplicationPrefix` uses this recursive language in
  actual Eq prefixes. `ApplicationStages` adds finite layers while preserving
  every old structure-singleton stage at the same bound. `ApplicationStageExample`
  uses f x / f y for distinct unit variables as proposition endpoints: stage-zero
  recovered checking now makes the Eq recursor expose its Pi payload at stage one.
  Old direct carrier guards fail at every old stage; alternative old computation
  paths have not been excluded, so no all-path computation separation is claimed.
- **Substitute the new application-checked stage family.**
  **Open.** Same-stage primitive substitution cannot be inferred from descent or
  operational replay: a recovered domain may need re-synthesis. The scoped finite
  joint law addresses the local application rule, but recursive checking and
  computational stages need a finite-stage transport proof that aligns the
  chosen bounds. No substitution/completeness theorem for ErasedApplicationStage
  has been asserted.
- **Use the new endpoint checker throughout explicit carrier guards.**
  **Open integration choice.** StructureCarrierGuard still internally uses
  ScopedCompare. Its full paired closure remains refuted even with the enlarged
  computation family, by not_carrier_finite_paired and the new stage-head theorem.
  ApplicationCompare fixes the neutral-application comparison in the enlarged
  language and Eq guard, not in the unchanged carrier relation. Generalizing
  the carrier/checking recursion, or avoiding full paired closure via actual
  joins, remains necessary for any route relying on that law. Neither integration
  nor the current exposure witness is a smaller sufficient strengthening front.
- **Remove stage alignment from contextual joint re-synthesis.**
  **Exact equivalence checked, not a solution of re-synthesis.**
  `ProofErasureStageUnion` collects all primitive bounds in a computation,
  recovery, scoped comparison, carrier guard, or application comparison into
  one finite stage, including bounded structure-field families.
  `ProofErasureScopedResynthesisUnion` proves finite joint re-synthesis iff
  re-synthesis over the two monotone unions. Inputs and outputs may initially
  choose different bounds; maxima align them without prescribing a domain.
  Consequently bound alignment is no longer a separate open semantic task.
- **Treat the application-stage union as a closed recursive computation relation.**
  **Least fixed point, descent, and replay checked.**
  `ProofErasureApplicationUnion` proves the union is exactly core primitives
  plus general typed singleton, structure-prefix, and application-prefix rules
  guarded by the union itself. Every such guard fits at a finite predecessor
  stage. Any relation containing core and closed under these constructors
  contains the union. This licenses stage-free reasoning about this exact
  computation family; it does not give substitution, join closure, or comparison
  completeness. The old carrier grammar is unchanged and remains subject to
  the neutral-application paired-instantiation obstruction. The next semantic
  task is compatible domain/guard re-synthesis or richer mutual checking, not
  additional stage bookkeeping. No smaller sufficient front is claimed.

- **Test joint re-synthesis against the remaining old general-singleton guards.**
  **An integration gap was identified; no counterexample established.** The
  application-stage family's special Eq prefix used ApplicationCompare while
  its general singleton family guard still used ScopedCompare. This prevented
  directly using newly recovered application certificates in arbitrary generated
  family checks. This mismatch alone does not refute re-synthesis or exclude
  alternative computations. No registered non-Eq separation witness was proved.
- **Use recovered application checking in all generated singleton family guards.**
  **Generic descent/replay interface and recursive integration checked.**
  ProofErasureSingletonComparison parameterizes only the family comparator,
  retaining the fixed templates, metadata, residual telescope, and output.
  ErasedFamilyDescent asks for typed proposition comparison below an inserted
  block; it suffices for the actual lower unfolding check and exact replay.
  ProofErasureApplicationSingleton discharges this interface with ApplicationCompare
  and retains typed source realizations. ProofErasureRecursiveSingletonStages
  integrates the upgraded general primitive at every stage, embeds every prior
  application stage at its original bound, and proves arbitrary indexed-prefix
  forward computation when supplied the new family guard. Descent and operational
  replay hold throughout. This repairs the integration mismatch, not completeness,
  joint re-synthesis, or the unchanged StructureCarrierGuard paired-law boundary.

- **Make application comparison and explicit-carrier checking recurse together.**
  **Unbounded finite grammar, simultaneous descent, and staged computation checked.**
  ProofErasureJointChecking uses one inductive relation with comparison and
  carrier modes. Its recovered application rule invokes joint carrier checking;
  carrier checked/field rules invoke joint comparison. Arbitrarily many such
  alternations are permitted in a finite certificate. All old scoped/application
  comparisons and old carrier guards embed. ProofErasureJointDescent proves
  simultaneous block descent, including dependent projection recipes and fresh
  function applications. JointPrefix and JointStages use this grammar throughout
  general singleton families and specialized Eq carriers; all preceding recursive
  singleton stages embed at the same bounds and operational replay is preserved.
- **Repair the actual neutral-application paired-instantiation witness.**
  **Strict carrier-language improvement checked at identical computation stages.**
  ProofErasureJointExample gives a stage-zero joint carrier at Prop for f x/f y
  with distinct positive empty-structure variables. Old StructureCarrierGuard
  still rejects these endpoints at every ErasedJointStage, since its internal
  ScopedCompare retains neutral-argument injectivity. This refutes the claim
  that more computation alone fixes the old grammar, and shows the new grammar
  fixes this witness. It does not establish unrestricted paired instantiation.
- **Re-state domain re-synthesis for the corrected joint carrier grammar.**
  **Open, with necessary Pi recovery/exposure checked.**
  JointCarrierDomainResynthesis requires a newly recovered Pi and a new joint
  argument guard at its domain after typed diagonal substitution. The older
  ScopedCarrierDomainResynthesis, which mentions StructureCarrierGuard, cannot
  silently discharge this obligation. A fresh-variable/reflexive-argument input
  proves the new law requires Pi recovery of every non-proof function with an
  inhabited domain, and Pi exposure above added function/argument binders.
  No general re-synthesis, paired-substitution closure, or smaller sufficient
  strengthening front has been proved.

- **Use typed primitive simulation for recursive substitution.**
  **Compatible transport checked.** ErasedPrimitiveSubstitutionTo requires
  transport only at actual typed sources, and permits a full target computation.
  ProofErasureTypedComputeSubstitution lifts this to compatible computations,
  using source descent to realize transitive intermediates and source domains
  under binders. No unconditional raw primitive substitution premise is needed.
- **Supply local typings under every joint-checking constructor.**
  **Full conditional joint transport checked.** Source reflection aligns lambda
  bodies and inferred applications. ProofErasureJointFieldRealization obtains
  actual common typings for projections and retained constructor fields from
  equality of their majors, typed expansion, and projection reduction.
  ProofErasureJointSubstitution covers every JointCheck constructor by one
  induction. Given source descent, primitive inclusion, source-typed primitive
  simulation into Target, and JointCarrierDomainResynthesis Target Target, it
  transports common-typed comparisons and explicit-carrier checks. Inferred
  non-proof endpoints may start with independent types. Re-synthesis is used
  at appCarrier; no separate field/binder realization assumption is added.
  The target relation can be a union larger than the source stage. Actual
  joint-stage primitive simulation and the re-synthesis law remain unproved;
  this is not unconditional substitution closure or a strengthening front.

- **Close actual joint-stage substitution without assuming primitive closure.**
  **Conditional finite-stage transport checked; re-synthesis remains open.**
  ProofErasureJointUnion proves finite bounds for the complete mutually recursive
  checker and closes the joint stage union under its own singleton and Eq guards.
  ProofErasureJointPrimitiveSubstitution transports the actual generated family
  guard under its residual telescope and preserves the literal generated output;
  specialized Eq prefixes retain their exact proof-domain lambda. Stage induction
  in ProofErasureJointUnionSubstitution discharges typed primitive simulation
  into the union from preceding-stage simulation. Thus canonical Eq, sound core
  definitions, and JointCarrierDomainResynthesis at the union imply finite-later-
  stage substitution of computations, common/inferred comparisons, and carriers.
  There is no primitive-substitution assumption left in these concrete results.
  This proves sufficiency for substitution only, not re-synthesis, heterogeneous
  paired closure, coverage/confluence, or a smaller sufficient strengthening front.

- **Test whether joint Pi re-synthesis avoids universe recovery.**
  **It does not; a literal-sort strengthening fragment is necessary.**
  ProofErasureJointSortExposure tests re-synthesis on a non-proof lambda returning
  a Pi whose domain is an arbitrary type. Recovery inversion forces a sort for
  that domain under one inhabited dummy binder, with no initial recovery premise.
  A fresh variable declared at T then forces computation from the twice-lifted
  erasure of every T convertible to a sort. These are contextual computations;
  no untyped retraction is used. With primitive descent, front-block insertion
  can include both fresh binders in one block, proving literal-sort strengthening
  below the entire block. The result does not cover arbitrary insertion depth,
  and no reduction of PropFront to this fragment is known here. Re-synthesis
  therefore includes a universe-exposure obligation as well as its already
  checked Pi-exposure obligation; it is not merely argument-guard transport.

- **Test quotient-prefix coverage in the actual joint stages.**
  **The old concrete re-synthesis premise is refuted; the omitted rule is repaired.**
  ProofErasureJointQuotBoundary constructs a well-formed context and an actual
  type T : Type with T definitionally equal to Prop, using Quot.lift at source
  universe zero and the constant function returning Prop. Its major is a proof
  and erases to the proof marker. Every finite joint stage based on
  ErasedCore.definitions fixes the entire erased source, including after any
  front lift and at any raw context. Ordinary iota cannot match the marker;
  Quot.lift has no recursor-registry entry, so neither general singleton nor
  specialized Eq prefixes repair it. Thus JointCarrierDomainResynthesis with
  this recovery union is false whenever canonical Eq and Quot are present,
  independently of the carrier comparison relation. All actual stored and
  selected structure equations were included. This is not a strengthening
  counterexample. ProofErasureJointQuotRepair adds the existing proved closed
  Quot.lift equation to the parameterized core, preserves its old equations
  and soundness, and covers every actual quotient prefix at stage zero. The
  identical witness now computes to Prop at stage zero. The generic joint
  grammar and conditional substitution results accept this new core unchanged;
  their re-synthesis premise remains open for it. Future re-synthesis work in
  environments with Quot must use ErasedQuotCore.definitions (or a collection
  containing the same equation), not the refuted old concrete instance.

- **Preserve ordinary confluence when restoring quotient prefixes.**
  **Proved for the repaired ordinary core, including typed erasures.**
  ProofErasureQuotCoreConfluence shows that the added closed Quot.lift equation
  preserves fixed-universe declaration determinism and rigid-head separation.
  A typed ordinary pattern at that head requires a nonzero source universe,
  whereas the added equation requires the same universe to equal zero. Thus
  every typed ordinary path still translates to SeparatedPatternCompute, whose
  raw confluence yields an exact join. Replay and forward erasure give exact
  typed-source confluence for ErasedQuotCore.Step. This removes the confluence
  regression risk from the quotient repair; it does not establish confluence
  for arbitrary joint singleton stages or discharge joint re-synthesis.

- **Separate binder-insertion transport from arbitrary substitution re-synthesis.**
  **Proved for every concrete joint stage and its union.** Exact interpreted
  variable renamings preserve the context oracle, hence the selected recovered
  type transports structurally, including beneath dependent binders. Actual
  well-formed block insertions supply this invariant without inhabitants of
  the inserted declarations. The entire mutually recursive JointCheck grammar
  transports, with the appCarrier rule retaining both the recovered Pi and
  its carrier guard. General singleton guards transport under their full
  generated residual telescope; specialized Eq prefixes transport directly.
  Stage induction therefore proves exact renaming at the same finite stage,
  for every sound core (including ErasedQuotCore). No joint re-synthesis premise
  or dependency is used. This removes a contextual-transport obligation from
  future joint confluence diagrams. It does not transport beta substitution
  by arbitrary expressions, expose missing types, or prove strengthening.

- **Remove re-synthesis from substitution of proof arguments.**
  **Proved throughout every concrete joint stage, at the same finite bound.**
  Exact ContextRenaming unnecessarily constrains erased proof variables.
  RetainedRenaming requires exact variable/oracle transport only at non-proof
  lookups in typed realizations. It extends beneath arbitrary displayed binders
  and is satisfied by substituting any actual proof for a proposition-valued
  binder. Source-typed replay supplies the types of intermediate computations
  and recovered types, so selected recovery outputs transport exactly. The
  shared JointCheck transport induction then transports the complete carrier
  grammar without re-synthesis. General singleton guards preserve this invariant
  under their full generated telescope, and Eq prefixes use source-typed carrier
  reflection. Stage induction discharges the primitive condition. Computations,
  selected recovery, comparisons at independent proof arguments, and explicit
  carriers all instantiate at the original stage. This handles proof-argument
  beta transport; it does not handle arbitrary non-proof substitution images
  such as the lambda arguments in the original matched-beta residue.

- **Replace non-proof re-synthesis with a literal join of assigned and recovered types.**
  **Refuted for the full joint union, even after the quotient repair.**
  ProofErasureRecoveryJoinBoundary gives an actual typed substitution of Prop
  at a universe syntactically max 1 0: its only recoverable type is Sort 1,
  while computation fixes both literal sorts. The native and assigned types
  already compare at stage zero. ProofErasureEtaRecoveryJoinBoundary removes
  universe syntax as the explanation: in context f : Prop → Prop,
  F : (Prop → Prop) → Type, x : F f, the variable x may be assigned
  F (fun p => f p). Both neutral types are fixed by every joint computation,
  and every recovery of x has its native type F f. They cannot have a literal
  computational join at any stage, but compare at stage zero by eta at the
  argument. Thus universe normalization alone cannot repair the proposed
  invariant. The same example gives an actual typed substitution by a variable
  that fails RetainedRenaming because its oracle assignment changes by eta.
  Joint carrier checking at a literal sort is also proved equivalent in power
  to its ordinary common-mode checking component, allowing raw sort-carrier
  reindexing with endpoint typings still required by sound interpretation.
  This rejects literal type joins and unconstrained variable-image transport;
  it does not refute re-synthesis or canonical-Eq strengthening. Further type
  alignment must retain comparison/conversion evidence, not just computation.

- **Transport guards across the neutral recovered-type join obstructions.**
  **Proved without joins or type-comparison evidence.**
  ProofErasureJointCarrierExposure factors every joint carrier guard into either
  ordinary common-mode endpoint comparison or a computation to a registered
  unindexed structure/Pi carrier, retaining the endpoint guard there. A
  variable-headed application spine cannot expose either shape: computation
  keeps its head/index/arity and supplies paths for its arguments, without
  normality or termination assumptions on those arguments. All guards at such
  carriers therefore yield common-mode comparison and transfer to any newly
  selected carrier (whose endpoint typings are still required for sound use).
  ProofErasureJointNeutralAlignment applies this to the actual eta example:
  x : F f also has assigned type F (fun p => f p), lookup recovers F f at stage
  zero, and the two types have no literal join in the entire union, yet their
  carrier guards are equivalent for every pair of raw endpoints at every finite
  stage. Together with sort_reindex, this bypasses both recent literal-join
  obstructions for guard alignment. General non-proof substitution, recovery
  exposure, and transport at exposed structure/Pi carriers remain open. The
  factorization is not a smaller sufficient strengthening front.

- **Use joint type comparison to expose recovered heads and align empty structures.**
  **Proved from existing comparison certificates.**
  ProofErasureJointRigidExposure excludes all rigid heads from every joint stage
  and the union when the core excludes them; singleton exclusion follows from
  the generated code's actual stored equation. Inferred comparison against an
  inert constant spine exposes the same family and arity on the other side,
  including carrier-aware application rules. ProofErasureJointTypeExposure
  converts either comparison mode between actual sort-typed endpoints into
  inferred mode by typed replay, then transfers empty-structure guards at the
  same quotient-repaired stage. ProofErasureJointRecoveryExposure also exposes
  sorts and Pis; a selected recovery plus a comparison to any of these three
  heads yields a newly selected recovery with that head, without exact domain,
  codomain, universe or parameter syntax. No arbitrary coverage is assumed in
  these constructive lemmas. ProofErasureJointUnitAlignment tests an existing
  empty S : (Prop -> Prop) -> Type: S f and S (fun p => f p) are typed equal and
  fixed by all repaired-union computation, hence have no literal join, yet their
  type comparison supplies target guards at every stage. The example assumes
  the displayed registration; it does not build an environment extension.
  Dependent nonempty-field and general Pi carrier conversion remain open.

- **Package universal compared recovery as the remaining smaller front.**
  **Rejected as a simplification, not refuted as a theorem.**
  ProofErasureJointComparedRecoveryBarrier proves that compared recovery for
  non-proof variables alone already implies the entire PropositionFront under
  the existing primitive descent theorem. Recovery may freely choose its output,
  and the type comparison only needs common mode. In the probe, a fresh variable
  declared at P -> Prop is assigned R -> Prop using the upper equation. Its
  recovered output computes from the declared lookup, so the type comparison
  composes with that path; joint descent removes both fresh binders and Pi
  injectivity returns the desired lower P = R. Thus proving coverage remains a
  live direct route to the main goal, but treating it as a routine subsidiary
  obligation hides the whole original front. No converse or impossibility of
  coverage is claimed, and no strictly smaller sufficient front is obtained.


- **Transport all joint stages through exactly recoverable non-proof images.**
  **Proved conditionally, with a strict-extension witness and a checked limit.**
  RecoveringSubstitution retains typed interpretation but permits arbitrary
  non-proof images when they recover their exact substituted oracle types.
  The invariant extends under binders and residual telescopes. Computation,
  selected recovery, joint comparison and recursive carriers transport through
  both singleton primitive families at stage imageStage + sourceStage, without
  assuming JointCarrierDomainResynthesis. The proposition identity is a native
  stage-zero non-proof lambda image outside RetainedRenaming and therefore
  preserves the body's stage. A displayed beta redex can prefix the transported
  body computation. These are diagonal substitution results, not a theorem for
  two different non-proof images. The earlier eta-converted variable example
  fails even this enlarged invariant with image recovery in the whole union;
  exact recovery is therefore not an unconditional solution to substitution.
  General converted-type alignment and recovery/comparison coverage remain
  open. This supporting result is not a smaller sufficient strengthening front.


- **Use annotation computation to transport joint certificates between contexts.**
  **Contravariant transport proved; exact covariant transport refuted.**
  ProofErasureJointDomainPullback constructs recoverable identity substitutions
  from target-to-source oracle computations. Thus A computing to B lets body
  computations, exact recoveries, joint comparisons and carrier guards under B
  pull back under A, with additive domain/body stages. The actual typed domain
  conversion follows from reflection. ProofErasureJointDomainDirection shows
  that reversing exact recovery already fails for the typed annotation
  (fun X : Type => X) Prop reducing to Prop: the fresh non-proof variable's old
  redex-shaped output cannot be recovered from the new normal sort oracle,
  even in the whole joint union. Binder confluence therefore cannot simply
  reuse exact recovery in both context directions.

- **Allow recovered outputs to compute further when an oracle reduces.**
  **Fresh-variable case proved for the repaired ordinary core.**
  ProofErasureCoreOracleReduction joins the original variable recovery and the
  weakened annotation reduction using typed core confluence. The new oracle
  recovers a shared output to which the original selected output computes.
  Hence a recovered Pi remains exposed, with a possibly different domain and
  codomain. Composite recovery remains a live induction: application needs
  codomain computation under instantiation, projection needs field-recipe
  computation after rigid family-spine reduction, and conversion needs a typed
  confluence join. The result does not give argument guards at the newly chosen
  Pi domain. The guarded joint stages still have no proved confluence or full
  re-synthesis theorem; their extension is not implied by the ordinary-core
  variable result. No smaller sufficient front is claimed.


- **Extend forward oracle-reduction recovery to all expression constructors.**
  **Proved for the repaired ordinary core with source typing.**
  ProofErasureCoreRecoveryReduction transports every ScopedTypeRecovery rule
  when old oracle entries compute pointwise to new entries. The raw expression
  is fixed and its selected output may compute further. The target raw context
  needs no original realization for this certificate result. Application tracks
  both recovered Pi components and substitutes the codomain path; projection
  tracks the actual dependent field recipe through computed family parameters;
  conversion joins two paths using typed core confluence and recovery replay.
  An actual typed-binder wrapper uses context conversion to express the result
  at the body's new-context erasure. Pi recovery records separate computation
  paths for the newly selected domain and codomain. This closes the composite
  recovery task from the preceding entry, not guarded joint-stage confluence or
  arbitrary context conversion.

- **Rebuild the new-domain argument guard for structural subsingletons.**
  **Proved under computational oracle reduction in the repaired ordinary core.**
  ProofErasureCoreCarrierReduction preserves structural subsingleton carriers
  through arbitrary repaired-core paths, including recursive Pi codomains.
  Combined with composite Pi recovery, this chooses a new Pi and a joint guard
  at its newly recovered domain. General field/function guards remain open.
  A live next step is simultaneous forward joint-check/carrier transport with
  computed oracles and computed carriers. The earlier eta no-join examples
  still prevent treating computational alignment as arbitrary type conversion;
  no smaller sufficient strengthening front is claimed.


- **Transport general joint checking and carriers simultaneously through computed contexts and carriers.**
  **Proved for the repaired ordinary core and the full joint grammar.**
  ProofErasureCoreContextReduction combines actual context-conversion
  realizations with pointwise forward oracle computation and extends beneath
  a computed binder annotation. ProofErasureCoreCheckReduction performs one
  induction over all 24 comparison/carrier constructors. Recovered application
  uses the new Pi domain's computation path to invoke its argument-guard IH;
  function carriers change the fresh binder and codomain together; dependent
  nested structure fields compute their actual projection recipes. Typed core
  confluence joins the two carrier paths in carrierCompute. No re-synthesis
  premise is assumed. The endpoints stay fixed, so this does not establish
  stability under arbitrary endpoint reduction or substitution.

- **Align arbitrary joint guards at computationally joined recovered domains.**
  **Proved for the repaired ordinary core, removing the subsingleton restriction.**
  ProofErasureCoreGuardAlignment transports any typed joint carrier guard
  forward along carrier computation and then backward along another path to
  the same reduct. Its context-transport result also chooses a new recovered
  Pi and a joint argument guard at its new domain under computed oracles.
  General function and dependent nonempty-structure carriers are covered in
  this computational setting. Guarded joint stages, arbitrary non-proof
  substitution and arbitrary conversion are not covered; the existing eta
  no-join examples prevent identifying conversion with computational alignment.
  Beta/capture residual transport and guarded-singleton integration remain
  live tasks, with no smaller sufficient strengthening front claimed.


- **Extend full joint checking through a single endpoint beta step in the same repaired core.**
  **Refuted, even when the environment already has PropositionFront.**
  ProofErasureJointEndpointBoundary uses a recursive Pi D and its reflexive
  canonical-Eq cast D'. Common checking compares (diagonal D)(diagonal D)
  with (diagonal D)(diagonal D'), since the functions are identical and common
  lambda checking ignores the argument annotations. Contracting only the right
  endpoint yields (diagonal D')(diagonal D'). Full joint loop readout now forces
  comparison of D and D'; sort-typed inferred checking forces a Pi exposure of
  the cast, contradicted by the full head model. ProofErasureQuotCoreCastBoundary
  includes the repaired quotient equations, and ProofErasureJointLoopReadout
  covers the full joint grammar, including recovered application. The actual
  extension preserves canonical Eq and quotient registration and separately
  satisfies PropositionFront. Thus no strengthening counterexample is claimed.

- **Allow a singleton-stage increase for the endpoint beta obstruction.**
  **Exact witness repaired at stage one; general transport remains open.**
  The reflexive cast computes to its original annotation at repaired joint
  stage one, restoring the resulting loop comparison without normalizing the
  recursive loops. This checks the positive boundary in the same repaired
  definition collection. Same-core endpoint closure cannot be a prerequisite
  for the current transport route. The remaining live alternative is transport
  allowing later joint stages (or their union), together with the recovery and
  guard alignment needed for captured substitutions. No universal later-stage
  endpoint closure, full re-synthesis, or smaller sufficient front is proved.


- **Invert full joint lambda computation while returning bodies to the original binder.**
  **Proved with a finite later stage and typed non-proof source lambda.**
  ProofErasureJointBinderComputation replays intermediate lambdas in transitive
  paths, then pulls their later body computations back along the annotation
  path. The previously proved contravariant domain transport discharges this
  step. Finite-stage extraction synchronizes the resulting annotation and body
  paths. This handles arbitrary joint guards and changing annotations without
  assuming joint confluence, arbitrary substitution, or re-synthesis. Unlike
  the old scoped-prefix inversion, a same-stage bound is not asserted.

- **Close the head-beta/function-argument computation overlap for joint stages.**
  **Proved for exactly recoverable original arguments, with finite stage growth.**
  ProofErasureJointImageComputation observes that computing images through a
  typed template only needs primitive renaming, not primitive substitution.
  It preserves the image-computation stage without any recovery premise.
  ProofErasureJointBetaExchange uses the new binder inversion, instantiates the
  recovered body path at the original argument, replays its body output, then
  computes argument occurrences through that output. The other arm is one beta
  step. No recovery of the computed argument is needed. This is a computational
  overlap, not arbitrary endpoint comparison transport or paired substitution.
  The original non-proof argument's exact assigned-type recovery remains a
  genuine restriction, already known not to follow from arbitrary typing.
  Removing or replacing it and handling guarded primitive overlaps remain live;
  no strictly smaller sufficient front or strengthening proof is claimed.


- **Compute substitution images before requiring exact assigned-type recovery.**
  **Checked for substitution joins, beta overlaps, both joint comparison modes,
  and full joint carrier checks.** ProofErasureJointComputedRecovery first
  replays the computed image as a typed original, applies exact-recovery
  transport there, and computes occurrences of the original image through the
  typed template. Computation endpoints meet at the old output instantiated by
  the computed image; a directed path to the old instantiated output is not
  asserted. Comparison and carrier constructors absorb these computations and
  retain the exact original substituted endpoints and carrier. The finite bound
  is max(argumentStage, recoveryStage + bodyStage).

- **Check whether computed recovery actually enlarges the useful image class.**
  **Strict extension proved for a non-proof lambda; still not arbitrary typing.**
  ProofErasureComputedRecoveryBoundary uses a lambda containing an identity beta
  redex at the syntactic universe max(1,0), assigned the equivalent universe 1.
  Every recovery of the original lambda retains max(1,0), even in the entire
  joint union. Its stage-zero beta reduct recovers the assigned type exactly.
  The eta-converted neutral variable example remains fixed by all computation
  and defeats computed recovery too. Thus reduction repairs some converted
  lambda images but cannot replace comparison-based type alignment in general.
  This is a strict improvement to conditional transport, not a smaller
  sufficient strengthening front or a solution of the matched-beta residue.


- **Align function carriers beyond computational joins by their terminal guard.**
  **Proved for arbitrary finite telescopes with variable-headed terminal results.**
  ProofErasureJointFunctionAlignment defines NeutralResult and replaces only
  the terminal result, retaining every displayed binder domain. Compatible
  computation preserves this class and mirrors all domain computations under
  replacement; neutral argument computations disappear at the replaced leaf.
  Full joint carrier checking then transports by induction, including function
  guards, carrier conversion, symmetry and endpoint computations. No raw type
  comparison or computational join is required. Actual endpoint typings at the
  chosen target carrier remain necessary for sound interpretation.

- **Test neutral-result function alignment on actual eta-converted Pi types.**
  **Checked at every finite joint stage, with no join in the whole union.**
  ProofErasureJointFunctionAlignmentExample puts the existing F f / F (eta f)
  neutral types beneath a shared Prop domain. Both resulting Pi types are
  actually typed and definitionally equal. Their raw forms are distinct and
  fixed by all joint computation, yet their full carrier guards are equivalent
  for all raw endpoints at every stage. This advances the function-carrier
  case beyond the previous neutral and empty-structure cases. It does not
  transport across changed function domains, cover structural terminal results,
  or establish general comparison-based carrier alignment. Those cases still
  require compared-context transport and dependent field-carrier alignment.
  No sufficient strengthening front has been made strictly smaller here.


- **Align nonempty record parameters through persistent neutral field recipes.**
  **Proved for the full joint carrier grammar.**
  ProofErasureJointRecordAlignment states NeutralRecordFields using the actual
  projectionType recipes after every reachable parameter computation, for all
  majors and retained fields. A nested field guard then yields ordinary field
  comparison. The record guard reindexes to any new parameter list of the
  correct length, retaining family and levels. Carrier computation preserves
  the inert family spine and composes parameter paths; projection metadata is
  aligned by its checked uniqueness. Actual target endpoint typings remain a
  separate requirement for sound use. Arbitrary field recipes are not assumed
  to meet this criterion.

- **Test the record criterion on Box A with a retained parameter-dependent field.**
  **Checked for an existing registered one-field Box, including a typed no-join
  eta example.** ProofErasureJointBoxAlignment derives its field recipe from the
  constructor telescope (A : Type) -> A -> Box A. At a variable-headed parameter,
  every reachable recipe is still neutral. The full guards at Box (F f) and
  Box (F (eta f)) are equivalent at each repaired joint stage although those
  typed, equal carriers have no joint-union computational join. Registration,
  constant typing and the constructor shape are explicit hypotheses; no fresh
  registered extension was constructed. Function/structure-headed field types,
  changed function domains and universal compared-type alignment remain open.
  The result is a new alignment case, not a smaller sufficient front.

- **Retain domain comparison when exposing a selected recovered Pi.**
  **Proved, and consumed by the empty-structure application case.**
  ProofErasureJointDomainExposure strengthens head exposure with a common
  comparison between the assigned domain and the newly selected domain.
  Compatible Pi computation preserves a domain computation in the original
  ambient context, so full joint comparison induction can retain this evidence
  without codomain-context transport. Actual recovery replay supplies a new Pi
  typing and upgrades the domain comparison to inferred mode. When the assigned
  domain is an empty registered structure, this supplies the recovered argument
  guard and closes the actual appCarrier rule at the same stage and endpoints.
  The input recovery and assigned-type comparison remain supplied certificates;
  universal variable compared-recovery is already known to imply PropositionFront.
  Codomain comparison would additionally require transport between compared
  binder domains, including the reverse orientation of forallE. This batch
  neither supplies that transport nor makes the sufficient front smaller.

- **Transport recovery through compared binder annotations, comparing new and
  old selected outputs instead of preserving the old output exactly.**
  **Refuted at the repaired ordinary core, already for a fresh non-proof
  variable.** ProofErasureComparedContextBoundary supplies a canonical-Eq,
  quotient-registered recursive extension in which PropositionFront holds but
  JointVariableRecoveryContextComparison fails. The annotations have the same
  actual sort and an inferred joint comparison before the change. Wrapping
  the existing mixed self-application loop comparison in proposition-domain
  Pis keeps the fresh variable non-proof. A selected recovery performs beta
  inside its oracle. The proposed transport would compare the two reduced
  loops, expose their annotations, and incorrectly expose a Pi from the free
  reflexive Eq cast in the ordinary core. This rules out that output-comparison
  invariant, not use-site recovery/guard re-synthesis or transport allowing
  later singleton stages. The raw computational retraction used at the end
  is substitution closure of the core, not inverse typing weakening.

- **Retract a proposition-producing function binder using exact recovery.**
  **Proved at the same finite joint stage for every typed domain.**
  ProofErasureRecoverablePropFunction uses the closed proposition Eq Type Prop
  Prop, whose syntax-directed recovered sort is literally Prop. A constant
  function returning it exactly recovers A -> Prop for arbitrary typed A,
  without any inhabitant or recovery certificate for A. Substitution of this
  stage-zero image removes an unused A -> Prop binder from a joint comparison
  with independently supplied common endpoint typing below. This preserves
  the certificate, not just the declarative equality it denotes.

- **Allow arbitrary stage growth in compared-output context transport.**
  **A stronger necessary consequence is checked; equivalence with the front
  remains unproved.** ProofErasureComparedContextConsequence shows that the
  union version of JointVariableRecoveryContextComparison implies inferred
  type comparison after every finite computation of its right endpoint, in
  the original context, at some later stage. The earlier auxiliary-binder
  argument now works for every universe and full contextual computation;
  exact recovered inhabitants remove its binder without stage increase.
  The existing arbitrary-term beta-composition barrier does not directly
  apply to this sort-typed endpoint law. No implication to PropositionFront,
  converse, or strict reduction of a sufficient strengthening front is claimed.

- **Recover every assigned type before developing a typed identity redex.**
  **Constructive for every typed argument.**
  ProofErasureIdentityRecoveryCover wraps x : A as (fun z : A => z) x.
  The result is typed at A, is equal to x, beta-contracts to it, and exactly
  recovers A whenever non-proof, at stage zero in any computation relation.
  This is a recoverable expansion of x, not a computation from x to a
  recoverable image; no canonical-Eq or recovery-coverage premise is needed.

- **Preserve assigned-type recovery, even up to computational joins, through
  finite developments.** **Refuted by one identity contraction at all stages.**
  ProofErasureRecoveryDevelopmentBoundary applies the expansion to the existing
  eta-converted variable. Before contraction its assigned type recovers exactly.
  Afterwards, even after any joint-union computation, no recovered type has a
  computational join with that assigned type. A stage-zero inferred comparison
  between the assigned and native recovered types still exists. This rules out
  the proposed recovery invariant, not finite developments in general, compared
  recovery, computational confluence, or strengthening.

- **Use recoverable expansions to obtain arbitrary substitution joins from
  typed confluence.** **Conditional theorem proved.**
  ProofErasureJointConfluentInstantiation transports the body computation at the
  identity expansion, then contracts its occurrences. The two requested
  substituted endpoints have a common typed computational ancestor. Assumed
  typed confluence of the joint union gives a common reduct at a finite later
  stage. There is no recovery premise on the original argument, but the result
  gives a join, not a directed substituted path. This does not prove confluence
  and cannot supply its substitution case circularly. Full joint confluence
  and the comparison/guard stability needed for the original goal remain open.


- **Reuse exact operational confluence with the quotient-repaired joint core.**
  **Checked** in `ClosedQuotPrefix` and `QuotPrefixConfluence`. Reabstracting
  the five fresh arguments of `QuotPrefixUnfold.atFive` constructs the actual
  zero-argument checked prefix; generator uniqueness fixes its RHS literally
  to `ClosedQuot.value`. Weakening its empty-context checks works in every
  context. Replacing declaration equations by prefix paths proves that the
  repaired and original actual-prefix relations are literally equivalent,
  without source typing. Existing typed prefix confluence therefore applies
  to the repaired collection, without a normalization or strengthening front.
  This is a presentation bridge, not a new proof of general raw confluence.

- **Use an original beta redex as the substitution peak's common ancestor.**
  **Operational join checked**, in `ProofErasureJointOperationalJoins`. Replay
  the joint body path to an actual path b to b'. The original redex (lambda A
  b) x computes both to b[x] directly and to b'[x] by computing under lambda
  before beta. Repaired prefix confluence joins them, and typed substitution
  proves erasure of b'[x] is exactly the raw output instantiated by erase(x).
  No recovery premise on x, identity expansion, or assumed raw confluence is
  used. The same module joins original representatives of any two finite-stage
  joint paths from one typed source. **Remaining:** the residual actual prefix
  paths have no proved joint certificates. The earlier conditional raw-join
  theorem is not discharged. Next useful target is certificate propagation
  through the existing exact peak constructions, using their input guards;
  unrestricted assigned-type recovery preservation has already been refuted.


- **Reduce guard substitution to beta stability of proposition comparisons.**
  **Conditional reduction checked** in `ProofErasureJointPropBeta`.
  `JointPropBetaStability` restricts the endpoint stability law to P,Q:Prop.
  Assuming it for the full joint union, exact recovery of the identity
  expansion of any x:A permits instantiating a finite proposition comparison;
  beta contraction of the expansion in both endpoints then gives the exact
  desired substituted comparison at a finite later stage. No recovery of x,
  raw computational confluence, or carrier-domain re-synthesis is assumed.
  **Limitation:** the stability law is unproved for the union. This covers
  one top-binder instantiation, not automatically arbitrary simultaneous
  substitution beneath a generated residual telescope.

- **Encode carrier guards by canonical equality propositions.**
  **Checked** in `ProofErasureJointCarrierPropositions`. Every typed guard for
  a,b:A gives a joint comparison of Eq A z a and Eq A z b, for any typed z:A,
  in either comparison mode and at the same stage. Exact recovery of Eq's
  declared argument domain licenses appCarrier; no recovery of A,a,b,z is
  required. Proposition beta stability then conditionally transports this
  encoding through arbitrary typed top-binder instantiation. This is a
  forward encoding only: a carrier decoder and use of the encoded comparison
  as the actual generated family guard are not proved.

- **Avoid the recursive-loop obstruction by restricting endpoint stability
  to propositions.** **Refuted for the repaired ordinary core.** The previous
  mixed-loop fixture already has P,Q:Prop. Refactoring
  `ProofErasureJointEndpointBoundary` proves that proposition-only stability
  would still recover every conversion out of a recursive Pi domain. The
  canonical recursive extension preserves Eq and quotient registration and
  satisfies PropositionFront, yet fails this restricted stability law.
  Existing general-law theorems remain as wrappers. This does not refute
  full-union stability: the known cast repair at joint stage one remains.
  Thus the restriction does not by itself produce a smaller sufficient front.


- **Expand all images of a dependent substitution with exact recovery.**
  **Checked unconditionally** in `ProofErasureRecoveringCover`. Induction on
  the source context builds the older images first. Each new image is an
  identity wrapper whose annotation uses those already expanded older images;
  forward paired substitution converts the original image to this exact type.
  The resulting substitution is definitionally equal to the original and has
  exact recovery for every retained image in any primitive relation. Every
  image beta contracts to its original image, including proof images. This
  does not claim recovery survives contraction.

- **Extend proposition beta stability through actual generated telescopes.**
  **Conditional substitution checked** in `ProofErasureJointPropSubstitution`
  and `ProofErasureJointPropSingleton`. The dependent recovering cover removes
  the earlier top-binder restriction: union proposition comparison now survives
  every typed simultaneous substitution under the same unproved proposition
  beta-stability premise. Applying this to the two typed family propositions
  under the entire generated residual telescope transports the general
  singleton guard, its literal output, and its typed source. The target is an
  actual step of the existing joint union, by finite guard extraction. No
  primitive-substitution or domain re-synthesis premise is used. Specialized
  carrier-guarded Eq primitives remain outside this theorem. A next concrete
  target is identifying their encoded Eq proposition comparison with the
  actual generated family guard, avoiding a general carrier decoder. The
  proposition beta-stability premise itself remains open for the full union.

- **Identify the carrier encoding with the actual canonical Eq family guard.**
  **Checked without beta stability** in `CanonicalEqFamilyGuard` and
  `ProofErasureJointEqGeneral`. Registered metadata fixes the extraction family
  to Eq at its original universe and its sole constructor index to the second
  parameter. The reconstructed family is literally Eq A a a; the requested
  family is Eq A a b, both opened under the fresh proof major. The earlier
  carrier encoding supplies exactly this guard. Every specialized Eq primitive
  at a typed source is consequently an actual general singleton primitive with
  identical raw endpoints. This uses Eq registry agreement, not a decoder for
  arbitrary proposition comparisons or assigned-type recovery.

- **Complete directed joint substitution and the head-beta exchange using
  proposition beta stability.** **Conditional theorems checked** in
  `ProofErasureJointBetaSubstitution`. Replacing specialized Eq steps by their
  general singleton presentation closes the last primitive branch. Existing
  compatible typed substitution then handles the entire union. Lambda inversion
  and image computation give the exact head-beta residual even when both the
  annotation and argument compute, with no argument-recovery premise. The
  proposition beta-stability hypothesis remains unproved. This is not yet
  global joint confluence, completeness, or a smaller sufficient front.

- **Use computational substitution to remove the direction restriction on
  binder-context transport.** **Conditional theorem checked** in
  `ProofErasureJointContextBeta`. A typed raw source and an interpreted context
  substitution suffice for exact transport of the full path. Applying this to
  identity substitution along arbitrary original context conversion preserves
  both raw endpoints, in either direction. The premise remains proposition
  beta stability. This does not transport exact type recovery or arbitrary
  joint comparison, so it does not contradict the earlier recovery barriers.

- **Assemble full lambda-path joins from joins of the original components.**
  **Conditional theorem checked** in `ProofErasureJointLambdaJoins`. Inversion
  gives annotation and body paths in their original contexts. Component joins
  are then assembled after realizing the output annotation and body and
  transporting each body residual to its own output context. Only confluence
  at the two fixed original component sources is assumed, in addition to
  proposition beta stability; global confluence is not assumed. This closes
  the changing-binder lambda assembly case. It does not settle primitive
  overlaps, stability of guards under full computation, or a well-founded
  construction of joins for all terms.

- **Transport an arbitrary joint singleton guard after argument beta.**
  **Conditional theorem checked** in `ProofErasureJointPropContext` and
  `ProofErasureJointSingletonBeta`. One-sided proposition beta stability gives
  independent endpoint residuals by beta replay. Its substitution consequence
  also transports proposition comparisons along arbitrary converted contexts.
  Supplied-argument beta computes the two actual family templates under the
  old residual telescope; the two results then move to the new telescope.
  Thus the new family guard follows from the same proposition beta-stability
  premise, without an additional guard-completeness or recovery assumption.

- **Close actual singleton/beta root peaks, not just their operational images.**
  **Conditional exact residual checked** in
  `ProofErasureJointSingletonBetaResidual`. Replay raw argument beta, regenerate
  the same prefix code, transport its guard, and use beta congruence of the
  entire generated program. The reduced raw source has an actual general
  joint singleton primitive to a beta reduct of the old output. Constant-spine
  inversion covers every finite beta path from the source. Specialized Eq
  steps use their general singleton presentation, with registry agreement.

- **Cover all ordinary primitive/beta roots syntactically.** **Unconditional
  raw theorem checked** in `ProofErasurePrimitiveBetaResidual`. Beta preserves
  each visible pattern match and reduces its captures pointwise. Declaration,
  projection, selection, capture application, and fixed-template primitives
  consequently all retain one primitive residual and beta-related outputs.
  No source typing, declaration soundness, confluence, or concrete-pattern
  completeness is required for this raw result.

- **Combine all primitive branches into one beta residual interface.**
  **Conditional theorem checked** in `ProofErasureJointPrimitiveBetaResidual`.
  Every joint-union primitive at a typed source, competing with any finite beta
  path, has one primitive residual whose output is a beta reduct of the old
  output. Canonical Eq, sound declarations, Eq registry agreement and full-union
  proposition beta stability suffice. This is not arbitrary compatible-path
  commutation or global confluence. A root-beta contraction may duplicate
  pending argument computation, so simply iterating root diagrams is not a
  justified proof of the path theorem. Parallel reduction/developments remains
  the live route to that lifting; proposition beta stability remains unproved.

- **Retain one parallel beta step while moving past computation.**
  **Raw infrastructure and exact typed replay checked** in
  `ProofErasureParallelBeta`, `ProofErasureParallelBetaReplay`,
  `ProofErasureParallelBetaStrip`, and `ProofErasureParallelPrimitiveResidual`.
  Parallel beta develops selected source redexes, with parallel body and
  argument development at contracted roots. Simultaneous substitution copies
  the selected developments; the complete-development triangle gives its
  diamond without normalization. Original ComputePar with empty declarations
  replays and erases exactly one step, including proof markers and changed
  binder annotations. The original parallel strip theorem therefore gives a
  single parallel residual across a finite typed beta path. Ordinary primitive
  residuals also retain one parallel output step, with no typing or stability
  premise. This supplies the step control missing from the earlier arbitrary
  finite-beta residual theorem.

- **Strengthen all joint primitive residuals to parallel beta.**
  **Conditional theorem checked** in `ProofErasureJointParallelSingleton` and
  `ProofErasureJointParallelPrimitive`. Exact parallel argument replay and
  parallel congruence of generated programs retain one parallel step between
  the old and new outputs. The existing proposition beta-stability premise
  transports the family guard using serialization of argument developments.
  Specialized Eq again uses its general singleton presentation. Every typed
  joint primitive now has a single parallel residual; no additional guard
  stability or confluence premise is introduced.

- **Lift beta residuals to arbitrary compatible joint paths.**
  **Conditional full commutation proved** in `ProofErasureJointParallelStrip`
  and `ProofErasureJointBetaCommutation`. Induction on a full joint path moves
  one parallel development across it. Typed replay supplies each sequential
  intermediate; proposition-derived context transport handles the two binder
  cases. In the application/root-beta case, component residuals and lambda
  inversion supply the inputs to the previously checked exact head-beta
  exchange, so argument duplication needs no recovery premise or fixed stage
  bound. Serializing an arbitrary beta path then proves joint/beta commutation:
  the joint output has a beta path to a common term, and the beta output has an
  actual joint path to it. Finite-stage input admits a finite later-stage
  residual. This closes the path-lifting gap, not proposition beta stability
  itself or confluence of two arbitrary joint paths. The stability premise is
  used in primitive guard and context/substitution transport, so this result
  cannot establish it circularly.

- **Decode canonical Eq comparisons at literal sort carriers.** **Checked** in
  `ProofErasureJointEqDecode`. Native recovery of `Eq` and its first two
  applications is fixed syntactically when the carrier is a literal sort.
  Thus inferred comparison of two primitive-inert Eq spines gives ordinary
  common comparison of their final arguments; typed sort endpoints extend
  this to either mode. The initial endpoints and universes may differ in the
  raw theorem. No beta stability, confluence or argument recovery is assumed.
  This decoder does not cover arbitrary computational carrier expressions.

- **Replace proposition beta stability by diagonal equality propositions.**
  **Rejected as a strict reduction** by `joint_eq_prop_beta_stability_iff`.
  Even restricting to comparisons of `Eq Prop P P` with `Eq Prop P Q`, and
  beta reduction of Q alone, retains the entire proposition beta-stability
  obligation. The existing carrier encoding and the new sort decoder are
  independent of that stability assumption.

- **Restrict stability to the actual Eq family guard under its fresh major.**
  **Rejected as a strict reduction** by
  `joint_eq_prop_family_beta_stability_iff` in
  `ProofErasureJointEqGuardBetaBoundary`. This includes the changing context
  `Eq Prop P Q :: Γ` and is exactly the Prop-carrier family-comparison shape
  described by `eqRec_family_guard_iff`. For the reverse direction, the input
  lower comparison reflects to definitional equality; beta subject reduction
  then supplies an explicit proof of the new major type. Proof substitution
  removes that binder from the transported guard, and the decoder recovers
  the lower proposition comparison. No inverse weakening is used. Hypotheses
  are canonical Eq, sound declarations and explicit exclusion of Eq unfolding.
  Soundness alone is not used to infer the exclusion. This rules out a guard-
  restriction shortcut, not a constructive proof of beta stability itself.

- **Induct on the source stage rather than assume full-union beta stability.**
  **Partially realized** in `ProofErasureJointStageBetaTransport` and
  `ProofErasureJointStageSubstitution`. Two-sided beta transport from stage n
  into the union suffices for arbitrary simultaneous substitution of stage
  n+1 computations. Recoverable image expansions use stage-zero recovery and
  leave the source comparison at n. Both endpoints contract in one invocation,
  avoiding a second stability call on a target certificate. Substitution plus
  extra endpoint beta and converted-context beta are also combined in one
  source-stage call. The family of these stage laws is proved equivalent to
  full-union stability; no individual stage law is asserted without a premise.

- **Preserve the source relation while encoding specialized Eq guards.**
  **Checked by generalizing** `ProofErasureJointEqGeneral`. Renaming within
  the source relation is enough for the actual family encoding. Typed replay
  also gives the specialized-prefix-to-general-singleton presentation in that
  same relation. The full-union APIs remain as specializations. Generalizing
  `ProofErasureJointPropSingleton` to directed proposition substitution then
  transports generated guards and primitives into a distinct target relation.

- **Instantiate a lambda computation before body-path stage inflation.**
  **Checked** in `ProofErasureLambdaInstantiation`. Realize each intermediate
  lambda, convert the fixed argument forward to its actual domain, and
  instantiate that segment's body computation. Only substitution of the
  original source relation is needed. There is no common-domain pullback or
  exact argument recovery. `ProofErasureJointStageBetaExchange` consequently
  closes stage-n+1 head-beta/function/argument peaks from stage-n proposition
  transport, including changes to the lambda annotation and duplication of
  the computed argument.

- **Use these lower-stage laws directly in the existing parallel strip proof.**
  **Still incomplete at a precise point.** Its application/root-beta case
  first constructs component residuals in the target union and then
  instantiates the residual lambda path. The source-stage substitution law
  cannot apply to an arbitrary target residual. The new direct lambda theorem
  fixes inflation while instantiating an original source path, but does not
  retain the originating source derivation of such a component residual.
  A simultaneous residual/substitution construction retaining that derivation
  remains live. Also needed is the source-stage-zero-to-union comparison case;
  the known failure with the ordinary core as target does not refute this case.

- **Carry substitution closure on each residual primitive.** **Checked** in
  `ProofErasureStablePrimitives`. An enriched primitive is an actual step plus
  an actual primitive after every interpreted context substitution. Context
  interpretations compose by forward typed substitution, so this subtype is
  itself substitution closed. It introduces no new primitive equality. The
  preceding stage-substitution proof was sharpened to retain one actual
  primitive; lower-stage beta transport therefore embeds every typed source
  primitive and source path in this enriched relation. This assertion concerns
  source paths, not yet their beta residuals.

- **Lift local parallel squares into a substitution-closed target.**
  **Checked** in `ProofErasureSubstitutableParallelStrip`. The source and
  target relations remain distinct. Typed source replay handles sequential
  composition. Target substitution and context conversion handle binders.
  At an application/root-beta peak, invert the target lambda residual in its
  initial domain, instantiate its body at the replayed beta argument, and
  compute the argument through the typed residual body. No beta-stability
  assumption about target certificates is required. The shared output still
  has one parallel beta step from the original output.

- **Use the enriched target for actual source stages.** **Local obligation
  isolated, core case checked** in `ProofErasureJointStableParallelResidual`.
  `JointStageStableParallelResidual` asks actual primitive beta residuals to
  retain substitution certificates. Stage zero has the property syntactically.
  The generic strip theorem then covers a full source-stage path against one
  parallel beta development. Nonzero singleton/Eq primitive certification
  remains open; the proposed construction must combine the original guard's
  beta and substitution transport before discarding its source stage. Further
  beta iterations also need retained primitive origins or an additional
  proved residual-closure property: substitution stability alone does not
  give beta closure of the enriched target. No smaller sufficient front for
  strengthening is claimed.

- **Certify singleton/Eq beta residuals from their original lower-stage
  guards.** **Checked**, closing the nonzero local obligation left immediately
  above. `ProofErasureStableFamilyBeta` applies the original stage-n comparison
  to beta-reduced endpoints and all future typed substitutions; substitution
  composition carries this certificate across the changed residual context.
  Generic family substitution and parallel residual proofs retain this richer
  comparator. Forgetting the certificate gives the actual union guard, while
  transporting it gives one actual union primitive at every substituted pair
  of endpoints. Specialized Eq roots first use their exact general singleton
  presentation at the original guard stage. Thus
  `joint_stage_stable_parallel_residual_of_lower_beta` and
  `proofErase_joint_stage_parallel_strip_of_lower_beta` handle every stage-n+1
  primitive/path against one parallel development using only stage-n beta
  transport. No full-union target stability is assumed. This is conditional
  progress, not a smaller sufficient front or a strengthening proof.

- **Retain future beta paths as well as substitutions in family certificates.**
  **Live next step, not yet implemented.** The present certificate quantifies
  over future typed substitutions but discards beta closure. Enrich it to
  retain comparisons after arbitrary future beta paths on both substituted
  endpoints. The original lower-stage `subst_beta_stage` theorem appears to
  supply these certificates by composing the beta paths before transporting
  the original guard. A target relation consisting of ordinary core primitives
  and general singletons with those certificates could then be closed under
  both substitution and parallel residuals. That would allow iteration of the
  strip theorem without feeding arbitrary union comparisons back into the
  lower-stage hypothesis. The comparison beta law, including its stage-zero
  case into the union, would still require a separate argument.

- **Retain future beta paths as well as substitutions in family certificates.**
  **Checked**, resolving the iteration gap in the preceding entry.
  `ProofErasureBetaStableFamily` quantifies over both endpoint beta paths after
  every interpreted substitution. Beta paths compose and substitutions compose,
  including beta redexes created by substitution. Lower-stage transport supplies
  the certificate using the original finite-stage guard; no enlarged target
  guard is fed back into that hypothesis.

- **Iterate within a certified subset of the existing union.** **Checked** in
  `ProofErasureBetaStableJoint`. The subset consists of core primitives and
  general singletons carrying the stronger family certificates. Forgetting
  certificates gives an actual union primitive. The subset is closed under
  interpreted substitution and has primitive parallel residuals in itself.
  The generic strip therefore has the same enriched relation as source and
  target, and finite iteration becomes valid. This is a restriction used to
  retain evidence, not a new computation rule or an assumed closure law for
  the whole union.

- **Close finite computation/beta commutation from a strictly lower guard
  stage.** **Checked** in `ProofErasureJointStageBetaCommutation`.
  Every stage-n+1 primitive, including specialized Eq, has a parallel residual
  in the enriched relation from stage-n proposition beta transport. An initial
  reflexive parallel development equips a whole source path with certificates;
  arbitrary subsequent beta steps can then be iterated. The exact residual
  embeds in a finite later joint stage. Stage-zero computation needs no beta
  transport premise. This removes both the local residual and finite-iteration
  gaps from this computation route, but does not prove proposition comparison
  transport or a strictly smaller sufficient strengthening front.

- **Use the computation result in a source-stage comparison induction.**
  **Next unproved task.** `JointCheck.compute` and `carrierReduce` expose finite
  computation prefixes; the new theorem can commute those prefixes with beta
  using only lower-stage guard transport. This does not automatically handle
  the remaining syntactic comparison cases: beta at application heads must
  preserve a comparison through body instantiation, and carrier recovery and
  lambda-domain comparison carry information beyond computation endpoints.
  The stage-zero comparison law into the joint union remains open as well.
  Establish a simultaneous comparison/carrier invariant rather than applying
  the computation theorem as though it already proved comparison stability.

- **Extend proposition beta transport to general common-mode comparisons for
  a simultaneous induction.** **Refuted even with a larger target union** in
  `ProofErasureJointCommonBetaBoundary`. Let S be a registered positive empty
  structure and x,y distinct variables at S. At stage zero, the two applications
  `(fun z : S => z) x` and `(fun z : S => z) y` compare using recovered carrier
  checking of x,y. Beta gives the bare variables. A new joint bvar-injectivity
  theorem proves that they cannot compare in either mode under any primitive
  relation obeying the existing head restriction, hence not in the whole joint
  union. The two-variable context is constructed from the closed typing of S.
  Their actual carrier guard at S survives. Two uses of one-sided stability
  would give the forbidden comparison, so general common-mode stability of the
  union is false as well. This is stronger than the earlier same-core cast
  obstruction: stage growth cannot fix it, and no recursion or cast is needed.
  It does not refute the proposition-only law or declarative strengthening.

- **Keep carrier output in the beta induction for arbitrary terms.** **Live,
  not proved.** The preceding checked peak forces this change of invariant.
  Type/proposition conclusions may still demand common/inferred comparison;
  ordinary term conclusions must allow a carrier guard at the relevant type.
  The identity peak already has that guard. A simultaneous comparison/carrier
  proof must still justify application, substitution and conversion of supplied
  carriers, rather than silently turning a carrier guard into ordinary common
  comparison. The new computation commutation theorems remain available for
  finite computation-prefix cases. No claim of a smaller sufficient front is
  made by this candidate invariant.

- **Formulate typed beta transport with carrier-preserving output.**
  **Interface and proposition consequence checked** in
  `ProofErasureJointCarrierBetaResidual`. JointCarrierBetaResidual retains an
  actual guard at the original supplied carrier after both finite endpoint
  beta paths. JointCarrierBetaTransport names the still-missing global law for
  typed input carrier guards. Its literal-Prop instance recovers exactly
  JointPropBetaTransport using carrierChecked on input and sort_checked on
  output. It does not imply the false general common-mode conclusion and is
  not claimed to be a smaller sufficient strengthening front.

- **Discharge recursive carrier cases using the new computation commutation.**
  **Checked cases:** subsingleton carriers, symmetry, function carriers given
  their body residual, a fixed target computation of the carrier, reflexive
  typed comparison, and two finite endpoint-computation prefixes given the
  inner residual. Prefixes at stage n+1 use only stage-n proposition transport;
  core prefixes need none. The body/function result uses beta under lift and
  application to the same eta argument. The unit identity obstruction is
  handled by its subsingleton carrier instead of ordinary common comparison.
  These are constructor-case lemmas, not a proof of the global transport law.

- **Handle application domains and changing dependent field carriers.**
  **Remaining live task.** An ordinary-term residual cannot simply be used as
  the inferred function comparison required by app/appCarrier. A replacement
  must retain enough type/domain information, or eliminate the application
  before requesting that comparison. For carrierNested, the field carrier is
  computed from the new left major, whereas the current endpoint residual
  retains the old supplied carrier. Carrier-computation pullback alone goes in
  the wrong direction to replace that old field carrier by its beta reduct.
  Simultaneous carrier/context transport or an invariant retaining the original
  dependent derivation must be tested; the endpoint-only residual property
  does not silently settle this. The earlier Eq-sort decoder handles literal
  universes only and must not be treated as a general carrier decoder.

- **Allow the supplied carrier to beta-reduce with the endpoints.**
  **Local cases checked** in `ProofErasureJointDependentCarrierBeta`.
  JointCarrierTypeBetaResidual strengthens the previous endpoint-only property
  and specializes back to it. The actual projectionType recipe beta-reduces
  when its parameters and left major do; this includes all preceding dependent
  fields. Consequently carrierNested reconstructs every field guard at the
  new parameters and new left major under the stronger recursive hypothesis.
  Subsingleton, symmetry, reflexive endpoints and endpoint-computation prefixes
  also preserve this property. This is not a global carrier-transport proof.

- **Commute carrier computation instead of reversing it.** **Checked.**
  Given an old carrier computation A -> B and a requested beta path A -> A',
  the finite commutation theorem supplies B ->beta C and A' ->compute C.
  Apply the recursive carrier/type residual at C, then wrap it by actual
  carrierCompute at A'. Stage-n+1 carrier computation needs only stage-n
  proposition transport; the stage-zero case needs none. This resolves the
  orientation problem recorded in the previous entry without inverting a path.

- **Recover through forward beta changes of context oracles.** **Checked** in
  `ProofErasureJointOracleBetaTransport`. Under an interpreted identity context
  change and pointwise beta reduction of oracle entries, every source-typed
  stage-n+1 recovery has a recovery in the certified target, with a pure beta
  path from its old selected type to the new selected type. Conversion forks
  use lower-stage computation commutation, and the target computation moves
  to the new context through its existing substitution certificate. Application
  recovery keeps beta-reduced Pi components; projection recovery uses the exact
  dependent recipe theorem. Stage-zero recovery needs no proposition transport.
  A typed binder-domain beta specialization preserves the original expression
  and gives its erasure in the actual new context. This changes the oracle,
  not the recovered expression; arbitrary expression-beta recovery remains
  outside the claim, as required by the earlier exact-recovery counterexamples.

- **Combine context-oracle beta with carrier-type transport before endpoint
  beta.** **Live next construction.** The new recovery result supplies the
  changed native Pi at a fixed application expression. A simultaneous context
  and carrier-type transport proof for JointCheck could use the recursive
  carrier guard at the beta-reduced selected domain, retaining ordinary
  comparison modes while the expressions stay fixed. Entering a beta-reduced
  binder needs an interpreted identity between A :: Δ and A' :: Δ', together
  with the new oracle beta paths; typed forward substitution and beta replay
  are candidates for constructing this extension. This context-only stage
  must not be mistaken for general endpoint beta comparison, which the unit
  example refutes. Application head-beta and paired body instantiation remain
  separate tasks. No smaller sufficient strengthening front is claimed.

- **Simultaneous context-oracle and carrier-type beta transport for all joint
  constructors.** **Proved, under strictly lower-stage proposition beta
  transport; unconditional at source stage zero.**
  `ProofErasureContextOracleBeta` constructs identity context interpretation
  beneath a beta-reduced binder using forward beta replay at each realized
  source domain. It also transports the domain-sort witness and all oracle
  entries. `ProofErasureJointCheckingOracleBeta` completes the mutual induction
  over the full JointCheck grammar with fixed expression endpoints and a
  beta-reduced carrier. In appCarrier, forward oracle recovery supplies a new
  Pi and a pure beta path of its domain; the recursive carrier hypothesis
  applies at that domain. In carrierFunction the context extension changes
  the binder and the recursive carrier changes the codomain. In carrierNested
  the dependent projection recipe beta-reduces with its parameters. Carrier
  computation uses a directed commutation square, and ordinary comparison
  computation uses the existing exact typed substitution theorem. Thus this
  is the full formerly proposed context/type transport construction, not
  another application re-synthesis assumption. The target is the existing
  union. At n+1 only stage-n proposition beta transport is needed, and no
  target-stage guard is fed back into that hypothesis. A specialization gives
  comparison in the actual context after reducing a typed binder domain;
  another reduces a typed carrier in the unchanged context. Endpoint beta
  transport, paired body instantiation and the proposition front remain open.
  No strictly smaller sufficient strengthening obligation is claimed.

- **Retain certified primitives through the whole checking transport, rather
  than forgetting them into the union.** **Proved.** The previous context/type
  theorem could not be reapplied to its union output using only the original
  lower-stage hypothesis. `ProofErasureJointStageCertification` now embeds
  every typed stage-n+1 primitive and path in ErasedBetaStableJoint at its exact
  original endpoints. In the singleton case a reflexive parallel development
  supplies the stronger guard, and deterministic telescope evaluation identifies
  the residual output with the original output. Typed path substitution extends
  this through sequential intermediates and binders. The existing finite-beta
  commutation theorem now uses this exact embedding directly, eliminating its
  preliminary reflexive-strip output reduction. `ProofErasureJointCertifiedChecking`
  proves recovery and the full comparison/carrier context-type transport with
  certified source and certified target, without a proposition beta hypothesis.
  It also upgrades the original finite-stage transport to certified output,
  using only strictly lower-stage proposition beta transport (none at zero).
  Hence both modes and carrier guards can retain exact endpoints and future
  context/type transport. Endpoint beta stability itself is not established.

- **Bootstrap finite stages from proposition beta transport on certified
  comparisons alone.** **Equivalence proved; not a smaller front.**
  `joint_prop_beta_transport_certified_iff` proves that two-sided proposition
  endpoint beta from ErasedBetaStableJoint to the union is equivalent to
  JointPropBetaStability of the union. The forward implication inducts on the
  source stage: stage zero certifies unconditionally, and at n+1 the induction
  hypothesis certifies the input comparison before applying the supplied law.
  The reverse implication uses certified primitive inclusion. This moves the
  remaining proof to one source relation with unconditional exact substitution,
  finite beta commutation, and full context/type transport, while honestly
  retaining the entire original endpoint obligation. A same-mode induction on
  arbitrary function comparisons is still refuted by the unit example. The
  next attempt must retain explicit carriers through application and paired
  body instantiation, potentially tracking a typed elimination spine whose
  final result is a universe; no such spine theorem is assumed here.

- **Use inferred function comparison to close paired head beta at proof
  arguments.** **Proved, including changing computation annotations and erased
  eta.** `ProofErasureJointProofHeadBeta` inducts over a full JointCheck
  certificate whose mode is inferred and whose endpoints are displayed
  lambdas. This rules out common-mode lambda-common and eta-body constructors;
  app/projection/type heads cannot be the displayed lambda endpoints. The
  surviving lambda cases instantiate their body comparisons by retained proof
  substitution. Typed Pi injectivity shows that each actual displayed domain
  is a proposition even when its syntax differs from the assigned domain.
  Both raw eta forms contract after substitution of the proof marker. In the
  computation case, typed lambda inversion returns body paths in the original
  annotation contexts; exact primitive substitution instantiates those paths,
  and source replay supplies the intermediate lambdas for the induction.
  Thus the conclusion compares the two contracted bodies directly, without
  appealing to any endpoint-beta stability law. Actual proposition-valued
  applications may use different proofs of the shared proposition. The
  certified relation stays certified without Hbeta, and source zero stays at
  zero. Stage n+1 uses only stage-n transport to certify the inferred function
  input. This closes the displayed-lambda/proof-argument head-beta critical
  pair, not all beta reductions of proposition applications. The non-proof
  paired-image case and further beta paths inside the resulting bodies remain
  open. Simply dropping the proof restriction for arbitrary result types is
  already refuted by the unit identity example.

- **Carry exact recovery at both displayed lambda domains through diagonal
  head beta.** **Proved, including non-proof arguments and typed erased eta.**
  `ProofErasureJointRecoveredHeadBeta` generalizes the inferred-lambda proof to
  an arbitrary supplied argument. A retained argument explicitly recovers both
  displayed domains. Lambda body substitution consumes the left recovery;
  computation extends both recoveries by its directed domain paths, and
  symmetry exchanges them. The erased proof-marker eta case is handled using
  the actual typed short endpoint: erasure reflection aligns its function type,
  and forward substitution of the supplied argument into the hidden proof
  shows that the argument must itself erase to proof. Thus neither proof
  inhabitation nor inverse weakening is assumed. Actual proposition applications
  may use different original arguments with equal erasure. A further theorem
  allows different erasures when both beta-reduce to a typed shared image that
  recovers both displayed domains. The output stays certified when the source
  is certified, without any endpoint-beta law; finite source comparisons use
  lower-stage transport only to enter the certified relation. The previous
  proof-argument theorem is now a corollary, eliminating the duplicate induction.
  These exact-recovery premises are local evidence, not asserted coverage:
  the eta-converted neutral-oracle boundary still forbids deducing them merely
  from ordinary assigned typings. General carrier-compared paired images need
  not have a literal join. Both limitations remain part of the open endpoint
  application problem, and no smaller sufficient front is claimed.

- **Read native argument guards out of neutral proposition applications before
  attempting paired substitution.** **Exact readout and necessary conversion
  consequence proved.** `ProofErasureJointNeutralCarrierReadout` shows that
  comparison of f x and f y, for a variable f with literal oracle Pi A B, is
  equivalent to a carrier guard at A in either comparison mode. Recovery's
  directed domain conversions become carrierCompute; argument computations
  become carrierReduce. The result covers the entire joint grammar, not only
  the application constructor. An eta wrapper displayed at an assigned domain
  A recovers A -> Prop even when its internal variable f is declared B -> Prop.
  Comparing wrapper x and wrapper y uses only the supplied source guard at A.
  Their head-beta contracta expose f x and f y, so any proposition endpoint-beta
  transport law necessarily supplies a target guard at the native B.
  Introducing a fresh observer and removing it with an exactly recovered
  constant function strengthens this: beta transport from any fixed finite
  source stage into the union entails transport of that stage's guards along
  every ordinary typed equation A = B. This includes source stage zero; it
  cannot be deferred solely to strictly lower primitive stages. No comparison
  certificate for A and B, exact recovery of x/y, or literal join is assumed.
  This is a necessary condition, not a proved conversion law, a refutation of
  proposition beta stability, or a strictly smaller sufficient front. Next:
  the paired-image invariant must account for this native-domain conversion;
  diagonal recovery alone cannot discharge it. General dependent record/Pi
  carrier conversion remains open with the quotient-repaired full core.

- **Collapse universe-result function carriers to ordinary function comparison.**
  **Not established; no counterexample claimed.** The function rule gives a
  comparison of applications under a fresh binder after sort-carrier decoding.
  Extracting a comparison of the functions still requires cancellation through
  computations of those applications. Merely wrapping the body comparison in
  two eta expansions would require composition not supplied by JointCheck.
  The existing function alignment theorem retains displayed domains and does
  not justify changing them by arbitrary semantic conversion. This shortcut
  therefore does not discharge the native-domain requirement on its own.

- **Use semantic head exposure to recover arbitrary retained syntax and to
  transport structural subsingletons through type conversion.** **Conditional
  reduction proved for contextual computation.**
  `ProofErasureScopedSemanticRecovery` isolates `ScopedSemanticHeadExposure`:
  a typed type convertible to a sort, Pi, or registered family computes to that
  kind of head. Computation freely chooses Pi annotations and family universes
  and arguments. Pi/family outputs retain actual typed representatives, without
  an additional full-type comparison certificate. The three clauses suffice
  for some-output recovery of every retained expression, including dependent
  projections. This extends the earlier raw `ErasedRecoveryHeads` approach to
  the contextual recovery used by the joint checker; exact assigned recovery
  remains unnecessary and is not claimed. A new induction on SubsingletonCarrier
  proves more: any type convertible to a structural subsingleton computes to a
  structural subsingleton. For Pi telescopes the codomain induction runs in the
  old domain context; primitive context transport moves the resulting path to
  the newly exposed domain, and Pi congruence completes the path. Thus all
  carrierSubsingleton cases, including arbitrary function telescopes ending in
  an empty structure, have semantic carrier conversion under this exposure
  premise. No checker-context conversion or global carrier-conversion law is
  used to prove that case. Head exposure itself remains open for the full
  quotient-repaired joint relation. This is not claimed a strictly smaller
  sufficient strengthening obligation. Next: extend the actual conversion
  argument to general function and dependent-record guards by a mutual
  checking/context-conversion induction, using some-output head recovery at
  recovered applications rather than exact assigned-type recovery.

- **Transport joint checking through ordinary context and carrier conversion,
  using semantic head exposure; then transport through arbitrary substitution.**
  **Proved conditionally, including dependent records.**
  `ProofErasureJointSemanticConversion` gives the full mutual checking/carrier
  induction. Recovered applications select a fresh Pi and convert the smaller
  argument guard to its domain. Function guards expose a target Pi, align the
  domains and codomains by injectivity, and move the smaller body guard through
  the converted binder context. Dependent records reconstruct the target
  projection telescope, transfer admissibility and proof-field classification
  across equivalent universe arguments, and align each smaller field guard by
  actual projection type uniqueness. `ProofErasureJointSemanticSubstitution`
  uses this result on the recursively substituted argument guard to prove
  arbitrary diagonal typed substitution. It needs no exact image recovery and
  no `JointCarrierDomainResynthesis` assumption or dependency. The certified
  primitive relation discharges descent and primitive substitution closure;
  semantic head exposure remains open. This removes the separate domain
  re-synthesis premise from these transport results but does not yet prove a
  strictly smaller sufficient strengthening front. Next: use this substitution
  law to remove exact-recovery premises from diagonal head beta, and investigate
  head exposure and genuinely paired argument substitution.

- **Use semantic substitution to remove exact-recovery restrictions from
  diagonal head beta.** **Proved under the same head-exposure premise.**
  `ProofErasureJointSemanticHeadBeta` proves inferred-lambda instantiation at
  every typed argument, proposition head beta for equal argument erasures,
  and the shared typed beta-image extension. Both displayed lambda annotations
  may differ from the assigned domain and neither needs an exact recovery
  certificate for the argument. The recovered-argument module now factors its
  private structural induction through an image predicate and a body
  instantiation callback. Its original theorem uses exact recovery, while the
  new theorem uses True and semantic substitution. Computation of bodies needs
  only typed ContextSubstitution, independently of image recovery. The original
  public exact-recovery results retain their statements and assumptions.
  Certified and finite-stage wrappers also compile. This addresses diagonal
  arguments and literal beta joins, not arbitrary carrier-related pairs.
  Head exposure remains open. Next: establish computational head adequacy or
  identify a concrete obstruction, and solve paired carrier substitution for
  the nonjoined critical pair; diagonal substitution alone cannot settle it.

- **Test whether semantic head exposure hides full proposition comparison by
  forcing a canonical Eq.rec probe to expose Prop.** **The probe and the
  five-argument decoding branch are proved; the full implication is open.**
  `ProofErasureEqHeadProbe` uses a constant motive returning Type, with minor
  Prop. The recursor is typed whenever its equality major is supplied, and
  ordinary definitional equality of its proposition endpoints makes its result
  definitionally Prop. Semantic sort exposure therefore forces a primitive at
  some computed prefix of its erased Eq.rec spine. The major is literally the
  proof marker, and the carrier and minor are literally Prop.
  `ProofErasureScopedFirstHeadStep` proves this first-prefix extraction for
  arbitrary contextual computation, retaining every preceding argument path.
  `ProofErasureEqPrefixGuardReadout` inverts the general singleton code at five
  arguments, realizes its exact generated telescope, and decodes its Eq-family
  guard to a comparison of proposition endpoints. If these endpoints come from
  below a front block, that certificate descends below the block and the fresh
  major binder together. No binder inhabitant or inverse typing weakening is
  used. This is evidence for a hidden-strength barrier, not yet proof of one:
  the first primitive can occur at an earlier prefix, and core alternatives
  must be excluded for the actual repaired definition collection. Preceding
  argument computations must also be prefixed to the decoded comparison.
  Next: connect those cases to the five-argument decoder before deciding
  whether head exposure is genuinely weaker than the full proposition front.


## Eq probe: computed prefixes and the semantic-head implication (2026-10-21)

- **Finish all first-head alternatives for the certified relation. Verdict:
  checked sufficiency, not a strictly smaller-front deliverable.**
  `ProofErasureEqHeadExposureBarrier` now proves
  `ScopedSemanticHeadExposure.propositionFront_of_core_singleton`. Its source
  relation has typed descent and constant/projection primitive heads; every
  primitive is ordinary core or a general singleton whose family guard uses
  a target joint comparator with typed descent and inert Eq spines. Canonical
  Eq.rec registration and exclusion of Eq.rec unfolding from the core are
  explicit. The proof uses only semantic sort exposure, with the constant
  motive probe from the preceding entry. It assumes one ordinary front binder
  and then a fresh equality-proof binder; neither needs an inhabitant below.
  The certified `ErasedBetaStableJoint D` corollary discharges the coverage and
  descent hypotheses using the existing union. Core soundness alone is not
  mistaken for syntactic Eq/Eq.rec inertness: both exclusions remain explicit.

  The previous gaps are now covered. Zero-argument singleton guards compare
  distinct fresh endpoints at a fresh variable carrier; native recovery and
  carrier inversion expose the contradiction. At one argument the carrier is
  Prop and the endpoints are distinct fresh proposition variables. At two,
  three, or four arguments the supplied proposition cannot compute/compare to
  the fresh requested index. Generation bounds arity by five. Padding a
  computed prefix with untouched arguments reconstructs a typed whole source,
  so the same exclusions apply after arbitrary argument computations. At five
  arguments, component paths and the decoded guard yield equality of the
  original propositions below all inserted binders. Existing core exclusion
  handles shorter prefixes and the full proof-marker-major application.

  This establishes an implication, not an equivalence or a proof that semantic
  head exposure is impossible. It also eliminates the need for the later
  generic substitution/head-beta arguments in this particular sufficiency
  proof. No strictly smaller irreducible obligation has been established;
  direct proof of sort exposure remains a live route to strengthening. The
  next substantive question is how to construct this probe's sort computation
  from its original-syntax conversion without assuming completeness of its
  singleton family comparison. If pursuing the full union instead, its extra
  specialized Eq-prefix alternative still needs to be connected explicitly;
  the current theorem already covers the certified core/general relation.


## Construct the probe computation before demanding global stability (2026-10-21)

- **Use ordinary joint endpoint checking to compute the probe directly.
  Verdict: constructed at the immediate successor stage.**
  `eqSortProbe_general_prefix` turns a stage-n endpoint comparison into the
  actual generated general singleton at that same guard stage. The full probe
  then computes exactly to Prop at stage n+1 by compatible application and one
  beta contraction. This works for a neutral proof major. No semantic head
  exposure, endpoint beta transport, or BetaStableFamily certificate is used.
  The construction does not produce its input comparison from arbitrary
  ordinary definitional equality. That remains the substantive adequacy gap.

- **Drop certification and the unrelated Pi/family head obligations from the
  sufficient target. Verdict: full-union sufficiency checked.**
  `TypedSource.computed_prefix` proves that a first-head primitive reached by
  component computation has an actual typed realization. The specialized Eq
  branch of ErasedJointUnion can therefore use the existing exact conversion
  to a general singleton, preserving its source, output and comparator.
  The prior core/general argument now covers the full union, with canonical
  registry agreement and explicit Eq/Eq.rec unfolding exclusions. A single
  computation of the lifted probe to any sort yields equality of the original
  proposition endpoints below an arbitrary inserted front block.

  The missing property is named `EqProbeSortExposure`: only this one fixed
  constant-motive Eq.rec probe must expose a sort when its endpoints are
  ordinarily definitionally equal. It suffices for PropositionFront in the
  full joint union, without the other semantic head fields or future beta
  certificates. This is a narrower proof target than the previously pursued
  global head/stability package, not a demonstrated strictly smaller
  irreducible front. No converse or strictness result is claimed.

  Re-examination of the substitution route found no automatic way around
  arbitrary native-domain conversion: the existing
  JointPropBetaTransport.native_domain_guard and carrier_conversion_stage
  already show that the required transport is semantic, not merely syntactic
  substitution of the old certificate. The direct probe construction avoids
  making that global closure law a prerequisite for the current route. Next:
  attack construction of the missing guard/computation from the original
  equality derivation. In particular inspect whether the guard's conversion
  evidence can be tracked as a genuinely smaller original derivation; neither
  replacing it by semantic equality nor simply invoking confluence resolves
  the missing erased certificate.


## Test proposition beta transport with a unit-valued Eq probe (2026-10-21)

- **Use finite-stage proposition beta transport as a local induction closure.
  Verdict: it already implies PropositionFront when a closed positive empty
  structure is present.** The checked theorem
  `JointPropBetaTransport.propositionFront_of_closed_unit` works from any one
  finite source stage, including zero, into the full joint union. The source
  carrier guard is just the empty-structure rule on two distinct variables;
  no source primitive computation is needed. Existing carrier conversion
  moves that guard to an Eq recursor returning the structure type. Common
  comparison cannot relate the two bare variables, so the converted guard
  must expose a structure or Pi carrier. Either output changes the Eq.rec
  head. Its first primitive then yields comparison of the original proposition
  indices below the inserted block, exactly as the sort probe does.

  This conditional implication does not refute proposition beta transport or
  strengthening. It does not assert that canonical Eq entails existence of
  a closed positive empty structure, or that such a structure may be added
  conservatively. It does rule out treating this transport law as an already
  justified local closure lemma in environments with such a structure. No
  strictly smaller sufficient front has been established.

- **Depend on the sort probe's literal result to obtain the barrier.
  Verdict: unnecessary.** `proofErase_joint_union_type_probe_head_descend`
  permits any lower type as the minor and any output whose head differs from
  Eq.rec. Actual typed first-head classification and the computed five-prefix
  guard provide the descent; semantic identification of the output is unused.

  Next: return to the original equality derivation and construct the particular
  probe computation directly. Any induction invariant that transports arbitrary
  carriers must account for the full strengthening content identified here.
  The present result gives no decreasing measure for that obligation. A useful
  next test is to retain the actual type-conversion subderivation as part of
  the guard construction and inspect the application and transitivity cases,
  rather than installing global beta transport as a premise.


## Test typed composition before choosing a strong-derivation rank (2026-10-21)

- **Compose two same-stage certificates once the intermediate is typed.
  Verdict: stage-preserving composition is false even for propositions.**
  `joint_unit_probe_proposition_composition_context` constructs a well-formed
  three-variable context containing a neutral observer and two unit variables.
  Its three propositions are observer x, observer unitConstructor, observer y.
  They all have literal type Prop; both adjacent comparisons exist at stage
  zero, but the outer comparison does not. The observer's native domain is a
  constant-motive Eq probe returning the unit type, with literally reflexive
  proposition indices and an actual Eq.refl proof. Thus neither an untyped
  middle nor an assumed endpoint equation explains the failure.

  A companion witness gives the same failure for explicit carrier guards with
  all three terms assigned that very same probe type. The constructor's typing
  is reconstructed from the unit metadata and an existing unit variable; no
  constructor-typing premise is smuggled into the witness. This refutes keeping
  the maximum of the two input stages in the transitivity case. It does not
  refute composition in the full union, any bound that increases the stage,
  or induction on the original strong derivation and its typing subproofs.

- **Account for the exact extra guard needed by this composition.
  Verdict: stage one repairs the witness.** `eqTypeProbe_compute_stage` returns
  an arbitrary type-valued probe's minor from an actual stage-n endpoint
  comparison at n+1. At reflexive indices the guard is already stage-zero
  reflexivity, so the carrier and proposition composites are constructed at
  stage one. Conversely `eqTypeProbe_zero_head` excludes every core path that
  changes the probe's head, including paths that first compute any arguments.
  This gives both the lower and upper bound for this particular example.

  The remaining induction must retain information from the assigned typing
  conversions, rather than only the two input comparison stages. Strong.appDF
  and Strong.defeqDF contain explicit conversion subderivations, but translating
  those into the required native-carrier guards remains open. Next test a
  simultaneous invariant that retains these subderivations when translating
  transitivity and application; the current result supplies a minimal case
  that any proposed stage bound must accommodate. No general decreasing rank
  or strictly smaller sufficient front is asserted.


## Consume an actual type comparison in the subsingleton application case (2026-10-21)

- **Replace arbitrary semantic carrier conversion by a supplied type comparison.
  Verdict: structural subsingletons, including dependent Pi telescopes, now
  transport constructively.** The exposed empty-structure case was already
  `proofErase_joint_unit_carrier_target`; it was not reimplemented. The new
  `proofErase_joint_compared_subsingleton_compute` extends this to all of
  SubsingletonCarrier: empty registered structures with arbitrary parameters,
  closed under arbitrary dependent Pi domains. Either typed comparison mode
  suffices. The target computes to a structural subsingleton using exactly the
  same primitive relation. The proof requires primitive descent, family-head
  inertness, and interpreted primitive substitution for changing binder
  contexts. It assumes no global semantic head exposure or beta-transport law.

  Both orientations of the comparison are proved together. Computation
  preserves source structural subsingleton certificates. In the Pi cases,
  actual source and target body typings are placed in the original left-domain
  context, where the smaller body comparison applies. Reflection of the domain
  comparison justifies moving the resulting computation to the right-domain
  context. No unrelated carrier-conversion theorem is invoked recursively.

- **Use this conversion evidence to build the application's native guard.
  Verdict: constructed for structurally subsingleton assigned domains.**
  `proofErase_joint_compared_recovery_subsingleton_guard` consumes an existing
  recovery and an actual comparison of its selected type with the assigned Pi.
  It chooses a new recovered Pi and supplies its argument guard together.
  `proofErase_joint_application_of_compared_recovery_subsingleton` then closes
  the application constructor. Stage-zero and certified-relation specializations
  discharge the primitive transport assumptions and stay at their source
  relation. Existence of the starting recovery and type comparison remains an
  input, not a coverage assertion about arbitrary original typing derivations.

  Remaining: source guards with a computation prefix need conversion of a type
  comparison at the unreduced carrier into information at the exposed carrier;
  arbitrary dependent-field and function endpoint guards also remain open.
  The new result handles literal structural subsingletons and actual supplied
  type comparisons, not all semantic subsingletons or arbitrary conversion.
  Next attack that computation-prefix case while retaining the original typing
  conversion evidence; do not replace it by the already-strong global head or
  beta laws. No proof of PropositionFront or strictly smaller sufficient front
  is claimed.


## 2026-10-21 — Decode Eq guards at arbitrary computed carriers

- **Keep native recovery paths instead of freezing the Eq carrier.
  Verdict: proved.** `ProofErasureEqNativeCarrierRecovery` inverts a typed Pi
  computation while retaining its body path in the original domain context.
  For an actual prefix `Eq α z`, every recovered final Pi is reachable from
  its native Pi, and its selected domain is reachable from `erase α`.
  Forward typed replay and interpreted substitution suffice; no inverse
  weakening or global recovery coverage is used.

- **Read endpoint guards from arbitrary typed Eq proposition comparisons.
  Verdict: proved with primitive descent, head restrictions, and interpreted
  primitive substitution.** The two carriers can compute independently from
  a common ancestor. The decoder retains both paths so symmetry can exchange
  the branches; it returns the guard at the ancestor. Primitive computation
  must preserve Eq heads. Actual typed realizations of both Eq spines survive
  computation by forward replay. Native recovery accounts for the domain
  selected by the carrier-aware application rule.

- **Make the existing Eq proposition encoding lossless.
  Verdict: proved in either comparison mode, with stage-zero and certified
  specializations.** `proofErase_joint_carrier_propositions_iff` extends the
  old forward encoding to an equivalence for arbitrary typed carriers and
  proof-valued endpoints. Stage zero and `ErasedBetaStableJoint` discharge the
  primitive substitution premise using established laws, assuming Eq is not
  unfolded. No semantic head-exposure or proposition beta-transport premise
  is needed for either specialization.

  This closes the earlier decoder gap but not the general computed-source
  carrier-conversion case. A common computational ancestor is directed
  evidence; an arbitrary type comparison supplies no such ancestor by itself.
  The next application-invariant step still needs to reconcile the guard's
  computation with the assigned/selected-type comparison. Do not infer
  comparison transitivity from the new equivalence: same-stage typed
  transitivity was already refuted. No strengthening theorem, canonical-Eq
  counterexample, or strictly smaller sufficient front is claimed.


## 2026-10-21 — Transport exposed record checks by actual type comparison

- **Use lossless Eq encoding to bypass carrier conversion.
  Verdict: composition remains missing; no closure theorem obtained.**
  An actual carrier comparison can be inserted into the carrier argument of
  an Eq expression by application congruence. Connecting that comparison to
  an encoded endpoint guard still asks for composition of proposition
  comparisons. The preceding decoder does not supply that composition, and
  same-stage typed proposition transitivity was already refuted. Do not use
  this encoding as an implicit transitivity or forward-computation rule.

- **Transport ordinary field comparisons directly at an exposed record.
  Verdict: proved, including changed levels and parameters and any number of
  dependent fields.** `proofErase_joint_compared_record_guard` uses an actual
  typed comparison from a displayed record family to the target type. Rigid
  family exposure supplies a target computation to that same family. Forward
  replay realizes its actual type; the type comparison and replay let the
  left endpoint be typed at both family instances. Existing record metadata
  transport then preserves admissibility and maps source proof fields to
  target proof fields. All retained common projection comparisons are reused
  unchanged. No primitive substitution or semantic head-exposure law is needed.

- **Consume this result at the application's recovered domain.
  Verdict: constructed at the original relation.** Compared Pi recovery
  supplies the selected domain and an actual assigned/selected-domain
  comparison. The record theorem produces its argument guard, and appCarrier
  closes the application comparison. Finite-stage and full-union record
  corollaries discharge family inertness when D does not unfold that family;
  they need no beta-stability premise or stage increase.

  This handles carrierIntro with ordinary field comparisons. It does not
  convert carrierNested's dependent field carriers, carrierFunction's binder
  checks, or a guard whose source carrier first computes to a family. Those
  cases still require new compatibility evidence. In particular, ordinary
  field comparison is not interchangeable with a carrier guard at a field's
  type. Next retain the actual family-comparison subderivations to investigate
  comparisons of the dependent projection carrier recipes; the source
  computation/type-comparison reconciliation remains open. No goal outcome
  or smaller sufficient irreducible front is claimed.


## 2026-10-21 — Retain native declaration domains through computed prefixes

- **Recover parameter evidence discarded by rigid family exposure.
  Verdict: prefix comparison and shared-native-domain readout proved.**
  `JointCompare.const_app_prefix` removes the final arguments of two inert
  constant spines while retaining their inferred prefix comparison, including
  all prefix computations. Family exposure alone did not retain this evidence.

- **Generalize native Eq recovery to arbitrary dependent telescopes.
  Verdict: proved, even after every argument computes independently.**
  `ProofErasureNativeTelescopeRecovery` starts recovery at the stored constant
  declaration and traverses an actual `InstForallsC` walk. Typed Pi inversion
  retains codomain computation in the original domain context. Substitution
  of the original typed argument gives the next native residual path. If that
  argument computes first, forward replay types its output, and computation
  of argument images transports all occurrences in the codomain. Every later
  dependent binder still uses the original native residual as its ancestor.
  No argument must recover its assigned type, and no normal forms are needed.

- **Read the last guard after independently computing a shared prefix.
  Verdict: constructed at the original relation.**
  `proofErase_joint_computed_native_argument_guard` takes a common original
  typed declaration prefix and two arbitrary computation paths from it. An
  inferred comparison of the resulting applications yields the final argument
  guard at the original native domain. The two final raw arguments need no
  independent typing or recovery certificate. Symmetry swaps both prefix paths;
  computation extends each path and retains the final-argument computations.
  Stage-zero and certified specializations discharge primitive assumptions for
  a rigid constant excluded from D's unfolding relation.

  This does not assume two unrelated parameter substitutions share a native
  computational ancestor. Comparing their native residual types is the next
  missing declaration-type congruence, named
  `JointNativePrefixTypeComparison Source Target`. Its non-proof prefix
  endpoints have actual declaration telescope walks and an actual comparison;
  the requested result compares the native residual types. Source and Target
  may differ. The property is explicitly unproved and is not claimed to be a
  smaller sufficient front. In the application case the residual types contain
  two different substitutions into a dependent codomain; the supplied parameter
  guard does not yet give that codomain comparison. Retain the actual prefix
  comparison and argument guards in a simultaneous proof instead of replacing
  them with semantic equality. Full dependent-field transport remains open.


## 2026-10-21 — Native declaration-type comparison has a recursive annotation barrier

- **Derive native result-type comparison from the ordinary core prefix check.
  Verdict: refuted in an actual well-formed canonical-Eq extension.**
  For a recursive domain D = (D -> Prop), install a constant with type
  `(x : D) -> (x x -> Prop)`. Its applications to two diagonal lambdas have
  a common prefix comparison consisting only of constant reflexivity and
  common lambda checking. Both applications are non-proofs. Comparing their
  native result types forces comparison of the original lambda annotations,
  even when their ordinary conversion was absent from the prefix certificate.
  A reflexive Eq cast of a literal Pi supplies an annotation that the ordinary
  core cannot expose as a Pi. Thus `JointNativePrefixTypeComparison Source core`
  fails for every source relation in this observer environment.

- **Check that the recursive observer really can be declared.
  Verdict: constructed with two fresh declarations, retaining canonical Eq.**
  `NativeLoopObserver.canonical_recursive_extension_failure` first installs
  the existing recursive family, derives a closed literal recursive Pi from
  it, and installs the observer as an axiom with a checked closed type. Both
  extensions are well formed and preserve canonical Eq and quotient
  registration. The resulting environment also satisfies PropositionFront:
  this counterexample refutes the certificate rule, not strengthening.

- **Does the same example refute the richer joint stages or their union?
  Verdict: no; its native result shapes compare at stage one.**
  `ErasedQuotCore.cast_native_observer_results_stage_one` computes the reflexive
  cast out of both self-application annotations, without normalizing the loops.
  This repairs this particular example only. Native result-type congruence
  with a richer target remains open. The next proof must use the original
  typing/conversion evidence to recover annotation comparisons; induction
  on the shallow prefix certificate alone does not provide that evidence.
  Test or construct that conversion-sensitive target before using native
  congruence to transport dependent record-field carriers. No smaller
  sufficient irreducible front or goal outcome is claimed.


## 2026-10-21 — Full-union native congruence already carries the front

- **Repair native type congruence by allowing an arbitrary target stage.
  Verdict: a conditional full-front implication, not a routine local helper.**
  `JointNativePrefixTypeComparison.propositionFront_of_closed_unit` proves
  that native congruence from any fixed finite stage, including zero, into
  the full joint union implies PropositionFront when a closed positive empty
  structure and a nonrecursive dependent observer are declared. This is not
  a refutation of union congruence. It excludes treating that unrestricted
  congruence as an independently easy compatibility lemma in these environments.

- **Find the obstruction without the recursive domain that already implied
  PropositionFront. Verdict: an inhabited nonrecursive observer suffices.**
  The observer type is `(A : Sort u) -> (f : A -> Prop) -> (x : A) ->
  (f x -> Prop)`. It has a checked closed lambda inhabitant: under its last
  proof binder return `f x`. Choose a variable f whose native type is B -> Prop
  but whose supplied type is A -> Prop by ordinary conversion. A guard at A
  compares the two fully supplied observer prefixes. Comparing their native
  result types forces a guard at B by Pi-domain and neutral-application readout.
  The observer needs no recursion, normalization, or extra logical axiom.

- **Can the fresh function binder be removed without strengthening?
  Verdict: yes, by forward substitution of an exactly recovered inhabitant.**
  The derived native-domain guard yields arbitrary ordinary carrier conversion
  from the chosen finite stage into the union. A closed positive empty
  structure supplies distinct guarded variables. Moving that guard to the
  type-valued Eq probe forces a head change and hence descends the original
  proposition equation. All inserted binders are handled by forward operations;
  no beta-transport or semantic-head-exposure assumption is used.

  The implication requires the stated observer and unit declarations, sound
  primitives, registry agreement, and exclusion of Eq/Eq.rec unfolding. It
  does not prove a converse, an unconditional equivalence, or strict smallness.
  The earlier recursive counterexample only ruled out the ordinary-core
  target; this stronger diagnostic shows why unrestricted union congruence
  itself must be treated as a full-front proof route. Continue the simultaneous
  derivation approach only with explicit source-derived conversion certificates;
  do not invoke native type congruence or ordinary carrier conversion as free
  closure lemmas when transporting dependent fields. The main goal remains open.


## 2026-10-21 — Construct native residual joins from actual argument joins

- **Use computationally joined parameters instead of unrestricted native
  congruence. Verdict: the native residual join is constructed.**
  `proofErase_computed_native_supply` proves that a typed telescope still
  admits literal raw supply after its starting type and all supplied arguments
  compute. It produces the raw supply output and a directed path from the
  original native residual. Two walks from the same declaration, whose
  arguments compute pointwise to one list, consequently have a shared raw
  residual and an actual joint comparison at the same relation. Determinism
  of raw supply identifies the two outputs. No normalization is assumed.

- **Can computed constant spines actually recover a type, rather than merely
  constrain hypothetical recoveries? Verdict: explicit recovery constructed.**
  Successful raw supply builds a recovery certificate along the entire spine.
  The new existence theorem combines it with the native supply result, without
  requiring any supplied argument to recover its assigned type. Only argument
  computations are included here; unfolding the constant head is a separate
  case. This strengthens the preceding native-recovery results, which took an
  existing recovery as an input.

- **Retain the dependent field-domain paths. Verdict: both paths constructed.**
  When both native residuals are Pis, typed Pi readout gives a common reduct
  of their next domains. Applied to a constructor telescope, this covers the
  next field after the actual preceding argument lists have been joined. The
  theorem takes the typed walks and explicit joins; it does not manufacture
  joins for merely compared parameters or preceding projections. The certified
  joint-relation corollary discharges primitive descent, head shape, and
  substitution closure with the existing proved interfaces.

  Arbitrary carrier guards cannot simply be moved forward along these domain
  computations: carrierCompute supports the opposite direction. The next
  dependent-field step must retain a guard at the common reduct, or prove its
  transport with explicit evidence. No unrestricted native congruence,
  confluence, carrier conversion, or proposition beta law has been assumed or
  proved. The original strengthening goal and strict-smallness question remain
  open; this is a constructive case feeding the simultaneous derivation route.


## 2026-10-21 — Consume native joins in actual application checking

- **Move an arbitrary argument guard to the joined native domain.
  Verdict: the repaired-core application case is closed.**
  The existing `ErasedQuotCore.carrier_compute_forward` already handles every
  joint guard constructor, including functions and nested dependent fields.
  `joined_native_prefix_guard` now combines it with the constructed native
  residual joins. A literal typed declaration walk supplies exact native
  recovery; converting that recovery to the common Pi and transporting the
  supplied guard produces the actual appCarrier premises. No new recovery,
  native-type comparison, or converted guard is assumed. The parameters must
  have an explicit ordinary-core join, and the source guard is in that core.

- **Check actual proposition endpoints, not only raw application shapes.
  Verdict: both literal Prop typings and their comparison are constructed.**
  `ErasedQuotCore.joined_native_propositions` reflects the constructed domain
  comparison to type the original arguments at the target prefix's domain.
  Applying that proposition-valued prefix to the two arguments yields actual
  propositions and a joint comparison of their erasures. It does not assume
  the target-domain typings or any strengthening principle.

- **Retain enough path information to allow certified singleton guards too.
  Verdict: the beta-joined parameter case is closed in the certified relation.**
  `ProofShape.supplyType_beta` is a raw, environment-independent theorem:
  successful literal telescope supply survives simultaneous beta reduction of
  the type and arguments, and its output only beta-reduces. Typed native walks
  therefore retain beta joins of their residuals and next domains. The existing
  certified oracle/carrier-beta theorem transports every certified guard along
  those paths. The resulting Pi recovery, guard, and application comparison
  stay in ErasedBetaStableJoint; no stage-wide proposition beta law is assumed.

  These cases have distinct premises: general ordinary-core joins with core
  guards, or pure beta joins with certified guards. They do not establish
  carrier transport along arbitrary certified computation, coverage of the
  unrestricted union, or joins for merely compared parameters. Both prefixes
  use the same instantiated declaration type and actual native walks. The
  next unresolved case is where a parameter comparison cannot be replaced by
  either of these explicit joins; the previous native-congruence barrier still
  applies. No strictly smaller sufficient front or goal outcome is claimed.


## 2026-10-21 — Consume native result-parameter changes without joins

- **Does a native application really require a parameter join when its
  parameter changes only a function result? Verdict: no, for neutral source
  results.** The new declaration shape is `(R : Sort u) → (Prop → R) → Prop`.
  Its parameter is absent from the function argument's displayed domain.
  `proofErase_neutral_function_result_guard` derives the two actual carrier
  erasures and transfers every joint guard, including carrier computation,
  endpoint reduction, and nested checking, by the existing neutral-result
  theorem. Ordinary R ≡ S supplies the target argument typings separately.
  `proofErase_native_neutral_result_propositions` recovers the actual target
  constant prefix and constructs comparison of its two actual proposition
  applications. No native type comparison, argument join, or transported
  guard is an input. The primitive head invariant suffices, including for
  the unrestricted joint union. The displayed observer type has a checked
  closed lambda inhabitant, so its signature needs no recursive type axiom.

- **Is this merely the previous join construction in disguise? Verdict:
  excluded by a checked example.** `native_neutral_result_without_join`
  specializes the earlier neutral eta example: R = F (fun p => f p), S = F f.
  These parameters compare at stage zero, yet neither the parameters nor
  the native argument types Prop → R and Prop → S have a computational join
  anywhere in the union. The source function type is explicitly inhabited.
  Nonetheless every finite-stage source guard produces the actual target
  proposition comparison at that same stage. The example assumes a named
  declaration with the displayed, inhabited observer type; it does not
  assert that every environment already contains such a declaration.

  Judgment: a concrete non-joining native application case is now consumed
  by the checking rule. The neutral-result reindexing itself was already
  known; the addition is actual native recovery, conversion of argument
  typings, proposition endpoints, and their combined no-join witness.
  This does not address parameter occurrences in function input domains,
  arbitrary dependent native templates, comparison composition, or coverage
  of arbitrary strong derivations. It is not a strictly smaller sufficient
  front and does not close any of the three success conditions in GOAL.md.


## 2026-10-21 — Neutral input changes through recovery and full carrier checking

- **Must context transport preserve every recovered type exactly? Verdict:
  no; preserving its function domains suffices for the application rule.**
  Added NeutralResultChange k. It permits changes at variable-headed terminal
  results, keeps every displayed Pi domain exact, and requires the changed
  heads to lie outside k protected binders. Pi descent increments k. The
  checked lifting, instantiation, and computation lemmas retain this condition;
  in particular, applying a recovered function cannot substitute an arbitrary
  term for a changed head. ScopedTypeRecovery.neutral_oracle reconstructs
  recovery after an interpreted context change, with only this controlled
  variation of its selected output. Sort and registered-family outputs stay
  exact; application consumes the unchanged Pi domain.

- **Does this repair the whole body judgment, including carrier-aware
  applications? Verdict: proved for substitution-closed primitive relations.**
  JointCheck.neutral_oracle transports every comparison/carrier constructor
  together, with identical endpoints and carrier. The computation paths and
  sort witnesses use the identity context interpretation. Actual convertible
  neutral binder types provide that interpretation and the oracle evidence.
  This gives unconditional same-relation transport for certified checking;
  it assumes neither general comparison completeness nor a proposition beta
  law. It is not an unconditional theorem for the full joint union, whose
  required primitive substitution closure is still open.

- **Can function input types change without restricting the guard to one
  displayed function rule? Verdict: all guard constructors are covered.**
  JointCarrierGuard.neutral_domain changes a neutral input A to convertible
  neutral B while retaining an arbitrary dependent codomain. In the carrier
  computation case, typed Pi inversion retains the codomain path in the
  original binder context; primitive context transport replays that path
  under B. The computed source input remains neutral, and the recursive
  guard transfers there. Endpoint reductions, subsingletons, symmetry, and
  nested function/field checking are included. The certified specialization
  has no open closure premise. The native-prefix corollary recovers its
  actual target function type, constructs the converted argument typings,
  and consumes the resulting guard to compare actual propositions.

- **Is allowing different recovery outputs essential here? Verdict:
  checked separation.** The eta-different neutral binders F (fun p => f p)
  and F f have no computational join in the entire union. Nonetheless all
  certified body judgments and all dependent function guards transport in
  both directions between them. A source bvar-0 recovery cannot keep its
  exact output in the target context even if target recovery is enlarged to
  the entire union. Thus the new positive result genuinely bypasses the
  previously refuted exact-recovery invariant.

  Judgment: this closes the neutral input-domain case left by the preceding
  result-only observer work. It is a new recovery/context invariant, not a
  proof of arbitrary context conversion. Non-neutral domain changes, arbitrary
  dependent native parameter templates, composition, full-union substitution,
  and strong-derivation coverage remain open. No goal success or strictly
  smaller sufficient front is claimed.


## 2026-10-21 — Simultaneous checking with recursively changing Pi domains

- **Can the exact-domain invariant be replaced by recursively related
  domains? Verdict: yes for protected neutral changes through Pi structure.**
  NeutralTypeChange relates identical subtrees, arbitrary neutral spines
  whose heads lie outside a protected depth, and Pis with recursively related
  domains and codomains. The depth increases under Pi bodies. Unlike
  NeutralResultChange, it permits input domains themselves to change.
  Checked lifting and instantiation preserve the protection condition.
  Structural subsingleton certificates survive this relation as well.

- **Can carrier computation preserve this larger relation without assuming
  arbitrary type congruence? Verdict: proved using actual equality.**
  Typed Pi injectivity supplies equality of domains and codomains; typed Pi
  computation inversion retains the body path in the original domain's
  context. The domain and body simulations recurse on the structural
  relation, then primitive context transport moves the body path to the new
  domain. Neutral leaves discard source argument computations; identical
  subtrees replay them exactly. Neither computational joins nor general
  comparison transport are premises.

- **Can recovery and application checking adapt together when a selected
  domain changes? Verdict: the complete simultaneous induction checks.**
  Typed recovery in convertible contexts produces recursively related
  outputs. In conversion, replay of both recovery certificates yields their
  actual type equality, enabling the preceding simulation. JointCheck's
  appCarrier case replays the new Pi recovery, uses typed Pi injectivity to
  establish equality of the selected domains, and invokes the smaller carrier
  subderivation at the new domain. The carrierFunction case changes the body
  context and codomain together. Every comparison and carrier constructor,
  including nested dependent fields and arbitrary carrier computations, is
  included. Certified specializations need no open union substitution or
  proposition beta premise.

- **Does this actually cover non-neutral binder types? Verdict: checked
  example outside the previous invariant.** Binder types
  `(F (fun p => f p)) → Prop` and `(F f) → Prop` are typed, inhabited, and
  definitionally equal. They have no computational join in the full union.
  The old result-only relation cannot relate them because their domains
  differ; the new recursive relation does. All certified typed carrier guards
  transport in both directions, and all certified typed body comparisons
  transport to the new binder context. The native-prefix corollary consumes
  any recursively related typed source carrier to compare actual proposition
  applications, constructing recovery and converted argument typings.

  Judgment: this replaces a flat neutral-input fragment by a recursive Pi
  invariant and closes its recovery/checking interaction. It remains a
  sufficient structural criterion for particular conversions, not a coverage
  theorem for arbitrary strong derivations. Changed record parameters,
  non-displayed type shapes, and arbitrary union primitive substitution are
  not established. No smaller sufficient PropositionFront or goal outcome is
  claimed; the original strengthening sorry remains.


### 2026-10-21 13:14 UTC — Recursive guards through a registered Box

- **Use the actual field recipe to cross a changed record parameter. Verdict:
  proved for the one-field Box, including function-valued fields.**
  ProofErasureRecursiveBoxGuard transports every typed carrier-guard
  constructor from Box A to Box B when A and B are typed equal and related by
  NeutralTypeChange. The nested-field case realizes actual projection types,
  identifies the closed field recipe with A, and invokes recursive carrier
  transport at the field. Carrier computation simulates the parameter path
  on B and recurses at the realized types. The proof retains nested checking;
  it does not assume ordinary comparison of projections. The certified
  specialization discharges descent, head shape and substitution, and an
  actual native proposition application consumes the converted guard.

- **Is this just the preceding Pi/neutral theorem applied to Box? Verdict:
  no, with a checked inhabited separating example.** For explicitly registered
  Box, the parameter functions `(F (fun p => f p)) → Prop` and `(F f) → Prop`
  are related by NeutralTypeChange, but their Box carriers are not. The Box
  carriers have no computational join even in the full joint union. Their
  certified typed guards are nevertheless equivalent. The example constructs
  a Box inhabitant by applying the registered constructor to the constant
  function returning the proposition `∀ P : Prop, P`; no proof of that
  proposition is claimed. Constructor universe arity follows from the
  registered declaration's typed result and the supplied family signature.

  Judgment: this removes one concrete record-field obstruction left by the
  recursive Pi criterion. Registration and the Box signature remain explicit
  hypotheses; no canonical-Eq environment extension is constructed. There is
  no new recovery/context invariant for changing whole Box binders, no
  arbitrary record-template theorem, and no general coverage of strong
  derivations. This does not establish a strictly smaller sufficient front.
  The original strengthening goal remains open.


### 2026-10-21 13:23 UTC — Close recursive Box recovery and context conversion

- **Extend the recursive type relation through Box, instead of stopping at
  a standalone carrier lemma. Verdict: proved, including arbitrary Pi/Box
  nesting.** BoxTypeChange embeds NeutralTypeChange and adds recursive closure
  under the selected registered Box. It preserves protected-depth weakening,
  instantiation, Pi exposure and structural subsingletons. Literal erased Box
  exposure recovers an actual parameter at Type from the family signature;
  rigid-family injectivity gives equality of actual parameters. Those facts
  let the relation simulate all source carrier computations recursively.

- **Can projection recovery survive a changed record parameter? Verdict:
  proved for the registered Box, without exact recovery output.** A related
  recovered rigid spine either retains its parameters or is the selected Box
  with a recursively changed parameter. Its closed projection recipes remain
  related. The sole Box field recipe is the parameter itself. Typed recovery
  therefore produces a related output after projection, and the convert case
  uses actual recovery replay and uniqueness to justify computation simulation.

- **Does recovery transport close the checking interaction? Verdict: proved
  simultaneously for every joint constructor.** Changed recovered application
  domains are handled by the smaller carrier derivation. Changed function
  domains extend the convertible contexts and related context oracles. Nested
  record fields are reified at both carriers; uniqueness of the same actual
  projection supplies their type equality, and the recipe relation supplies
  the recursive carrier premise. Source endpoint typings suffice. Certified
  specializations discharge primitive descent/head/substitution and family
  inertness and remain in the same certified relation.

- **Does the extension move an actual whole Box binder? Verdict: checked on
  the previous inhabited no-join example.** The Box types with eta-different
  function parameters are outside NeutralTypeChange, but BoxTypeChange relates
  them. All certified typed body comparisons survive the binder change, as do
  all certified carrier guards. The example uses the new general theorem,
  not an assumed context-conversion law.

  Judgment: the whole-Box recovery/context gap recorded at 174a9614 is closed
  for this structural fragment, even with arbitrary alternation of Pi and Box
  nodes. Only one explicitly registered monomorphic Box is allowed to change;
  other record parameters remain exact. Arbitrary dependent field recipes,
  non-displayed type shapes and coverage of strong derivations are unresolved.
  No goal outcome or strictly smaller sufficient front has been established.


### 2026-10-21 13:30 UTC — General transport from local type-relation laws

- **Separate the checking induction from the selected record family.
  Verdict: proved, with the Pi/Box fragment as a checked instance.**
  TypeChangeLaws gives explicit local requirements on a depth-indexed relation:
  reflexivity, one-binder shifting, result instantiation, Pi introduction and
  exposure, exact sort exposure, fixed registered record heads/levels/arity,
  preservation of actual closed field recipes, structural subsingletons, and
  simulation of computations of actually equal typed carriers. None of its
  fields assumes recovery transport, comparison transport or carrier transport.
  No symmetry, transitivity, or depth-monotonicity law is required.

- **Are dependent fields enough to force another bespoke checking proof?
  Verdict: no, once the selected field recipes stay related.** Generic recovery
  and the full simultaneous joint-checking theorem now work for every relation
  satisfying those local laws. Record parameters may change for any registered
  family; dependencies on earlier projections are retained in projectionType.
  Actual projection typing and uniqueness supply equality of the selected
  field types, so the smaller carrier derivation discharges nested checking.
  The record-specific work is establishing the relation and its laws, not
  repeating the entire recovery/application/context induction.

- **Does the abstraction smuggle in a global transport premise?
  Verdict: checked instance and rebuilt separating example.**
  BoxTypeChange.transport_laws proves all requirements from the existing
  syntactic/typed Box lemmas. The old Box recovery and simultaneous checking
  proofs now invoke the generic theorem; their public hypotheses and outputs
  are preserved. The inhabited, no-join whole-Box binder example rebuilds.
  The substitution and primitive descent interfaces remain explicit, and
  the existing certified Box corollaries still discharge them independently.

  Judgment: this gives a general sufficient criterion for recovery and
  checking transport, with a concrete implementation, and isolates the
  dependent-field obligation. It is not a proof that arbitrary record recipes
  preserve a suitable relation, nor coverage of arbitrary type equality or
  strong derivations. Heads, universe instances and record arities still stay
  fixed. No strictly smaller sufficient PropositionFront obligation is claimed;
  the full strengthening goal remains open.


### 2026-10-21 13:39 UTC — Typed beta paths around structural conversion

- **Make the raw local-law relation cover all typed equality. Verdict:
  refuted by a checked typed beta example.** TypeChangeLaws.sort_inv forces a
  related literal sort to remain that exact sort. Prop and its typed identity
  wrapper are definitionally equal, but the wrapper erases to an application.
  type_change_laws_miss_typed_beta proves that every relation satisfying the
  local laws misses this conversion. Broadening the same raw relation cannot
  supply full coverage; a path closure or weaker exposure interface is needed.

- **Interleave structural changes with beta reduction and expansion.
  Verdict: full certified carrier/context transport proved.** TypeChangePath
  records actual types at one sort, structural equality plus the proposed
  relation, beta paths in either direction with typed endpoints, and finite
  composition. Its actual equality is derived. TypeChangePath.carrier and
  TypeChangePath.context transport every certified checking constructor along
  any such path. Forward beta uses certified oracle/carrier transport;
  reverse beta uses exact recovered annotations. Every intermediate guard
  remains certified, allowing arbitrary finite iteration. No proposition
  endpoint-beta assumption or strengthening inverse is used.

- **Does this merely disguise a computational-join criterion? Verdict:
  checked inhabited counterexample to that interpretation.** A typed identity
  beta redex hides the source carrier of the eta-different function-field Box
  example. The resulting endpoints are not BoxTypeChange-related and have no
  certified computational join. A beta edge followed by the structural edge
  nevertheless transports all certified typed guards and body comparisons.
  No-join follows from certified computation/beta commutation and the old
  full-union no-join result. The new claim is specifically no certified join,
  not a stronger full-union no-join claim for the wrapped endpoints.

  Judgment: hidden pure-beta type shapes and finite mixtures of structural
  changes are now covered constructively. A same-relation computation-pullback
  lemma also handles arbitrary backward annotation computation when primitives
  are substitution closed. General forward primitive computation, arbitrary
  dependent field recipes and coverage of strong derivations remain open.
  The raw-local-relation coverage idea is rejected; mixed typed-path coverage
  remains live. No goal outcome or strictly smaller sufficient front is claimed.


### 2026-10-21 13:49 UTC — Mixed Pi/Box/beta coverage fails at primitive Eq

- **Do finite beta expansions make the Pi/Box paths complete for type
  conversion? Verdict: refuted under canonical Eq by a closed typed example.**
  TypeChangePath.box_sort_reduct proves that beta reducibility to a literal
  sort is preserved along every Pi/Box/beta path. The analogous bare-constant
  invariant is also proved. Structural Pi/Box edges cannot introduce either
  atomic reduct, and typed beta confluence handles arbitrary beta expansions.
  An Eq type probe preserves its Eq.rec head under beta, so it cannot be
  reached from its sort or non-Eq.rec constant minor by these paths.

- **Could the failure depend on an unsolved proposition equality or empty
  context? Verdict: no.** box_beta_paths_not_complete constructs the closed
  proposition ∀ P : Prop, P and uses Eq.refl at that proposition. The probe
  returning Prop is definitionally equal to Prop in the empty context by
  canonical Eq, but no mixed Pi/Box/beta path connects them. No inhabitant of
  the proposition, extra record registration or environment extension is
  assumed. This refutes coverage of the fragment, not strengthening.

- **Is unit-probe path coverage a routine remaining lemma? Verdict: it already
  suffices for PropositionFront, conditionally on a closed positive unit.**
  UnitProbePathCoverage asks only for paths from the fixed constant minor to
  its type-valued Eq probe whenever the proposition indices are definitionally
  equal. Given the local transport laws, a path transports a two-variable unit
  guard to the probe; target carrier exposure reads the original proposition
  equality below the inserted binders. The full proposition front follows by
  the checked fresh-unit-variable construction. Neither strictness nor an
  unconditional converse is established.

- **Does the existing Pi/Box relation at least satisfy that restricted
  coverage? Verdict: refuted even at reflexive closed indices.**
  UnitProbePathCoverage.not_box uses the bare-constant invariant for any closed
  positive constant type other than Eq.rec. Thus the restricted sufficient
  coverage condition is not solved by the existing relation.

  Judgment: retain the proved transport fragment, but reject its unrestricted
  or unit-probe completeness as a live route without primitive extensions.
  The necessary extension must handle actual Eq singleton/recursor computation,
  already at reflexive indices; more beta closure or additional visible Box
  nesting cannot remove this obstruction. General primitive transport and
  coverage remain live research tasks. No strictly smaller sufficient
  irreducible front or other goal outcome is claimed.


### 2026-10-21 14:03 UTC — Construct certified Eq computation from joins

- **Certify reflexive or beta-joined Eq indices directly. Verdict: proved.**
  proofErase_beta_join_family builds every future beta/substitution comparison
  from typed beta confluence, without JointPropBetaTransport. The literal Eq
  family has a beta join when its indices do. Lifting this certificate under
  the generated proof-major binder constructs the exact certified singleton
  prefix and computes a type probe to its minor. The equality major is arbitrary.

- **Allow primitive computation inside the compared indices. Verdict:
  proved for certified computational joins.** proofErase_certified_join_family
  commutes both source computations with future beta paths, realizes their
  common output as a typed term, and uses beta confluence at that output.
  Substitution closure of certified computation handles all future interpreted
  substitutions. No confluence of arbitrary primitive computation is assumed.
  proofErase_certified_join_eq_prefix consequently builds a new certified Eq
  primitive from indices joined by existing certified primitives. This can
  iterate through nested Eq computation without a fixed depth bound.

- **Does this cover the primitive obstacle from the preceding turn?
  Verdict: yes, constructively.** certified_probe_beyond_box_beta_paths gives
  the same closed reflexive Eq probe, its certified computation to Prop, and
  the checked exclusion from every Pi/Box/beta path. Carrier guards and typed
  body comparisons pull back from any minor to its probe when the indices have
  a certified join. This is reverse-computation transport, not general forward
  primitive transport or completeness of the old path relation.

- **Is the primitive-index extension merely beta in disguise? Verdict:
  refuted by a closed nested example.** certified_nested_probe_without_beta_join
  compares the proposition ∀ P : Prop, P with a type-valued Eq probe returning
  that proposition. Their erasures have incompatible beta heads and no beta
  join. An inner certified Eq computation nevertheless joins them, providing
  the certificate for the outer probe. The outer equality proof is obtained
  by converting Eq.refl with the inner actual type equality.

  Judgment: the reflexive primitive obstacle is now discharged, with closure
  under certified computational joins and reusable reverse-computation checking
  transport. Equal indices without such joins remain outside this construction;
  existing eta/no-join examples already rule out assuming join completeness.
  A live next step is to construct future family certificates from non-join
  comparisons (especially typed eta), using the same Eq-prefix construction.
  General forward primitive transport, strong-derivation coverage and the full
  strengthening goal remain open. No strictly smaller sufficient front is claimed.


### 2026-10-21 14:13 UTC — Certify eta indices without computational joins

- **Build a future certificate directly for typed head eta. Verdict: proved.**
  proofErase_eta_head_beta specializes the scoped eta residual theorem to the
  primitive-free relation; typed beta confluence supplies its confluence
  premise. EtaHead.subst and interpreted typed substitution then give
  proofErase_eta_head_family. proofErase_function_eta_family also handles
  proof-valued functions by their reflexive erased certificate. This does not
  assume endpoint-beta transport of arbitrary joint comparisons.

- **Place non-join certificates inside the generated Eq family. Verdict:
  proved through constant-headed spines.** BetaStableFamily.const_spine uses
  beta spine inversion and the independent future certificates of all arguments.
  A future index certificate therefore gives the reflexive/requested Eq family,
  and proofErase_stable_eq_prefix constructs the actual certified primitive.
  The certificate's base comparison supplies actual index equality by reflection;
  separate semantic equality and computational-join premises are unnecessary.

- **Combine primitive paths with non-join residuals. Verdict: proved.**
  BetaStableFamily.certified_prefixes retains a future residual comparison
  after preceding certified computations on both sides. Beta commutation
  supplies residual paths at the exact original outputs; the stored family
  certificate compares those outputs after their future beta paths. Interpreted
  substitution preserves this construction. Residual equality or a common
  computational output is not required.

- **Could these certificates still conceal a join requirement? Verdict:
  checked counterexample to that interpretation.** EtaCertifiedProbe adds a
  single function variable f : Prop → Prop. The proposition indices Eq f f and
  Eq f (fun x => f x) have different syntactically normal erasures, fixed by
  every full-union computation when D does not explicitly unfold Eq. Hence
  they have no full-union join. Their future eta-family certificate nevertheless
  computes the type probe to Prop in ErasedBetaStableJoint. The proof major is
  constructed from Eq.refl by actual eta conversion, not assumed as new data.
  No extra environment declaration is needed.

  Judgment: certified Eq computation now constructively includes non-joining
  eta indices and certified prefixes before those comparisons. Carrier and
  typed-body checking pull back from a minor to such a probe with certificates
  retained. This solves the specific join restriction of the preceding turn,
  not coverage of arbitrary typed equality. Constant-headed congruence does
  not cover variable-headed applications after arbitrary substitution: a new
  beta redex can expose an argument comparison inside the substituted body.
  Coverage of such applications, broader compatible eta, and strong derivations
  remains live, as does general forward primitive transport. No GOAL.md outcome
  or strictly smaller sufficient irreducible front is claimed.
