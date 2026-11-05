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


### 2026-10-21 14:25 UTC — Future certificates under binders and application

- **Retain body certificates when a binder annotation beta-reduces. Verdict:
  proved for lambdas and dependent Pi.** BetaStableFamily.lam_common inverts
  both lambda beta paths and uses an interpreted identity into the left residual
  domain. The body certificate is reindexed before lamCommon is applied.
  BetaStableFamily.forall_sorted additionally transports the actual domain/body
  sort witnesses and their independent future comparisons. Both constructions
  retain all future substitutions, including new annotation and body redexes.

- **Apply future-related lambda bodies to joined arguments. Verdict: proved,
  with the computational-join restriction on the arguments explicit.**
  proofErase_family_inst retains the whole certificate at any typed image.
  proofErase_family_inst_joined realizes the shared argument output as a typed
  term, instantiates the body certificate there, and uses certified image
  computation to connect both original instantiations to those residuals.
  proofErase_family_apply_lams_joined then handles the two displayed beta
  redexes. The resulting certificate includes arbitrary future substitutions
  and beta paths; it is not just a comparison before the application contracts.
  This does not settle paired instantiation at arbitrary non-joining arguments.

- **Does the application construction merely supply an application join?
  Verdict: refuted by a typed eta example.** Apply the identity lambda to a
  function variable f, and the eta-expanding lambda to an identity-redex copy
  of f. The arguments beta-join; the bodies have a future eta certificate.
  The applications receive a future certificate, but beta-reduce to f and
  fun x => f x, respectively. These distinct normal residuals exclude a
  certified computational join of the original applications, by certified
  beta commutation and typed beta confluence at any proposed shared output.

- **Can future common certificates compose through arbitrary commonly typed
  intermediates? Verdict: refuted, even in the full joint union.** For a closed
  registered positive empty structure, its constructor has a future comparison
  against either of two distinct variables: the null field telescope needs no
  residual premises. Symmetry gives both links through the actual typed
  constructor, while bare-variable injectivity excludes their composite.
  Beta and arbitrary future substitution certificates do not repair this
  failure. Proposition-only or carrier-indexed composition is not refuted.

  Judgment: binder handling and displayed application at joined arguments are
  constructive additions to the future-certificate fragment. Arbitrary paired
  instantiation and application after function substitution remain open. Reject
  unrestricted common-certificate transitivity as an induction invariant for
  strong derivations; the counterexample carries all actual typings and future
  certificates. A carrier-indexed future invariant or proposition-specific
  composition is still live. No GOAL.md outcome is established.

### Future carrier certificates and the composition front (2026-10-21 14:33 UTC)

- **Retain the supplied carrier through every future beta/substitution path.
  Verdict: constructed, with independent closure lemmas.** BetaStableCarrier
  quantifies over independent carrier and endpoint beta paths, both locally
  and after every interpreted context substitution. It is closed under beta,
  substitution, symmetry, subsingleton carriers, and dependent function
  checking. The function case reindexes its body certificate into the residual
  domain. At literal sorts it is equivalent to BetaStableFamily. Thus it
  repairs the previous distinct-unit-variable counterexample at the literal
  unit carrier without weakening the proposition observation.

- **Does this repair make typed composition a smaller front? Verdict: no
  reduction in difficulty established; a conditional full-front implication
  is checked.** TypedFutureCarrierComposition requests only an ordinary target
  guard after composing two full future certificates through an actual common
  typed intermediate. For any source relation, even False, composition into
  ErasedJointUnion implies PropositionFront when a closed positive empty
  structure is available (with the stated Eq registry/unfolding assumptions).
  Its constructor supplies both future input certificates at the Eq probe
  carrier. Upper proposition conversion supplies all actual typings there;
  distinct variables force exposure of that carrier, reading out the lower
  proposition equality. No general beta-transport assumption is used.

- **Can the source primitive stage bound such composition? Verdict: refuted
  even for these full future certificates.** A reflexive-index Eq probe in a
  two-variable unit context gives a checked negation of composition from any
  source relation into stage zero. The input certificates may have no
  primitive computation at all; stage zero cannot expose the probe carrier.
  This is not a failure of composition into the union or of strengthening.

  Judgment: future paths alone do not discharge the type-conversion work
  hidden in typed composition. A remaining direction is to require explicit
  certificates for the typing conversions that assign the intermediate and
  endpoints their supplied carrier, then test closure through those conversion
  certificates. Free carrierChecked embedding of constructor comparisons is
  exactly what admits the hard probe here. This direction remains unproved;
  no strictly smaller sufficient obligation or other GOAL.md outcome is claimed.

### Explicit type computation in future carrier certificates (2026-10-21 14:40 UTC)

- **Carry a certified type computation into every future check. Verdict:
  proved in the pullback direction.** BetaStableCarrier.certified_carrier_prefix
  transports a future certificate at a computation's output to its actually
  typed input carrier. Commutation with arbitrary carrier beta paths and
  interpreted substitutions retains the entire certificate, including endpoint
  futures. BetaStableCarrier.certified_prefixes separately handles certified
  computation of both endpoints at independently supplied actual types. Neither
  theorem assumes arbitrary typed composition or general type conversion.

- **Use explicit proposition-conversion evidence to repair the unit/probe
  composition. Verdict: constructed, including non-joining indices.**
  eqTypeProbe_future_carrier_of_family uses the index future certificate to
  compute the carrier, then pulls back the full future certificate at the
  minor. The subsingleton specialization handles every pair of endpoints.
  future_unit_probe_composition_nonjoining_indices supplies actual common
  typings, two primitive-free future links through the unit constructor, an
  absent stage-zero composite, and a full future composite in the union.
  Its indices are the eta-related propositions Eq f f and Eq f (fun x => f x),
  whose erasures have no union computational join. Thus the explicit conversion
  evidence is sufficient in a case beyond a joined-index criterion.

  Judgment: this discharges a concrete instance of the last turn's composition
  barrier by retaining the missing conversion evidence. It does not derive
  that evidence from arbitrary declarative conversion, transport certificates
  forward through arbitrary primitive computation, or establish general
  composition. The next substantive test is whether future comparison of two
  actual carrier types suffices for carrier transport, and which branches of
  that transport can be derived from comparison syntax. Simply wrapping the
  existing structural/beta paths was rejected as duplicate work. No GOAL.md
  outcome is established.

### Future carrier checking from type comparison (2026-10-21 14:49 UTC)

- **Read every future type comparison in inferred mode. Verdict: proved.**
  BetaStableFamily.types_inferred replays the endpoint beta paths at their
  independent actual sort types and uses interpreted substitution for later
  contexts. It consumes the comparisons already retained by the input rather
  than a global primitive substitution or endpoint-beta transport law.

- **Replace prescribed carrier computation by future comparison with an
  empty family. Verdict: proved at the same primitive relation.**
  BetaStableFamily.unit_carrier exposes the target family independently at
  every future target-carrier beta residual, including after substitution.
  proofErase_future_unit_carrier derives its inferred comparison from actual
  type typings. Parameters may contain redexes. No global primitive
  substitution closure or literal type join is needed.

- **Must a certified comparison itself retain futures to transfer a structural
  subsingleton? Verdict: no.** An ordinary certified type comparison already
  extracts a certified computation to a structural subsingleton, by the prior
  recursive comparison theorem. The new carrier-prefix operation turns that
  path into a full future output certificate. This covers arbitrary dependent
  Pi telescopes ending in an empty structure, not only a displayed unit.

- **Does this construction merely hide a join of the carrier types, or require
  an already structural target? Verdict: both limitations refuted.** The
  checked example compares P → Unit with Q → K(Unit), where K is a closed
  reflexive Eq type probe. The domains P = Eq f f and Q = Eq f (fun x => f x)
  have no union computation join, and Pi-domain inversion rules out a join of
  the full carrier types. Eq.rec at the target codomain excludes a structural
  subsingleton certificate there. An ordinary certified type comparison still
  supplies its full future guard.

  Judgment: comparison-based carrier transport closes constructively for this
  subsingleton fragment. General carriers with data fields still require
  transport of their dependent field checks; arbitrary type comparison has
  not been shown to supply that transport. Function domains/bodies with
  genuinely non-subsingleton results and general composition remain open.
  No full equality coverage or GOAL.md outcome is claimed.

### Full future certificates for nonempty dependent records (2026-10-21 14:57 UTC)

- **Preserve record checks while parameters, majors and earlier-field recipes
  change. Verdict: proved for both field-checking constructors.**
  BetaStableCarrier.record_fields lifts future common projection comparisons.
  BetaStableCarrier.record_nested lifts full future carrier checks at the exact
  dependent field recipes. The prior projectionType_beta and
  projectionType_subst lemmas identify the residual recipes after parameter
  and left-major beta paths and arbitrary interpreted substitution. No global
  type-conversion, endpoint transport or primitive substitution law is used.
  BetaStableFamily.proj separately preserves future inferred major comparison
  under projection.

- **Does recursive future checking add anything beyond empty structures or
  common future comparison? Verdict: checked separation at Box Unit.**
  BetaStableCarrier.box uses the actual one-field constructor recipe, whose
  field carrier is its type parameter. Two distinct actual variables of Box
  Unit have a full future guard from the unit field certificate. The registered
  Box has one field, so the original SubsingletonCarrier grammar rejects it;
  bare-variable injectivity excludes their common future comparison. The
  variables are definitionally equal by the checked reflection theorem. This
  is a distinction between checking certificates, not a strengthening failure.

- **Test dependence on an earlier field rather than just a parameter. Verdict:
  proved for a registered Pack constructor (A : Type) → A → Pack.** Its first
  projection carrier is Type, and its second is the first projection of the
  left major. BetaStableCarrier.dependent_pair consumes a future comparison of
  the type fields and a future value check at that changing first projection.
  The exact recipes and their full future record assembly are checked; no
  constant-field approximation or subsingleton premise is used.

  Judgment: record assembly and preservation through beta/substitution no
  longer require a separate general transport assumption. The input recursive
  field certificates still have to be constructed. In particular, arbitrary
  comparison of record carrier parameters/majors has not been shown to supply
  the corresponding dependent-field conversion checks. General composition
  and paired instantiation remain open; no GOAL.md outcome is established.

### Future constructor comparison and full typed structure eta (2026-10-21 15:06 UTC)

- **Retain constructor-to-major comparison through independent futures.
  Verdict: proved for arbitrary retained fields.**
  BetaStableFamily.struct_fields splits a constructor beta path into its
  parameter and field paths. Each retained field's future certificate compares
  the new field with the corresponding projection of the new major. Original
  proof markers remain proof markers under beta and substitution; newly erased
  fields may be skipped. The result requires no primitive closure law.

- **Cover the actual structure-eta rule, rather than merely request future
  field checks. Verdict: proved for every typed admissible expansion.**
  proofErase_structure_eta_family obtains typings of each projected field from
  the actual typed expansion. Its reflexive field certificate follows from
  typed beta confluence, and struct_fields assembles the expansion's full future
  comparison. The proof includes dependent field telescopes, proof fields and
  whole-proof erasure. No canonical Eq or primitive-confluence hypothesis is
  needed for this forward coverage theorem.

- **Is the resulting structure-eta certificate just a computation join?
  Verdict: refuted for retained variables.** Under the stated constructor
  unfolding exclusion, a typed variable's expansion preserves its constructor
  head throughout full-union computation, while the variable remains fixed.
  structure_eta_future_without_join proves the full future certificate and
  absence of a union join without normalizing parameters or projected fields.

  Judgment: actual structure eta is now covered by the future relation, and
  the earlier empty-constructor certificate is a specialization of the general
  constructor rule. General compatible application/paired instantiation and
  typed composition remain unresolved. Projection reduction of displayed
  constructors is a concrete next interaction to test using the retained field
  certificates and certified computation prefixes. No GOAL.md outcome is claimed.


## 2026-10-21 15:18 UTC — Full future comparison through typed projection

- **Select a retained future constructor field across projection iota.
  Verdict: proved without a join of the majors.**
  BetaStableFamily.primitive_prefix uses an ordinary primitive's exact beta
  residual and raw substitution theorem. project_constructor selects the
  indexed field and preserves its complete future certificate. These raw
  theorems need neither typing nor primitive confluence.

- **Extend projection beyond the displayed-constructor branch.
  Verdict: proved for arbitrary typed joint comparisons.**
  proofErase_joint_project_typed inducts over the whole joint comparison
  grammar. Inferred cases include applications with recursively checked carrier
  arguments. A lambda cannot type as a projection major; a displayed constructor
  selects its smaller field guard; computation replays and projects at the
  original major and field types. Carrier-only conclusion cases are impossible
  by the comparison index. proofErase_joint_project needs only the left field
  typing and obtains the right one by sound reflection.

- **Retain arbitrary future major certificates through projection.
  Verdict: proved, including iteration.** proofErase_future_project splits
  future beta paths of retained projections into major paths, types their
  residuals by forward beta replay, and applies joint projection closure.
  Proof-valued projections collapse on both sides. Interpreted substitution
  supplies new actual typings and the input's substituted future certificate.
  proofErase_future_union_project discharges all primitive premises in the
  concrete canonical-Eq joint union. Its output can be projected again.

  Judgment: general typed projection is no longer an open compatibility case
  for this future invariant. This does not prove compatibility with arbitrary
  application, arbitrary paired instantiation, general carrier conversion or
  typed composition. Those remain substantive gaps; no smaller sufficient
  front or GOAL.md success is claimed. Next investigate application of a future
  function comparison to an unchanged typed argument before unequal arguments.


## 2026-10-21 15:29 UTC — Shared application refutes the outer future invariant

- **Apply arbitrary future common function comparisons to one shared typed
  argument. Verdict: refuted by fully typed selector lambdas.** For distinct
  variables x,y of a positive empty structure S, compare `fun f : S → S => f x`
  and `fun f : S → S => f y`. unit_selector_family supplies their full future
  certificate at any source primitive collection, including False. Ambient
  substitution preserves the bound neutral head f; beta changes only its
  argument, which is accepted by the unit carrier guard. Applying both to the
  typed identity beta-reduces to x and y. Bare-variable injectivity excludes a
  future common output even in the full joint union. The closed-unit context
  theorem supplies the actual context and all typings, conditional on the
  specified registration; no environment-extension construction is claimed.

- **Invert a future lambda certificate to get a future body certificate.
  Verdict: refuted for the same selectors.** unit_selector_body_not_future
  instantiates a proposed body certificate with the actual identity, using the
  already-proved family instantiation theorem. Beta again exposes the distinct
  variables. Ambient future substitution is therefore not a hereditary binder
  invariant. Existing lam_common is a construction rule, not an equivalence.

- **Repair shared application by retaining a future result carrier.
  Verdict: already implies PropositionFront under the closed-unit hypotheses.**
  TypedFutureCarrierApplication requests a future carrier certificate for the
  applications at their actual result type. Assign the selector lambdas a Pi
  whose result is an Eq probe definitionally equal to S. Their source future
  certificate still uses no primitive computation. The output's stored beta
  paths expose x,y at the probe carrier; carrier exposure must reduce its
  Eq.rec head and therefore descends the hidden proposition equation.
  propositionFront_of_closed_unit packages the full implication, including
  when Source=False. This is not a strict reduction or a strengthening
  counterexample; it demonstrates that this proposed general repair retains
  the original difficulty.

  Judgment: the general shared-application route for outer common future
  certificates is closed by a concrete counterexample. Arbitrary future
  carrier output is not a demonstrated smaller substitute. The data-valued
  counterexample does not refute proposition-only/sort-typed application;
  investigate that restriction and which hereditary body information it needs,
  without assuming the disproved inversion of lam_common. GOAL.md remains open.


## 2026-10-21 15:35 UTC — Proposition-only application retains the full front

- **Restrict future shared application to proposition-valued functions.
  Verdict: it still implies PropositionFront under the closed-unit hypotheses.**
  unit_prop_selector_family constructs full future certificates for
  `fun f : S → Prop => f x` versus `fun f : S → Prop => f y`. The bound predicate
  remains neutral after ambient substitution and beta, so the unit carrier
  accepts arbitrary residual arguments. The source relation can be False.
  TypedFuturePropositionApplication asks only for proposition-valued results,
  yet native_unit_guard reads out a unit-value guard at the shared predicate's
  declared domain B when ordinary typing assigns it S → Prop.

- **Does using a neutral predicate merely introduce a context artifact?
  Verdict: no; the target guard returns to the original context.**
  unit_carrier_conversion adds a fresh predicate declared B → Prop and assigns
  it S → Prop using S ≡ B. After native readout, an exactly recovered predicate
  inhabitant removes that binder by forward typed substitution at a finite
  stage. No inverse weakening or general recovery re-synthesis is assumed.

- **Test the restricted application law against the unit-valued Eq probe.
  Verdict: the original front is recovered.** unit_probe_descend transports
  distinct actual unit variables to the probe carrier. Bare-variable
  injectivity rules out common checking; carrier exposure must change the
  Eq.rec head, reading the lower proposition equality. The closed-unit wrapper
  derives PropositionFront even with source False. This is a conditional
  implication, not a converse or a strict reduction.

  Judgment: proposition-only future application remains an unproved,
  full-strength route; it is not rejected as false or too difficult. Restricting
  the result sort alone does not eliminate converted native domains. The next
  constructive work must address that conversion/exposure step itself (or
  return to the original confluence residue), rather than introduce another
  outer future certificate and assume its application closure. None of the
  three GOAL.md outcomes is established.


## 2026-10-21 15:41 UTC — Construct future record conversion in supported cases

- **Retain the whole future record guard through an actual future type
  comparison. Verdict: proved for stored common field certificates.**
  proofErase_future_compared_record_guard replays independent target-carrier
  and left-major beta paths, then applies the existing ordinary compared-record
  construction to the residual typings. Future field comparisons handle both
  major paths. After interpreted substitution, the source remains the same
  registered family with mapped parameters. Universe-dependent proof-field
  flags are transferred using actual typings at each target exposure. The
  concrete union specialization needs only local family unfolding exclusion,
  not arbitrary primitive substitution or general carrier conversion.

- **Use certified type conversion inside recursive record fields.
  Verdict: constructed for converted structural-subsingleton fields.**
  proofErase_future_box_compared_subsingleton obtains the target parameter's
  full future guard from an ordinary certified type comparison, then builds a
  nonempty Box guard. The whole Box carrier is proved outside the structural
  subsingleton grammar. proofErase_future_dependent_pair_compared_field uses
  the same conversion where the carrier is the first projection of the left
  major, and combines it with a stored future comparison of the type fields.
  Value-field common comparison and source/target type joins are not premises.
  Actual endpoint typings remain necessary for reflecting the raw guards.

  Judgment: these are constructive conversion cases with explicit stronger
  input certificates, not general dependent-field conversion. In particular,
  ordinary type equality alone supplies none of the required type comparison
  certificates. The main goal remains open. Next investigate extracting a
  future field-carrier certificate from an already supplied future Box guard,
  so non-subsingleton field conversion can be used without reconstructing the
  source guard from common field comparisons.


## 2026-10-21 15:53 UTC — Recover full future field guards from typed Box guards

- **Invert an arbitrary supplied Box carrier certificate. Verdict: proved.**
  proofErase_box_field_guard handles every constructor of the joint checking
  grammar. Common checking projects using actual typings; endpoint computation
  replays both majors; carrier computation exposes and replays the single
  parameter. The nonempty registration excludes structural-subsingleton
  checking. Both record introduction forms select the retained field, and the
  exact constructor recipe identifies its carrier with the parameter.

- **Keep all future information during this readout. Verdict: proved.**
  proofErase_future_box_field_guard replays independent parameter and major
  beta paths, converts the residual majors and their projections using those
  actual equalities, and applies ordinary readout. Interpreted substitution
  realizes the new context and preserves all supplied typings. Combined with
  the existing Box constructor, proofErase_future_box_iff is an equivalence.
  The concrete union wrapper derives projection typings from registration and
  discharges primitive descent using canonical Eq and sound declarations.

  Judgment: nonempty Box checking now exposes its recursive field certificate
  without requiring common comparison of the values. This is an exact
  decomposition at a fixed parameter, not general carrier conversion and not
  a strictly smaller sufficient strengthening obligation. All GOAL.md success
  conditions remain open. The next dependency to examine is the two-field
  dependent record: symmetry swaps the major supplying the value-field type,
  unlike Box symmetry, which keeps the parameter. A readout there must account
  for transport between the two first projections; simply copying this Box
  induction would leave that conversion step unproved.


## 2026-10-21 16:02 UTC — Dependent readout and closed-carrier transport

- **Read a dependent value guard at one of the two type fields.
  Verdict: exact ordinary and future decompositions proved.**
  DependentPairFieldCheck stores common checking of projection zero and a
  disjunction of value-field guards at the left or right projection zero.
  Ordinary readout handles all joint constructors: symmetry exchanges the
  alternatives, and endpoint computation pulls back both the chosen field
  carrier and the value projections. Either alternative reconstructs the pair
  guard. Actual projection typings come directly from registration.
  proofErase_future_dependent_pair_iff retains these field checks at every
  future major residual and interpreted substitution. Orientation may vary
  between residuals; no quantifier is exchanged with the disjunction. Type
  fields separately retain a full future common comparison. No independent
  future carrier path or uniform left-field value certificate is asserted.

- **Transport an arbitrary whole guard from a rigid carrier with no arguments.
  Verdict: constructed, including full future certificates.**
  proofErase_compared_closed_carrier_compute uses an actual supplied type
  comparison to expose the same head and zero term arguments in the target.
  Source and residual target typings force zero universe arguments too, so
  the exposure reaches the exact source constant. This preserves any stored
  source guard by carrierCompute. proofErase_future_compared_closed_carrier
  repeats exact exposure after each target beta path and interpreted
  substitution, retaining arbitrary endpoint paths and recursive field checks.
  The union wrapper needs canonical Eq, sound declarations, record registration
  and local unfolding exclusion. It does not require common value comparisons
  or a structural-subsingleton certificate.

- **Use that exposure in an actual recovered application domain.
  Verdict: the application comparison is constructed.**
  proofErase_joint_application_of_compared_recovery_closed_carrier extracts
  the recovered Pi domain and its comparison with the assigned constant type.
  Exact target exposure transports the supplied argument guard into that native
  domain, and appCarrier closes the application comparison. Recovery and its
  actual type comparison remain inputs, not consequences of arbitrary typing.

  Judgment: arbitrary dependent-value guards can now pass through conversion
  from a closed rigid carrier; this goes beyond common-field reconstruction.
  It does not settle parameter-changing conversion, arbitrary source-carrier
  computation prefixes, or production of the comparison certificates from
  original typing derivations. In particular, the one-way target-to-source
  computation does not justify pushing an existing target guard forward along
  that computation. Next address that missing propagation while retaining the
  actual supplied type comparison. None of the GOAL.md success conditions is
  established; these are constructive cases, not a smaller sufficient front.


## 2026-10-21 16:11 UTC — Semantic readout at closed rigid carriers and sorts

- **Move a guard forward to an equal closed rigid carrier despite source
  computation prefixes. Verdict: proved without type-comparison transport.**
  proofErase_joint_carrier_to_closed_rigid inducts over the supplied guard.
  Actual head injectivity identifies each exposed registered carrier with the
  exact target constant: both universe and term argument lists are empty.
  Function carriers are separated from the target; carrier computation is
  replayed and eliminated. Endpoint computations and common checking survive
  unchanged. Only the carrier needs an actual typing; endpoints may stay raw.
  proofErase_future_carrier_to_closed_rigid retains the full future certificate
  using substitutable actual equality in every realized context.

- **Consume an arbitrary sound computation to that constant. Verdict: forward
  ordinary and full future transport proved.** Computation replay produces the
  actual carrier equality, so proofErase_future_carrier_compute_closed does
  not require primitive substitution or beta commutation. The computation
  establishing exposure may differ from those internal to the supplied guard.
  Combining this readout with backward transport gives a future-guard iff from
  a future type comparison. With certified primitives, an ordinary certified
  comparison already suffices: its exposure path provides backward future
  transport, and only soundness is needed for the forward direction.

- **Read an arbitrary guard at a type equal to a universe. Verdict: exactly
  common checking, including full future certificates.**
  proofErase_joint_carrier_semantic_sort separates a sort from every exposed
  function or registered-record carrier. Replaying source carrier computations
  leaves only common checking, endpoint computation and symmetry.
  proofErase_future_carrier_semantic_sort_iff needs ordinary actual equality
  only, not a type-comparison certificate, primitive-head condition or a path
  exposing the sort. This supplies a semantic target-sort decoder but does not
  generate a carrier guard from arbitrary original equality.

  Judgment: source computation prefixes are discharged for already exposed
  closed rigid and sort targets. This is a stronger direction than the preceding
  backward conversion result, but not general semantic head exposure or
  strengthening. The live next case is a parameterized Box target: exposed
  source/target parameters are actually equal, and converting its recursive
  field guard remains necessary. Test whether the closed-carrier and sort
  readouts can serve as constructive base cases for nested Box conversion.
  Function targets additionally change binder contexts. None of the three
  GOAL.md success conditions is established.


## 2026-10-21 16:20 UTC — Semantic Box closure and a finite target fragment

- **Lift parameter readout through a nonempty Box. Verdict: proved.**
  CarrierReadoutAt records the local property at a fixed actual context and
  target: any guard at an actually equal sort-typed source reads at that target.
  CarrierReadoutAt.box derives the property for Box C from the property for C.
  Actual rigid-head injectivity identifies the source family, empty universe
  list and sole parameter B; native family typing gives B : Type, and the head
  argument equation gives B ≡ C. Recursive field checking uses the supplied
  parameter readout at B. Common-field introductions need no field conversion.
  Carrier computation prefixes are replayed, function cases are impossible,
  and nonempty registration excludes the structural-subsingleton source case.

- **Discharge the recursive parameter property at arbitrary finite Box depth.
  Verdict: ordinary and full future readout constructed.** ClosedBoxCarrier
  consists of sorts and closed rigid constants, closed under explicitly
  registered Box constructors. Actual typing is checked separately, enforcing
  the parameter's Type level at every nesting. Its readout theorem uses the
  proved sort and closed-carrier bases, then Box closure. Targets contain no
  context variables and their typed erasures are beta fixed. Actual source
  equality and full future guards therefore transport into these targets
  after every interpreted substitution and independent endpoint beta path.
  No type-comparison certificate or source computation path is required.

- **Consume a recovered domain in the fragment in an actual application.
  Verdict: constructed without a separate type-comparison certificate.**
  ClosedBoxCarrier.application replays the supplied Pi recovery, reflects the
  equal erased domains to identify its actual domain with the fragment target,
  and uses uniqueness to relate the originally assigned domain to that target.
  Readout transfers the source argument guard and appCarrier closes checking.
  Existence of the displayed recovery remains an input; arbitrary original
  functions are not claimed to recover into this fragment.

  Judgment: parameter-changing conversion is now constructive for this finite
  nested-Box target grammar, including arbitrary source computation prefixes.
  The grammar is a sufficient fragment, not a strictly smaller sufficient
  strengthening obligation. Targets outside it, notably arbitrary neutral or
  computed parameters and function carriers, remain open. Adding function
  targets must address changed binder contexts and recovery there, rather than
  assume that the current ambient future certificate supplies a future body
  certificate (that inversion was previously refuted). This is the next live
  structural extension to test. All GOAL.md success conditions remain open.


## 2026-10-21 16:42 UTC — Typed recovery through rigid terminal replacements

- Idea: changing a binder to an equal closed rigid type can alter a recovered
  result, while typed head separation still forces every recovered Pi domain
  to remain exact. Verdict: proved for all scoped recovery constructors.
  RigidResultChange permits arbitrary source-to-closed-rigid replacement and
  recursive changes only in Pi codomains. Its raw relation has no unconditional
  Pi inversion; actual equality and source typing exclude the wrong-head case.
  Typed sort and record inversion likewise preserve the exact exposed carrier.
- Computation transport mirrors domain computation and discards a replaced
  terminal computation. Typed recovery handles lambdas, applications,
  projections and arbitrary result computation prefixes. A concrete single
  binder replacement and a certified specialization discharge the primitive
  premises. No inverse weakening or general head-exposure axiom is used.
- Judgment: this supplies the recovery ingredient for typed joint context
  transport. Recovery alone does not move argument guards or prove function
  carrier conversion. Full joint transport is the next step; all three GOAL.md
  success conditions remain open.


## 2026-10-21 16:41 UTC — Full typed context transport and closed function readout

- Timestamp correction: the preceding recovery entry was recorded at 16:40 UTC;
  its 16:42 heading was ahead of the wall clock.
- Idea: exploit the exact recovered domain in a typed induction over the full
  joint judgment. Verdict: proved. JointCheck.rigid_oracles transports both
  checking modes, retaining raw endpoints and carrier syntax. Actual context
  equality supplies forward typing and erasure compatibility. Applications
  reuse their argument guard at the exact domain; function bodies extend the
  same binder on both sides; nested records retain their exact field recipes.
  The single closed rigid binder replacement is proved for both modes and
  specialized to certified primitives.
- Idea: use this transport to read a function guard at an actually equal target
  Pi whose domain is closed rigid and codomain lies in ClosedBoxCarrier.
  Verdict: proved for arbitrary typed source endpoints and source carriers,
  including carrier computation prefixes and all guard constructors. Pi
  equality supplies domain/codomain equalities. The ordinary function rule
  supplies a body guard, which moves through the equal binder and is read at
  the target codomain. Structural Pi subsingletons supply body guards directly.
  This does not invert a future lambda certificate.
- Full future readout also holds: the closed function target is beta fixed,
  endpoint beta paths replay with their typings, and interpreted substitutions
  preserve the target syntax. A certified specialization discharges every
  primitive premise. No unrestricted union substitution theorem is claimed.

  Judgment: function carriers now enter the constructive target fragment.
  Source types are unrestricted but targets still have one closed rigid domain
  and a closed nested-Box codomain. Arbitrary function domains, dependent target
  codomains and general semantic head exposure remain unresolved. Recursive
  function codomains are a live extension; the general argument must eventually
  handle changes of recovered domains, rather than merely accumulate closed
  examples. These results do not establish any GOAL.md success condition.


## 2026-10-21 16:51 UTC — Recovery with recursively changing Pi domains

- Idea: fixed recovered domains are unnecessary if the actual type relation
  exposes related new domains and the smaller argument guard can transport.
  Verdict: recovery proved for RigidTypeChange. It retains arbitrary identical
  subtrees, replaces arbitrary source subtrees by closed rigid constants, and
  recursively changes both the domain and body of a Pi. Unlike the preceding
  RigidResultChange, Pi domains may change at every depth.
- Raw Pi/sort inversion is deliberately not imposed: raw closed replacements
  allow incompatible source heads. Actual equality and source typing exclude
  those cases. Registered record carriers remain exact. Typed structural
  subsingletons transport recursively using Pi equality and equal contexts.
- The relation survives arbitrary raw substitutions. Both source and target
  beta paths have matching paths preserving the relation. Typed scoped
  computation also simulates, moving recursive body computation through the
  changed domain context. All scoped recovery constructors now preserve this
  relation, including projections and computed recovered results.

  Judgment: this supplies genuinely changed recovered argument domains without
  semantic head exposure or carrier-domain re-synthesis. The full joint
  induction must still consume the related domain and adapt the argument
  guard. Coverage of arbitrary actual type equality is not assumed.


## 2026-10-21 16:52 UTC — Changed argument guards, full futures, and the primitive boundary

- Idea: let the smaller carrier branch of the full joint induction adapt a
  recovered argument domain, using typed recursive rigid recovery. Verdict:
  proved for every joint constructor. Context oracles and carrier types may
  change simultaneously; actual type equality is supplied separately. The
  application case replays both recovered Pis, obtains their actual domain
  equality, and invokes the smaller argument guard at the related new domain.
  Function guards extend the equal contexts by related changed domains.
  Record field recipes remain exact. Certified context transport follows.
- Concrete higher-order consequence: a binder of type Pi A B may become
  Pi K B whenever A equals the closed rigid type K. B may be an arbitrary
  dependent codomain; the whole binder need not be closed. Its body checking
  remains certified. This goes beyond retaining recovered domains.
- Full future carrier transport is also proved for the recursive relation.
  Target carrier beta paths need not be trivial: match them on the source,
  replay both carriers and endpoint paths with actual typings, and transport
  the residual guard. Arbitrary interpreted substitutions preserve the raw
  relation, so the same argument handles all futures. The certified wrapper
  assumes no whole-union substitution or proposition beta principle.
- Does recursive domain change plus finite beta closure now cover arbitrary
  type equality? Verdict: refuted by a checked closed canonical-Eq example.
  Every typed TypeChangePath over RigidTypeChange that starts with a literal
  sort beta reduct retains that exact reduct. Closed replacement cannot break
  this invariant: typed beta replay and sort/rigid separation exclude it.
  The reflexive closed Eq type probe is definitionally that sort but has an
  Eq.rec head that beta cannot remove. rigid_beta_paths_not_complete proves
  the missing path; this is not a strengthening counterexample.

  Judgment: changed argument domains and full future carrier transport are
  constructive for this larger recursive relation, but beta closure cannot
  make it complete. Adding further closed target examples cannot address this
  established primitive Eq-computation gap. The next research step should
  handle actual primitive type steps or a stronger invariant covering them,
  while respecting the earlier Eq-probe/PropFront barrier. All GOAL.md success
  conditions remain open; no strictly smaller sufficient front is claimed.


## 2026-10-21 17:04 UTC — Forward primitive binder transport when the result is a universe

- Revalidation: the previous turn made progress by proving recursive domain
  transport and refuting completeness of its beta closure. The Eq probe's
  certified computation itself was already constructed in earlier work,
  including non-joining future index certificates. The missing operation is
  forward checking transport through the primitive type change, not another
  construction of the same probe reduction.
- Idea: permit a recovered terminal to become a universe while retaining exact
  recovered Pi domains. Verdict: proved. UniverseResultChange allows changed
  sort levels; typed Pi/sort and sort/rigid separation rule out incompatible
  application and projection carriers. Pi recovery remains exact in its domain.
  The forall-recovery case rebuilds its result using the newly recovered levels.
- Can exact sort recovery be retained instead? Verdict: refuted in typed equal
  contexts. A fresh variable declared at Sort 0 recovers Sort 0, whereas after
  changing that binder to Sort (max 0 0), no recovery has the old literal output.
  The binder types are definitionally equal. Variable recovery must compute
  from its oracle, and sort computation preserves its literal level. This is
  a recovery-invariance counterexample, not a strengthening counterexample.
- Instantiate the existing shared JointCheck.transport induction with equal
  context realizations and universe-related oracles. Verdict: both typed
  checking modes transport from any actual binder type equal to a literal sort.
  No duplicate full checking induction or unproved re-synthesis premise is
  introduced. The certified specialization discharges primitive assumptions.
- Combine this forward result with recovery-based backward computation.
  Verdict: both checking modes are equivalent before and after any sound,
  substitution-closed primitive computation of a typed binder annotation to
  a literal sort. No confluence or beta-only restriction is required. A future
  proposition-index certificate constructs the Eq type probe computation, so
  its universe-valued binder and its minor have the same certified body
  comparisons and carrier guards. Its indices need not have a computational
  join, and its equality major is arbitrary.

  Judgment: the universe-valued primitive probe now has constructive two-way
  ordinary checking transport. This does not supply future certificates for
  arbitrary proposition equality, nor handle arbitrary primitive result types.
  The latter remains the live forward-transport problem; the earlier head
  exposure/PropFront barrier still prevents treating semantic equality as a
  general computational exposure theorem. All GOAL.md success conditions remain
  open, with the original strengthening sorry unchanged.


## 2026-10-21 17:14 UTC — Future common certificates fail forward delta transport

- Revalidation: the preceding exchange clarified the user's instructions and
  made no technical progress. The clean worktree remained at 31c85f5e. The
  previous research milestone transported checking through universe-valued
  primitive binder computation; arbitrary primitive result types remain open.
- Idea: resolve competing primitive type computations by preserving full future
  common comparisons along arbitrary endpoint computations. Verdict: refuted
  conditionally on a registered closed positive unit and a declared constant
  unfolding to its identity. constant_unit_application_family proves that c x
  and c y retain common checking after every beta path and every interpreted
  substitution, even with no checking primitives. Unit carrier checking handles
  the argument positions while beta leaves the constant head intact.
- unit_constant_future_compute_failure constructs certified delta-plus-beta
  paths from the actual typed applications to distinct unit variables. No
  ordinary common comparison relates these reducts, even in the full joint
  union. unit_constant_future_compute_context supplies the actual context
  [Unit, Unit]; ambient typings are not extra existence assumptions.
- The reducts retain a full BetaStableCarrier certificate at their unit type,
  including carrier/endpoint beta and interpreted substitution. Thus this
  obstruction rules out unrestricted common-certificate endpoint transport,
  not carrier-aware endpoint transport or proposition-only transport. This is
  stronger than the earlier ordinary common beta boundary: the inputs here
  already satisfy all beta futures. It differs from the shared-application
  boundary because existing endpoints are computed through a declared delta.

  Judgment: keep carrier information when investigating primitive computation
  forks; the unrestricted common future law cannot supply their induction
  invariant. No canonical-Eq environment or strengthening counterexample is
  constructed, and no strictly smaller sufficient front is claimed. General
  carrier-aware forward primitive transport remains live; semantic head
  exposure must not be assumed as its solution.


## 2026-10-21 17:22 UTC — Retained future bodies versus arbitrary forward carrier computation

- Revalidation: the preceding turn made progress by checking unrestricted
  common future transport false under identity delta. HEAD 82e591a2 was clean.
  Literal unit carrier futures survive that example; arbitrary supplied carrier
  conversion remained the next premise to test before using it for forks.
- Does retaining a full future carrier certificate make unrestricted endpoint
  computation a smaller obligation? Verdict: no such strictness claim is
  available. TypedFutureCarrierForwardCompute requests only source-False future
  carrier certificates, certified endpoint paths and a base output guard in
  the union. It implies PropositionFront given a closed positive unit and a
  declared identity unfolding, canonical Eq, sound definitions and the usual
  Eq/Eq.rec inertness and registry assumptions. Convert the two constant-unit
  applications to a unit-valued Eq probe; delta/beta exposes distinct variables,
  whose guard must expose the probe and descend its proposition indices. This
  is a conditional strength result, not a refutation of the carrier law.
- Retain the future eta-body recipe before changing a function domain.
  Verdict: constructive for arbitrary actual equal domains. The stored future
  substitutions include the interpreted identity between equal contexts.
  BetaStableCarrier.function_defeq_domain moves the body and reconstructs the
  full function certificate. function_computed_domain replays any sound domain
  computation, with no restriction on its result shape and with independent
  computation and checking relations. The whole-function certificate is not
  used as a substitute for the required body certificate.
- Can the retained recipe be consumed at dependent applications? Verdict:
  proved. Typed instantiation transports carrier and endpoints together.
  Certified computationally joined arguments instantiate the body at a shared
  typed realization; endpoint prefixes pull back its comparisons and a separate
  carrier prefix restores the left dependent result type. The bodies need not
  join, and the codomain need not be independent of the argument or beta fixed.
- Combine arbitrary domain conversion with paired application. Verdict:
  proved for displayed lambdas supplied with the old future body certificate.
  Equal-context erasure transports the actual body typings and recipe before
  instantiating at the new-domain arguments. No recovery re-synthesis, semantic
  head exposure or inverse weakening premise is introduced.

  Judgment: retained body recipes now support arbitrary primitive domain
  changes and dependent application at joined arguments. This is not coverage
  of arbitrary whole-function certificates or declarative equality. A general
  forward endpoint law at freely converted carriers already contains the
  proposition front, so it cannot be treated as an independently discharged
  shortcut for primitive forks. The live next step must preserve the particular
  body recipe or address the competing computations directly, rather than
  postulate that general law. GOAL.md's success conditions remain open.


## 2026-10-21 17:29 UTC — Certified binder forks and singleton root uniqueness

- Revalidation: the previous turn made progress by proving retained-body
  transport/application and the conditional strength of unrestricted forward
  carrier endpoint computation. The worktree at 1f6255fd was clean. The next
  investigation returned to actual computational forks, avoiding that global
  endpoint law as an unproved shortcut.
- Existing evidence: DeclarationConfluence already proves deterministic closed
  beta/delta confluence; repaired ordinary-core and actual prefix confluence
  also exist. JointOperationalJoins already returns exact original joins for
  the repaired definition collection. These do not supply erased residual
  guards, and must not be presented as new certified confluence results.
- Does a changing binder add an independent confluence obligation? Verdict:
  no, for a sound relation closed under interpreted substitutions with primitive
  constant/projection heads. ScopedConfluentAt at a displayed lambda or Pi is
  equivalent to confluence at its annotation and body in the original context.
  Existing typed binder inversion gives the forward paths. Annotation replay
  reindexes residual body paths to each output domain. Conversely, forks in
  either component embed into the binder and project from any common reduct.
  Only the initial annotation needs typing; the raw body may be unrealized.
- Certified specialization: proved both equivalences for ErasedBetaStableJoint
  without any global proposition beta law or whole-union substitution premise.
  This improves on the earlier conditional union-lambda join theorem but does
  not prove component confluence, application joins or full confluence.
- Can two certified singleton choices at one source disagree on their output?
  Verdict: no. Registration, exact universe instance and supplied arity uniquely
  determine all fields of valid singleton code. Telescope calculation then
  fixes its residual domains and exact output. SingletonPrimitiveWith is
  deterministic even when the two guards use different comparators, without
  source typing, canonical Eq or a transport law.

  Judgment: binder compatibility and singleton/singleton root overlaps are
  now isolated constructively. The remaining confluence work includes nested
  argument computations and singleton/ordinary-root overlaps. A useful next
  test is output congruence when the guards at both argument states are actually
  supplied; persistence of an arbitrary guard through primitive computation
  must not be silently assumed. Neither these local criteria nor root
  determinism prove full certified confluence or any GOAL.md success condition.


## 2026-10-21 17:41 UTC — Singleton output transport and computed residual telescopes

- Revalidation: the previous turn made progress on exact binder join criteria
  and singleton root determinism. HEAD 963a6147 was clean. The next target was
  singleton output congruence under argument computation, separating it from
  the unproved persistence of an arbitrary family guard.
- Use the actual equation-body capture telescope rather than posit a globally
  typed template over all recursor arguments. Verdict: constructive. The source
  guard types the fixed equation-body captures. Pointwise computation of those
  erased captures extends through the typed body using primitive renaming only;
  new captures need no chosen typed representatives. Slot selection preserves
  these paths, including proof markers and default slots.
- Saturated singleton output computation. Verdict: proved with an empty
  residual telescope. The source guard and raw argument paths give a directed
  path from the old output to the exact new output formula. No new family guard
  is needed for this output path. If a new full future guard and its empty
  telescope are supplied, certified_saturated_residual constructs the new
  certified primitive and the old-output residual to its output. The new
  source typing is replayed from the old typed source and argument paths.
- General prefix telescope computation. Verdict: proved. ScopedTelescopeCompute
  indexes each dependent annotation path by its original prefix context. It
  preserves length and combines with a body path to compute wrapped lambdas.
  Typed finite Pi inversion extracts all these annotation paths and the final
  body path from a whole residual-type computation. The existing native supply
  theorem constructs that whole path from a typed argument walk and pointwise
  argument computations, including changed later dependent domains.

  Judgment: the saturated singleton/argument fork is closed conditional on
  an independently supplied new guard. The general prefix proof now has its
  annotation paths but still needs the fresh provider vector and capture-body
  path through the changed residual telescope. This is not full singleton
  output congruence, guard persistence, confluence, or a GOAL.md deliverable.
  A concrete next route is to replay the residual-type path, recover actual
  target Pi binders from their erasures, and use actual forall-context equality
  to preserve contextVariable's proof classification. Interpreted raw identity
  substitution alone must not be assumed to preserve proof-variable status:
  its erasure agreement constrains retained variables, not hidden proof images.


## 2026-10-21 17:50 UTC — General singleton output computation

- Realize computed residual telescopes as actual converted contexts. Verdict:
  proved in ProofErasureComputedProviders. Successful raw takeForalls of a
  typed type has an actual telescope realization. Replay of the whole type
  computation and forall-context inversion give actual IsDefEqCtx between
  source and target full telescope contexts. Every fresh contextVariable is
  unchanged, by isProof_defeqCtx, even when raw annotations differ. This
  avoids the invalid inference from interpreted identity substitution alone.
- Preserve successful residual peeling under argument computation. Verdict:
  proved. Typed Pi computation retains enough displayed binders; native supply
  transports the argument vector first. Valid.telescope_compute_exists needs
  neither an old nor a new family guard. Target telescope success is no longer
  an independent premise of the existential output theorem.
- Assemble general prefix output congruence. Verdict: proved. Opened argument
  computation combines lifted supplied paths with the unchanged fresh suffix;
  the old guard types the fixed body captures. Selected capture computation,
  template substitution, and ScopedTelescopeCompute.wrapLams give the entire
  output path, including arbitrary dependent residual annotations.
  Valid.output_compute_exists produces both the new telescope and output path
  from the old guard and argument computations, without a new guard.
- Close the singleton/argument fork when its target guard is available.
  Verdict: proved by Valid.certified_residual for ErasedBetaStableJoint. Target
  source typing is replayed. A new full future family guard remains explicit.

  Judgment: this closes the previously missing nonsaturated output side of
  the fork, not its target-guard side. No global future common-comparison or
  fixed-carrier forward-transport law has been assumed; previous refutations
  and PropositionFront reductions still apply. Next investigate the guard at
  the actual singleton family after computed parameters/indices, retaining
  their native dependent carriers and the converted residual context. Do not
  replace this with the already refuted arbitrary common guard transport.
  This is progress toward the route, not a GOAL.md success condition or a
  proved strictly smaller sufficient obligation.


## 2026-10-21 18:00 UTC — Mixed singleton argument forks

- Recover a full future singleton guard through arbitrary computation outside
  the family parameter/index slices. Verdict: proved, then generalized below.
  The previous output theorem already realizes the changed residual telescope
  by actual context conversion. Retain that witness in its private helper;
  use BetaStableFamily.defeqCtx to transport the old guard. No ordinary union
  context-conversion law is assumed.
- Permit beta reduction in the parameter/index slices while all other supplied
  arguments compute arbitrarily. Verdict: proved in
  ProofErasureSingletonGuardComputation. Slice beta paths lift through the
  equal-length residual telescopes; the fresh suffix agrees exactly. The
  fixed family templates beta reduce under their changed captures, and the
  guard's stored beta future composes with those paths before actual context
  conversion. This covers unsaturated dependent telescopes and does not ask
  for a target family guard.
- Close the mixed singleton/argument fork completely. Verdict: proved by
  Valid.certified_residual_of_family_args_beta. It constructs the new telescope,
  full future union guard, certified target primitive, and old-output path.
  The family-relevant slices need beta paths to their target values; unchanged
  slices are included. Other arguments may use all certified primitives.

- Test a stronger Eq-family forward-computation obstruction using declared
  unit identities at a converted supplied carrier. Verdict: unresolved, not
  refuted. Existing stable Eq encoding produces the source guard, but decoding
  an arbitrary target union Eq guard at its supplied carrier currently needs
  interpreted substitution closure (ProofErasureEqCarrierDecode). That closure
  is proved for the certified relation, not for the full union without an
  additional unresolved hypothesis. Thus the existing supplied-carrier
  PropositionFront barrier does not by itself establish the exact general
  singleton-guard barrier. Do not silently add union substitution or conclude
  that the actual target-union guard question has been settled.

  Judgment: the remaining argument forks on this route require genuinely
  non-beta changes in the family parameters or indices. Motive/minor and other
  family-irrelevant computations, even mixed with beta family changes, now have
  a complete checked residual. General guard persistence, certified confluence,
  coverage, and the original strengthening objective remain unproved. The
  narrowed operational case is not claimed strictly smaller than PropFront or
  sufficient by itself for GOAL.md.


## 2026-10-21 18:12 UTC — Native unit Eq guards and a certified transport barrier

- Rebuild future Eq family guards at a literal unit carrier after arbitrary
  index computation. Verdict: proved in ProofErasureFutureEqUnit. Native Eq
  recovery yields the literal unit domain at the final application, where
  carrierSubsingleton checks arbitrary raw endpoints. Independent beta futures
  of the repeated anchor use its reflexive future certificate. Arbitrary
  interpreted substitution preserves the constant head and unit carrier.
  A typed anchor supplies the reflexive certificate; certified computation
  replays to a typed new anchor. No common comparison between final endpoints
  is needed, so distinct variables exposed by the earlier delta example are
  allowed. proofErase_unit_eq_prefix constructs the actual certified Eq
  singleton step at every typed non-proof literal-unit prefix, without an old
  guard, index comparison, computational join, or guard-transport hypothesis.
- Forward diagonal Eq guard computation into certified checking. Verdict:
  conditionally contains PropositionFront. TypedFutureEqFamilyForwardCompute
  is explicitly an unproved law. Source guards use no primitives, the supplied
  carrier is unchanged, both target indices are already typed there, and only
  base target checking is requested. A declared unit identity gives source
  future common index comparisons and certified delta/beta paths to distinct
  variables. Put an Eq type probe in the supplied carrier; certified Eq
  decoding reads out its carrier guard and exposure descends the hidden
  proposition equality. The closed positive unit/identity assumptions are
  explicit. This is a strength implication, not a counterexample or a proof
  of transport.
- Restrict that certified law to diagonal Eq guards over literal Prop.
  Verdict: the same conditional PropositionFront barrier remains. Nest the
  arbitrary-carrier Eq propositions as the two Prop indices; stable Eq
  encoding gives the outer source guard, and literal-sort decoding removes
  the outer target Eq. TypedFutureEqPropFamilyForwardCompute.eq_family proves
  this reduction and its closed-unit corollary proves PropositionFront.

  Judgment: literal native unit guards now have constructive non-beta
  coverage. Freely converted supplied carriers still carry the original
  difficulty at the certified target, even when the outer guard has carrier
  Prop. Do not infer the corresponding full-union result: arbitrary-carrier
  decoding uses primitive substitution, available for certified computation
  but not established for the full union. The actual singleton guard uses
  future full-union comparison; its general non-beta persistence remains
  unresolved. A base certified result and a full-future union result must not
  be conflated. No GOAL.md success condition is met.


## 2026-10-21 18:28 UTC — Future Eq encoding and the full-union transport barrier

- Encode a retained future carrier certificate as a future Eq family guard.
  Verdict: proved for arbitrary raw carriers and anchors with their retained
  future comparisons. At actual typed occurrences, reflexive carrier/anchor
  families suffice. A full future carrier certificate in ErasedJointUnion
  constructs an actual ErasedBetaStableJoint Eq-prefix step. This consumes
  the certificate; it does not synthesize or transport it forward.
- Decode the whole future Eq certificate, including independent carrier beta
  reduction and every interpreted substitution. Verdict: proved when the
  primitive relation is sound, head-preserving, Eq-inert and substitution
  closed; certified computation satisfies these premises. Future Eq and
  future carrier certificates are equivalent there. No general union
  substitution theorem is inferred.
- Replace unrestricted substitution in native Eq recovery with existing
  recoverable substitutions and contravariant domain pullback. Verdict:
  proved. Typed union Pi inversion retains the body computation in the
  original context. A recoverable anchor instantiates the body path, giving
  native Eq prefix recovery and a path from the supplied carrier to the
  selected last-argument domain. Actual body typing is required.
- Preserve the anchor recovery through arbitrary union Eq comparison by
  choosing a variable anchor. Verdict: proved. Variables remain fixed through
  computation; their recovery follows the computed carrier by conversion.
  The resulting decoder handles all inferred comparison constructors and
  returns a guard at a common ancestor carrier. This removes the missing
  unrestricted-substitution premise for the case needed by the probe test.
- Weaken the earlier diagonal Eq forward-transport law's target from base
  certified comparison to base full-union comparison. Verdict: still implies
  PropositionFront, conditionally on the same closed positive unit, declared
  unit identity/unfolding, canonical Eq, sound definitions, Eq registry
  agreement and inert Eq/Eq.rec heads. Declare the probe before the two fresh
  variables, and declare both variables at the probe itself. Their native
  recovery is then available, while actual conversion types them at unit.
  The source has a primitive-free future guard and the paths only unfold
  the identity; union target decoding exposes the probe or contradicts
  distinct-variable comparison. This closes the limitation explicitly left
  by the preceding certified-target result.
- Restrict the new union-target law to diagonal Eq over literal Prop.
  Verdict: the same conditional PropositionFront implication is proved by
  nested Eq encoding and literal-sort decoding. Restricting the outer
  supplied carrier to Prop does not remove arbitrary inner carriers.

Judgment: future carrier recipes now construct actual Eq guards, and typed
union binder computation has a constructive substitute for unrestricted
substitution. But generic non-beta forward persistence of actual future Eq
family guards is not a demonstrated smaller obligation: even its base union
output contains the original front under the stated environment assumptions.
This is not a refutation of transport or a canonical-Eq counterexample. The
full arbitrary-anchor union decoder and unrestricted substitution remain
open; neither is needed for the new conditional barrier. No GOAL.md success
condition is met. Next use typed union binder inversion/recoverable
instantiation in the computation-join argument itself, retaining native
recovery evidence, rather than installing forward guard transport as an
unproved supposedly smaller repair.


## 2026-10-21 18:38 UTC — Native residual joins from original recoverable walks

- Assemble a union binder join using the new typed Pi inversion and ordinary
  component confluence. Verdict: inversion provides contravariant body
  pullback, while assembling a binder join needs the forward direction.
  Existing DomainDirection.forward_not_recovering refutes exact recovery in
  that direction. The existing certified binder criterion has substitution
  closure and cannot be specialized silently to the union. No new binder
  confluence theorem is claimed.
- Instantiate at the original recoverable argument, then compute its images
  in the output. Verdict: this ordering already occurs in the finite-stage
  head-beta exchange proof. Extracted the union square for arbitrary typed
  bodies and combined it with typed Pi inversion. The resulting computed-Pi
  instantiation theorem needs recovery only of the original argument, never
  of its computed image. No confluence or forward context law is assumed.
- Carry original argument recoveries through a dependent native telescope.
  Verdict: proved using RecoverableNativeWalk. Computed arguments supply any
  computed initial native type, and the original residual computes to the
  deterministic raw supply result. Two such walks with pointwise joined
  arguments therefore have a full-union residual join. This generalizes the
  existing substitution-closed native-supply theorem in a different direction:
  the relation is now the entire union, with retained original recoveries.
- Control selected recovery after all prefix arguments compute. Verdict:
  proved for the recoverable walk. Every selected recovered type is reachable
  from the original native residual, even with conversions before successive
  applications. An inert constant's selected next domain is consequently
  reachable from its original native domain. Inferred comparison of two
  independently computed copies of that prefix reads out an actual carrier
  guard at the original native domain. No computed-image recovery is needed.
- Is original recovery secretly forcing computed-image recovery? Verdict:
  no, with a checked typed example. The identity expansion of the existing
  eta-converted neutral variable recovers its assigned type and beta-reduces
  to that variable, which cannot recover that type anywhere in the union.
  The directed square nevertheless transports every typed body path through
  this computation.
- Can every ordinary typed native walk supply the new invariant? Verdict:
  false. The same eta-converted variable gives a one-argument literal typed
  telescope walk with no RecoverableNativeWalk certificate. This is an exact
  premise boundary, not a strengthening counterexample.

Judgment: retained original recovery suffices for concrete union native type
joins and argument-guard extraction without the earlier unrestricted
substitution assumption. This does not solve arbitrary converted arguments,
forward binder-context computation, general guard persistence or confluence.
No strictly smaller sufficient irreducible obligation has been established.
Next investigate the remaining converted-argument case using explicitly
computed native telescopes/identity covers, keeping track of the direction
of beta paths: a cover computes to its argument, and its existence alone
cannot reverse computation or supply the missing union beta-join law.


## 2026-10-21 18:47 UTC — Identity covers remove the full-union Eq decoder gap

- Remove original-argument recovery from the previous native telescope
  theorem by an identity cover. Verdict: not justified for general dependent
  codomains: instantiation leaves cover occurrences in the native result, and
  reversing their beta paths would require an unproved transport/join law.
  The earlier recovering-substitution-cover and confluence-conditional
  instantiation results already isolate this issue; no repetition is claimed.
- Use a cover only where the native result is independent of the argument.
  Verdict: proved for all typed nondependent arrows in the full union.
  proofErase_joint_union_computed_arrow_inst covers the original argument,
  invokes the directed computed-Pi square, then computes the cover to the
  requested argument image. Instantiation of a lifted result is literally the
  original result, so no path has to be reversed. Neither the original nor the
  computed argument needs exact assigned-type recovery.
- Apply that nondependent arrow lemma to Eq's fixed anchor. Verdict: proved.
  The type of Eq α is α → (α → Prop), and its final result type is independent
  of the anchor. Every selected type recovery of Eq α z therefore computes
  from α → Prop in the entire union, with no recovery premise on z and no
  unrestricted union substitution law. Its selected argument domain is
  reached by a path from α. This resolves the earlier general native Eq
  recovery gap, rather than merely another variable-anchor special case.
- Decode arbitrary full-union Eq comparisons. Verdict: proved. Actual source
  replay supplies the carrier/anchor typings at each computation node; the
  new native result handles appCarrier. The decoder retains independently
  computed carriers, changing anchors and endpoints, symmetry, and a common
  ancestor carrier. Either comparison mode of typed Eq propositions yields
  the endpoint carrier guard. This is lossless at base union checking.
- Decode the entire future Eq certificate. Verdict: proved, including every
  interpreted substitution and independent carrier/endpoint beta residual.
  Each substituted occurrence is decoded afresh, so no union primitive
  substitution theorem is smuggled in. Under canonical Eq, sound D and no
  Eq unfolding, proofErase_union_future_carrier_eq_iff identifies full future
  Eq guards with full future carrier certificates at arbitrary typed carriers.
- Change the repeated Eq anchor without relating the two anchors. Verdict:
  proved for complete future union certificates. Both encodings express the
  same carrier guard. A future Eq guard at any repeated typed anchor now
  constructs the actual certified Eq-prefix step and its exact generated
  output, by decoding and re-encoding at the prefix's own anchor.

Judgment: the full-union arbitrary-anchor Eq decoder and its full future
version are now proved. Earlier ledger entries naming these as open are
superseded by these theorems. General dependent native-walk recovery and
unrestricted union substitution remain open; the new proofs do not require
either. This is not forward persistence under arbitrary primitive computation:
the preceding conditional PropositionFront barrier for that law remains.
No GOAL.md success condition is met. Next use the lossless full-union Eq
encoding in the simultaneous proposition/carrier beta-transport argument,
tracking source stages and proof dependencies explicitly so that decoding is
not confused with a proof of the transport law being encoded.


## 2026-10-21 18:56 UTC — Explicit primitive-free Eq beta peak

`ProofErasurePrimitiveFreeEqPeak` constructs, for every actual proposition-front
instance, four typed Eq propositions with a primitive-free source comparison
and two beta paths contracting only the final identity-application arguments.
Both carrier and anchor stay fixed along those paths. A full-union comparison
of the resulting pair descends that exact original proposition equation.
The source comparison has a fixed structural skeleton; the arbitrary lifted
equation enters through the endpoint typings at the converted Eq-probe carrier.

Verdict: checked localization of the existing beta-transport barrier, not a
new discovery that global proposition beta transport implies PropositionFront
(the latter was already proved in ProofErasureJointUnitBetaBarrier). Removing
source primitive steps or fixing the carrier and anchor does not remove that
barrier. No declared identity unfolding, global beta law, or strengthening
inverse is used. No target certificate is supplied, no nonconvertibility is
asserted, and no strictly smaller sufficient obligation is established. A
structural transport proof must still account for the typing conversion;
primitive-stage descent alone does not supply the missing base case.


## 2026-10-21 19:03 UTC — Paired lambda head beta without union substitution closure

The previous proof-argument/recovered-image head-beta results used primitive
substitution closure, or lower-stage proposition beta transport to certify
their inputs. That premise is unnecessary when the target is the full union.
`ProofErasureJointUnionHeadBeta` replaces raw lambda inversion with typed
inversion retaining both body paths under their original annotations, then
instantiates those paths through the proven recovering-substitution theorem.
The original argument's recovery extends along each computed domain path.

Verdict: five theorems checked. Full-union comparisons instantiate at an
original recoverable argument; inferred lambda comparisons close diagonal
head beta; proposition-valued applications close at same-erasure arguments;
proof arguments need no recovery; and distinct data arguments are accepted
when full-union computation takes both to a typed shared value recovering
both displayed domains. The last result allows primitive argument paths,
not only the beta paths of the earlier joined-argument interface.

No global primitive substitution, certification, semantic head exposure, or
proposition beta transport is assumed. This removes a real premise from the
paired head-beta subcase, but does not cover arbitrary carrier-related data
arguments or contextual beta transport at a converted supplied carrier. The
primitive-free Eq peak of f9104d62 is therefore still unresolved. Neither
completeness of ordinary typing conversion nor a smaller sufficient front
has been established.


## 2026-10-21 19:11 UTC — Retain original recoveries across paired computational joins

Tested removing recovery of the shared computed argument from the previous
paired lambda theorem. For arbitrary inferred function comparison, its
structural lambda case still requires instantiating a body comparison at that
image; the original-recovery computation square does not provide comparison
transport. No general extension or refutation of that extension is claimed.

A computational join of the functions gives a constructive alternative.
`ProofErasureJointOriginalRecoveryJoins` inverts both typed lambda paths under
their original binders, then instantiates each body path at its own original
recoverable argument before computing the copies to the shared image. Both
contracta reach the same literal raw output. Only each argument's own displayed
domain is recovered; no cross-domain or shared-image recovery is required.
The domains may differ. A checked eta-converted-variable example has no exact
assigned-type recovery at the shared image anywhere in the full union, yet
every pair of joined typed body paths still yields the two exact output paths.

Verdict: three theorems proved; a constructive computational subcase, not
full paired substitution. This trades the previous inferred-function premise
for an actual function join while dropping the shared-image recovery premise;
it is not an unconditional strengthening of the previous theorem. Arbitrary
carrier-related arguments still need not join, so the converted-unit peak
and the main strengthening obligation remain open.


## 2026-10-21 19:22 UTC — Retain certificates when descending computation and recovery

The existing joint descent results reconstruct actual lower typing/equality
but do not return lower checking certificates. This loses reusable evidence
when trying to localize later conversion and body checks. Investigated a
stronger certificate-preserving induction rather than assuming semantic
descent also proves this stronger property.

`ProofErasureCertificateDescent` defines the precise primitive interface and
proves compatible computation and selected recovery retain lower certificates
under arbitrary block insertion. Changing lambda/Pi annotations use actual
context conversion only to identify the output erasure; the lower body path
retains its original binder. The recovery induction reconstructs the exact
selected output, including projected field recipes and type computation.

Verdict: generic closure checked, and an unconditional stage-zero instance
checked. Core primitive descent first establishes a lower typed representative
and a lifted output; raw retraction then constructs the lower core step.
Computation and exact selected recovery have literal lift iff theorems at
stage zero. No removed binder is inhabited, and no inverse typing weakening
is used. Higher joint stages still require certificate-preserving descent of
their comparison/carrier guards. Next extend the mutual joint-check induction
using these computation/recovery results, then reconstruct singleton guards.
This is a reusable induction tool, not completeness or a smaller sufficient
strengthening front.


## 2026-10-21 19:33 UTC — Exact certificate descent for all joint stages and the union

Completed the pending mutual comparison/carrier induction. Actual semantic
source descent aligns recursive lower typings; the new induction retains the
Target checker derivation. This includes selected application recovery,
changing lambda/Pi domains, witnessed sorts, eta bodies, constructor fields,
structural subsingletons and dependent carrier projection recipes. For records,
source semantic equality realizes the lower fields at common types; it is not
used as a substitute for the recursive Target certificate.

General singleton family guards now descend beneath their actual generated
telescope with their comparison certificate intact. The lower unfolding check
is reconstructed separately using source semantic descent. Specialized Eq
prefixes retain their exact lower carrier guard. Together these close the
certificate-descent stage induction and its full-union instance. Computation,
selected recovery, common-typed comparison and carrier checking all have exact
lift iff theorems at the original stage and at the union.

Verdict: the previous entry's higher-stage task is proved, with no Target
soundness assumption in the generic construction and no carrier resynthesis,
semantic head exposure, global beta transport or inverse typing weakening.
This closes loss of checking evidence during descent. It does not establish
checker completeness, the nonjoining carrier-argument beta case, a canonical-Eq
counterexample, or a strictly smaller sufficient front. The next substantive
use is to retain these lower certificates when revisiting paired lambda-body
transport; obtaining certificates for arbitrary declarative conversions remains
an explicit outstanding problem, not a consequence of the new iff theorems.


## 2026-10-21 19:45 UTC — Paired head beta with argument-free erased bodies

Revisited nonjoining carrier arguments and comparison-directed type transport.
The general common-mode beta rule is already refuted by the unit identity
example, and the primitive-free Eq peak still carries the original front.
The old compared-subsingleton Pi proof uses arbitrary context substitution;
replacing that assumption by semantic type equality would merely hide the
unresolved carrier/recovery conversion problem. The existing eta-converted
neutral type also rules out retaining exact assigned recovery by such a step.
No general converted-context transport was assumed or claimed.

A genuine use of exact certificate descent does avoid that problem when both
erased lambda bodies omit the argument. Proved direct computation inversion:
a typed lambda with a body erasure lifted from a lower typed term retains that
form through every computation, and its lower body path stays at the same
relation. The trans case descends each residual body independently, so changing
lambda annotations require no body-context conversion or primitive substitution.
The full inferred-comparison induction then descends to the two lower bodies,
including eta-lambda and computation cases. Proposition-valued paired head beta
follows for arbitrary typed arguments at the original stage or full union.

Verdict: the argument-free case needs neither argument recovery, equal erasures,
a common computational image, nor even a carrier relation between the arguments.
A checked two-variable context witnesses simultaneous failure of both exact
assigned recoveries in the entire union and absence of an argument join; the
new theorem still applies to all its argument-free proposition lambda checks
at every finite stage. The displayed lambda domain is exactly the unrecoverable
assigned type. This closes the unused-argument branch, not all nonjoining paired
substitution. The retained-occurrence case, including the primitive-free Eq
peak, remains open. No smaller sufficient irreducible front is asserted.


## 2026-10-21 19:57 UTC — Actual universe-context transport and retained-argument beta

Revalidated the current worktree after the discussion-only turn. The original
semantic-sort carrier readout already exists; re-proving it would not advance
the goal. The existing universe-binder transport, however, requires arbitrary
primitive context substitution, unavailable for the actual joint union.
Tested removing that assumption by a simultaneous finite-stage argument.

Verdict: successful. Typed primitive transport through universe oracle changes
closes at every original stage. Source semantic replay realizes intermediate
computations; recovery conversion replays the changed result and transfers its
path using its actual typing. The shared joint checking induction preserves
exact application domains. The general singleton case extends the context
relation through its actual generated dependent telescope, retaining the
family comparison certificate; specialized Eq prefixes retain their carrier
certificate. No arbitrary substitution, semantic head exposure, carrier
re-synthesis, or proposition beta transport is assumed. The union follows
without a uniform stage bound.

Applied this to the retained-argument head-beta branch: move each displayed
lambda domain to its semantically equal literal universe before instantiating
body comparisons and body computations. The argument need recover only the
literal universe, not either displayed annotation. The whole inferred-lambda
induction includes computation and eta; the proposition-valued paired theorem
allows two arguments with the same erasure. A fresh proposition variable under
a beta-expanded Prop annotation cannot recover that displayed annotation in
the full union, yet all compared proposition bodies under that annotation
satisfy the new result, including bodies retaining the variable.

Boundary: recovery at the literal universe is still required; arbitrary
universe-valued expressions are not asserted to have this exact recovery.
Distinct nonjoining argument erasures and the primitive-free Eq peak remain
open. This is a strictly stronger checked beta case, not a proof of PropFront
or a new strictly smaller sufficient irreducible obligation. Keep the original
goal active; no PR extraction.


## 2026-10-21 20:05 UTC — Inhabited proposition recovery already carries the full front

Investigated removing the exact-universe recovery premise from the new
universe-domain paired-beta theorem. Universe oracle transport is directed:
it can replace a native result by a literal universe, but does not synthesize
recovery of an arbitrary substituted proposition. A proposed ambient-sort
recovery constructor would not inherit the existing recovery descent proof:
DomainSort.descend requires the lower source already be sort-typed, whereas
recovery descent starts with arbitrary lower typing. The older sort-recovery
and Eq-probe results confirm that general universe exposure is not a free
structural inference lemma. Literal-sort semantic strengthening alone has not
been shown here to imply the full front; do not conflate it with computational
sort exposure, whose Eq-probe implication was already proved.

Tested the much weaker fallback: request any recovered output only for
inhabited propositions. Verdict: it still suffices for PropositionFront in the
actual joint union (with the existing sound-core/registry hypotheses).
For any A : Sort u, the explicit inhabited proposition Pi (_ : A), E, where
E is the closed reflexive equality of Prop, tests universe recovery of A:
any recovery of that Pi must recover a universe for its domain. Next test a
fresh variable declared at T but converted to Sort v. Variable recovery gives
a computation from the lifted declaration to a universe; exact certificate
descent removes the fresh binder, retaining the computation. Applying this
exposure to the Eq sort probe yields the original front without a closed unit
assumption. No arbitrary primitive substitution or head-exposure premise is
used in the implication.

This checked reduction changes the next action: do not replace the missing
argument recovery by generic inhabited-proposition recovery completeness and
call it a simpler auxiliary lemma. It is a sufficient coverage obligation,
not proved coverage and not a proven strictly smaller irreducible front.
Direct comparison/paired-development arguments that avoid generic recovery
remain live. The original strengthening goal is unchanged and still open.


## 2026-10-21 20:14 UTC — Preserve the full certificate at the Eq probe's first head change

Verdict: proved. The computed general-singleton guard now returns an actual
lower JointCompare certificate for the original proposition indices, including
the index computation paths. Exact certificate descent removes both the added
context block and generated proof major. The checker compute rule restores the
original endpoints; comparison transitivity is not assumed. In the actual full
joint union, any changed probe head yields that certificate. Conversely a
certificate computes the probe to its original minor, giving exact head-exposure
and literal-universe computation equivalences under the recorded Eq/Eq.rec
inertness and registry hypotheses.

This is a lossless replacement for the earlier semantic-only readout. It does
not establish checker coverage of arbitrary semantic equality, full-reduction
head factorization through eta expansions, or a strictly smaller sufficient
front. The original strengthening obligation remains open.


## 2026-10-21 20:21 UTC — Keep the computed eta body at the original function carrier

Verdict: a local eta/computation exchange is proved for the full joint union.
The older PrefixEtaHeadExposure/NormalPrefixFactorization route assumes the
witnessed proposition front and cannot supply it. The older scoped eta residual
uses arbitrary primitive substitution to transport the body to a changed
annotation. Instead, joint lambda inversion retains the entire body computation
under the original binder. Opening the computed lambda at that original carrier
beta-contracts to the retained body, including the proof-marker case by typed
erasure. This constructs a JointCarrierGuard relating the actual computed
output to the short function without forward annotation transport.

An independently computed argument also gives an exact application join if the
original argument recovers the original domain. The computed image and computed
lambda annotation need no recovery. When the output annotation is a literal
universe, actual universe-context transport supplies an ordinary common
comparison of the computed output and short function. These are concrete
partial exchange lemmas, not arbitrary eta postponement: the carrier result
cannot be silently used as an inferred function comparison, and the general
application result still requires original-argument recovery. Full reduction
coverage, arbitrary retained arguments and strengthening remain open.


## 2026-10-21 20:26 UTC — Remove the final proof-argument eta detour, retaining the complete tail

Verdict: proved for arbitrary subsequent full-joint computation. A first-head
beta decomposition of a lambda application retains the separate function and
argument computations, the exact beta contractum, and the entire remaining
path. Literal-sort output rules out the uncontracted application alternative.
The preceding eta-body instantiation can therefore reach that exact contractum
from the short application and compose the original tail. No confluence or
comparison transitivity is needed. The reverse direction is the typed eta/beta
identity followed by the supplied short path.

Original-argument recovery is sufficient in general and automatic at a proof
domain. Applying this to the Eq probe's last five-argument prefix proves that
eta expansion followed by arbitrary joint computation reaches the original
literal universe iff the original proposition indices have a joint comparison.
The equivalence also descends across arbitrary binder insertion with an equality
major supplied only upstairs; no lower proof major is assumed.

This removes a concrete eta detour from the probe route, rather than assuming
all eta can be postponed. It does not cover eta at earlier prefixes, new eta
steps inside the subsequent full reduction, structure eta, or the unrecoverable
retained-argument case. General semantic coverage and strengthening remain open.


## 2026-10-21 20:33 UTC — Retain pending arguments and remove finite recoverable spine-eta interleavings

Verdict: proved. First-head-beta decomposition now applies to an entire lambda
application spine. Its witness retains the exact contractum, the computations
of every pending argument, and the complete remaining path. The typed eta
instantiation reaches that exact contractum from the short application; applying
the retained argument paths then composes the original tail. Only the consumed
argument needs recovery at the original domain, not any pending argument.

A literal-universe consumed argument supplies recovery directly. Consequently,
eta at the bare Eq recursor before its Prop carrier preserves the probe's exact
index-certificate criterion, including below arbitrary binder insertion with
an equality major available only upstairs. This extends the final-proof-prefix
case to an actual earlier prefix without assuming recovery of the pending
proposition indices or motive.

The local theorem also composes: the new explicitly bounded JointSpineEtaCompute
fragment allows any finite interleaving of full joint computation and typed
recoverable spine-eta steps. A continuation induction removes all such eta
steps before a literal universe, preserving that exact universe. Eq probes in
this fragment still expose their original universe iff the lower indices have
a joint comparison certificate. This is not FullReduction coverage: eta inside
arbitrary arguments, structure eta, and prefixes consuming unrecoverable retained
arguments remain outside the proved fragment. The proposition-index argument
case is not solved by the initial universe-argument example.


## 2026-10-21 20:44 UTC — Read a displayed lambda domain without recovering its codomain

Verdict: the local rule and its exact certificate descent are proved. An
application whose left function is a displayed lambda can read its argument
carrier from that annotation, compare the functions in inferred mode, and
check the arguments at the displayed carrier. Independent lower endpoint
typings suffice to reconstruct the actual domain and align the right argument.
Complete Pi recovery of the lambda is not needed. The rule also guards actual
canonical-Eq prefix computation, and finite layers above the full joint union
preserve exact computation certificates under arbitrary binder insertion.

This is a candidate for replacing the full-recovery application rule in a
larger checker, not a proved coverage improvement. The recursive function and
carrier premises still use the existing joint grammar. Inspection of
JointCheck.subst_recovering_typed confirms that nested ordinary appCarrier
cases still require recovery transport. Thus this local result does not
establish substitution by arbitrary proposition images, and no strict
comparison-coverage separation from the existing union is claimed. The
inhabited-proposition-recovery barrier remains in force.


## 2026-10-21 20:49 UTC — Test displayed-domain checking at the missing universe binder

Verdict: the immediate proposed gain is redundant, even for converted universe
annotations. A displayed-domain application certificate whose actual argument
domain is definitionally equal to a universe already gives ordinary joint
comparison at the same primitive relation. The existing semantic-sort carrier
readout removes the carrier guard, and the old app rule then suffices without
any function recovery. Its exact Eq-prefix step already belongs to the old
full joint union. No computation of the annotation to a sort is required.

More generally the local rule either already gives ordinary joint comparison,
or its argument domain computes to an exposed structure or function carrier;
the latter alternative retains the exact carrier guard. This is a necessary
condition for extra power, not a strictness witness. It rules out the direct
universe-domain application as the way this extension could fix arbitrary
proposition substitution. Nested applications at structural carriers remain
a possible use, and their substitution/coverage problem is still open.

Do not add further universe-domain stages expecting extra checking power from
this rule alone. A useful next test must address those nested structural
applications or the recovery demanded inside their function subderivations.


## 2026-10-21 20:54 UTC — Any-output lambda recovery is sufficient, but not a free coverage lemma

Verdict: checked the exact recovery requirement in the remaining structural
case. Any recovered output of the left displayed lambda suffices to embed its
local application certificate in the old joint checker: recovery inversion
returns a body certificate, and rebuilding the lambda recovers a Pi at its
original annotation. A prescribed full Pi output is unnecessary.

Uniformly supplying even this weaker-looking premise is still a major
obligation. In the full joint union, a constant lambda returning a proposition
has some recovery iff that proposition itself has some recovery. The forward
direction removes the unused binder with exact recovery-certificate descent;
the reverse direction is ordinary renaming. This holds at any typed domain,
without inhabitation or recovery of the domain. Consequently, recovery only
for constant predicates over the fixed closed function domain Prop -> Prop,
returning inhabited propositions, already implies PropositionFront. No unit
structure or extra environment declaration is required.

This is not a strictness witness for displayed-domain checking. Applications
of constant lambdas returning the same body compare in the old checker by
beta for arbitrary arguments and annotations, without any body recovery.
The checked contrast rules out using recovery-completeness as a routine way
to settle comparison coverage. Direct comparison/paired-beta reasoning for
retained argument occurrences remains the live task; no smaller sufficient
irreducible front or proof of strengthening is obtained.


## 2026-10-21 21:03 UTC — Remove eta before an arbitrary proposition index without recovery

Verdict: proved for the first proposition index of the actual Eq type probe,
and integrated into finite eta interleavings. General paired carrier
substitution still encounters the existing native-domain alignment problem.
A more specific application case avoids it: eta of Eq.rec Prop has a body
containing only Eq.rec, Prop and its fresh proposition variable. Existing
typed arity exclusion rules out every root primitive at its zero-, one- and
two-argument prefixes. This includes general singleton rules, not only core
reduction. The eta function is therefore fixed in its actual binder context.

Added scoped syntactic normality, whose primitive exclusions are indexed by
the actual occurrence context. A fixed eta function admits first-head-beta
elimination while retaining all consumed/pending argument computations and
the complete continuation. No recovery of the consumed image is needed.
For the Eq prefix that image may be any raw term; the actual probe theorem
therefore covers every typed proposition P without recovery of P at Prop.
The result preserves the exact original universe and the original lower
index-comparison certificate, including arbitrary binder insertion with the
proof major supplied only upstairs.

The existing finite JointSpineEtaCompute fragment now also admits scoped-normal
eta functions. Its continuation theorem and Eq-probe criterion survive this
extension, so the new case can interleave finitely with the previous recovered
eta cases and arbitrary full-joint computation. This closes the first
proposition-index case explicitly left out by the earlier universe-argument
example. It does not cover arbitrary eta inside arguments, structure eta,
other unrecoverable prefixes or arbitrary paired body substitution.
FullReduction coverage and strengthening remain open.


## 2026-10-21 21:18 UTC — Remove motive-prefix eta by descending earlier argument paths

Verdict: proved for the positive-universe Prop-carrier Eq motive prefix,
including the actual type probe and arbitrary insertion of binders. The earlier
proposition index may compute, so scoped normality of the entire eta function
is unavailable. Instead, the typed proper-prefix arity exclusion applies after
argument computation and preserves an exact path for every argument.

A motive need not have a minor inhabitant below. Introduce a fresh minor
variable, complete a typed retained five-argument prefix upstairs, decompose
the computation there, and descend the proposition and motive certificates.
This requires only forward typing weakening and proved exact certificate
descent. It neither invents an inhabitant below nor invokes inverse typing
weakening. In the fresh motive context, the motive argument is a fixed bvar;
only the earlier index path needs descending across that binder. The short
application can then reproduce the exact beta contractum for any raw motive
image, with every pending argument and the entire continuation retained.

The actual Eq probe has precisely its original index-comparison criterion
after this eta detour. Its lower-context version needs the equality major only
upstairs. Added the explicit motive case to JointSpineEtaCompute; finite
interleavings preserve the existing universe-exposure theorem. This removes
another local recovery requirement but supplies no FullReduction coverage,
strictly smaller sufficient front, or proof of weakN_iff.

Next unrefuted extension: eta before the minor should permit decomposition
using the fresh minor itself, followed by descent of the earlier proposition
and motive paths. Eta before the final proposition index is different: its
body has five arguments and may enable a singleton guard. Excluding or
descending that guard needs an argument about comparison against the fresh
index, not merely proper-prefix arity. Eta inside arguments and general
paired substitution still remain beyond these spine results.


## 2026-10-21 21:24 UTC — Exclude the five-argument guard by fresh-index separation

Verdict: proved eta removal before the final proposition index of the actual
Eq type probe, including exact lower comparison certificates and finite
interleavings. Proper-prefix arity alone stops at five supplied arguments.
However, every singleton head occurrence after arbitrary argument computation
retains a comparison certificate of the original proposition indices. Thus a
retained five-argument prefix with noncomparable original indices computes
only its arguments. This is proved for the full joint union, not only core
reduction or a selected singleton rule.

In the final-index eta body, the first proposition is lifted from below and
the final index is the fresh proposition variable. Existing typed fresh-variable
readout excludes their comparison by exact computation descent and the range
of lifting. Applying the separated-prefix theorem retains all earlier argument
paths. The fresh index and literal minor universe stay fixed; the proposition
and motive paths descend across the binder. The short application therefore
reproduces the exact first-beta contractum for any raw consumed index and any
pending arguments. No recovery of the index or motive is assumed.

The actual probe theorem preserves its original index-comparison criterion,
and the inserted-context version requires the equality major only upstairs.
JointSpineEtaCompute now includes this endpoint eta rule; its universe criterion
survives the extension. This covers the formerly exceptional five-argument
eta body but does not cover arbitrary eta inside arguments or full semantic
reduction. No strictly smaller sufficient irreducible front is established.

The minor-premise case remains live. Although the concrete minor is a literal
universe, its canonical assigned domain is a motive application that computes
to a universe, not a literal universe annotation. The existing literal-domain
eta lemma therefore does not directly cover it. A fresh minor variable should
instead allow proper-prefix decomposition and descent of the earlier arguments.
After that, all individual direct prefixes of the probe must still be connected
to arbitrary contextual eta and structure eta; finite spine coverage alone is
not the goal's missing semantic coverage theorem.


## 2026-10-21 21:28 UTC — Minor eta at the actual motive-application domain

Verdict: proved for arbitrary positive-universe Prop-carrier Eq motives,
with a typed retained three-argument prefix and its canonical minor domain.
The fresh minor variable completes a typed retained five-argument prefix in
the original minor context. Proper-prefix decomposition at four arguments
keeps all earlier computations. The fresh minor is fixed; the proposition
and motive paths descend with exact certificates. First-head beta then
replays the computed contractum for any raw consumed image and any pending
arguments. Neither recovery of the minor nor conversion of its annotation
to a literal universe is required.

Instantiated the result at the actual type probe, proving its canonical
three-argument prefix typing directly from the recursor telescope. The exact
original index-comparison criterion persists, including arbitrary insertion
of binders with an equality major only upstairs. Added eqMinorEta to the
finite interleaving relation, whose continuation and universe-exposure
criterion remain proved.

This closes the last individual direct-prefix eta position of the six-argument
probe: carrier, first proposition, motive, minor, final proposition, proof.
It does not prove arbitrary contextual eta coverage, or closure of the finite
relation under application arguments or binder bodies. The local theorems
use ordinary computation paths for supplied arguments. Replacing those paths
by arbitrary contextual eta/computation paths still requires a new argument;
it is not licensed by the spine continuation theorem. Structure eta and the
general paired-substitution/native-domain alignment problem remain open.
No smaller sufficient irreducible front has been established.

Next live question: can exact argument-path decomposition and primitive guard
readout survive eta/computation interleavings inside a supplied argument, so
that the finite spine relation has a typed contextual extension? This must
preserve original guards and outputs, not merely give semantic equality or
postulate a recovery condition already equivalent to PropositionFront.


## 2026-10-21 21:37 UTC — Bypass contextual eta transport for the entire motive slot

Verdict: proved a stronger replacement theorem for the motive argument.
An initial attempt to extend the finite spine relation through arbitrary
argument contexts has no ready transport lemma: the existing image-substitution
result transports ordinary computation, and full guarded-joint confluence is
still conditional. A comparison of two argument endpoints alone also does
not supply preservation of a subsequent universe-exposing continuation.
Those observations change the approach but do not refute contextual coverage.

For a retained typed Prop-carrier Eq recursor with literal universe minor,
first-head readout supplies an exact comparison of its original proposition
indices independently of its motive. Conversely that comparison enables the
prefix primitive and beta, returning the exact literal minor. This proves
universe exposure iff the original index certificate for an arbitrary motive,
not just the constant probe motive. Any two typed retained motives therefore
have identical exposure of this specified universe, with no equality between
the motives required. The recursor universes and proof majors may differ too.

Positive-universe canonical motive typing implies retention; the theorem has
a version with those explicit typings instead of an abstract retention premise.
An arbitrary semantic conversion of the original probe motive supplies both
the changed motive typing and the minor-domain conversion, so eta anywhere
inside that motive is covered without erased recovery or a semantic exposure
assumption. An inserted-context version permits the motive to exist only
upstairs, still retaining the original lower-index comparison certificate.

Added finite interleavings of these replacements, the certified spine eta
rules and full joint computations at a specified minor universe. The new
relation is an observation-preserving fragment, not an assertion that arbitrary
motive replacements are semantic reductions or that all universe observations
are interchangeable. Its lower Eq-probe criterion is unchanged.

This closes the entire motive-argument replacement case. It does not close
changes inside either proposition index: those are precisely the values read
by the guard. Arbitrary contextual eta and structure eta on the indices still
need preservation of original comparison certificates. General paired
substitution and the original strengthening theorem remain open. No strictly
smaller sufficient irreducible front has been established.


## 2026-10-21 21:42 UTC — Index transport has two distinct directions

Verdict: backward observation transport along directed index computation is
proved; the stronger forward beta law is exactly the existing missing
JointPropBetaStability obligation. A comparison of the computed indices lifts
back to the originals by JointCheck.compute. Combined with the arbitrary-motive
criterion, this allows both indices to compute while motives, recursor universe
arguments and proof majors change independently, provided both complete sources
are typed and retained. Added that step to the fixed-universe finite path
fragment. Its continuation theorem and lower-index criterion remain valid.

This does not license the converse implication. Defined EqProbeRightIndexBeta
as the missing forward law for beta contraction of just the right index, using
only the fixed literal minor Prop and the original constant motive. Proved it
equivalent to JointPropBetaStability of the full union. In the hard direction,
realize an arbitrary raw beta output as a typed proposition and construct both
proof majors from reflection of the input comparison; the exposure law then
returns the beta-contracted comparison certificate. No extra inhabitation or
lower equality major premise is hiding in the equivalence.

The equivalence is a checked boundary, not a proof of either law and not a
new smaller sufficient front. Forward stability is stronger than the pullback
needed for the new finite path rule. This finding does not refute a direct
contextual-eta argument; it rules out silently treating index replacement as
the already-settled motive replacement, or assuming forward exposure stability
as routine bookkeeping. Raw untyped comparison transitivity is already refuted
by the earlier empty-structure boundary, so it cannot fill the gap either.

Next live task: preserve an eta change inside an index through the actual
comparison/continuation derivation, or attack the existing proposition-only
beta transport induction. Stage-zero oracle and carrier-type beta transport
is already proved, but its statements keep compared endpoints fixed; it does
not discharge endpoint beta stability. The paired lambda/body substitution
case with unrecovered arguments remains the relevant unresolved case.


## 2026-10-21 21:59 UTC — Sort-image recovery failures have finite head exposure

Idea: replace full Pi recovery, when substituting arbitrary propositions, by
computation exposing a lambda domain. Verdict: the local rule and the
lowest-stage recovery-or-lambda classification are now proved; application
guard coverage and proposition beta stability remain open.

ProofErasureComputedLambdaApplication.lean compares the original function
endpoints and reads the left argument domain from a computation to a lambda.
Exact binder descent reconstructs that lambda below and retains all three
certificates. No forward comparison transport is used. This extends the
previous syntactically displayed-lambda rule without recovering its codomain.

SortRootedHeadExposure.lean supplies a finite path measure: follow lambda
bodies, function positions and projection receivers until reaching any
sort-typed leaf. Typed substitution preserves the measure. A typed expression
in this fragment either is sort-typed or beta-exposes a lambda whose body has
smaller rank. The leaf and arguments need not normalize. Projection is ruled
out by rigid-head separation. This is a checked finite head-reduction argument
for this fragment, not normalization of arbitrary functions or propositions.

ProofErasureSortImageRecovery.lean classifies every native recovery under
substitution whose retained images either recover exactly or are types. The
result has exact substituted recovery or belongs to the sort-rooted fragment.
For functions the latter branch exposes a lambda. At stage zero, substituting
any type, including an arbitrary proposition, meets these conditions without
any image recovery premise: core primitive transport is supplied explicitly.

The classification does NOT retain the selected domain on its lambda branch.
That branch currently supplies an annotation only semantically aligned with
the old recovered domain; a carrier guard at the latter cannot yet be used at
the former. Next live task: refine the recovery induction to retain annotation
computation from the exposed lambda domain to the selected substituted domain,
or find a concrete obstruction to that refinement. The conversion and
application cases must retain their original recovery evidence. Even after
that refinement, recursive comparison transport and higher joint stages need
proof. No full beta stability, counterexample, strictly smaller sufficient
obligation, or completion of GOAL.md is claimed.


## 2026-10-21 22:15 UTC — Selected domains survive sort-image recovery failure

Idea from the previous entry: retain annotation computation through the
recovery classification instead of appealing to semantic carrier conversion.
Verdict: proved at stage zero, including arbitrary proposition substitution.
The exposed-domain alignment gap from that entry is closed at this stage.

SortRootedRecovery retains the selected raw type and its ordinary-core
conversion paths. Typed substitution preserves its rank and exact output.
Head exposure retains a computation from the exposed lambda's Pi to that
output. In the application case, the smaller body path is instantiated and
receives one conversion node; its rank is still smaller than the source
application's. Pi decomposition gives computation of the annotation to the
selected domain, which can be performed on the lambda itself. No semantic
carrier-conversion premise or normalization of type leaves is used.

The substitution classification needs an exact-sort image alternative:
retained images recover their assigned type, or that assigned raw type is a
literal sort with actual image typing at the same universe. Mere semantic
equality of an assigned type with a sort is not silently substituted for this
condition. Single substitution of any type satisfies the condition, and it
extends through all typed binders. All recovery constructors are covered.

The final application corollary uses the original substituted-domain guard
unchanged. It returns an ordinary joint application comparison or a local
ComputedLambdaApplication certificate at identical endpoints. Target function
comparison and argument guard remain premises; the theorem does not establish
their recursive transport. Next live task: absorb the computed-domain branch
into existing comparison, or make it a recursive checking rule with proved
descent and transport. Higher joint-stage primitive transport also remains
open. This is not a proof of JointPropBetaStability or a new strictly smaller
sufficient obligation for PropositionFront.


## 2026-10-21 22:23 UTC — Recursive computed-domain checker closes type-image transport

Idea: make the computed-domain application rule recursive, rather than leave
its target comparison and carrier premises as external assumptions. Verdict:
proved for the full enlarged grammar at stage zero under exact-sort or native
recovering images; arbitrary type/proposition single substitution is covered.
No embedding of the enlarged checker back into the old one is asserted.

ComputedJointCheck retains every old joint checking constructor and adds
appComputed. Both its function comparison and carrier guard recurse in the
same family, with no bound on nesting or alternation. Old joint certificates
and the earlier local ComputedLambdaApplication embed. A full semantic binder
descent proof reconstructs the exposed lambda below inserted binders and then
uses the recursive function and carrier induction hypotheses. This is semantic
descent, not yet exact lower-certificate descent for the enlarged family.

The shared transport induction now permits exact native Pi recovery OR lambda
computation at the exact substituted domain. The appComputed case transports
its function computation and both recursive premises directly. At stage zero,
the previous selected-domain theorem discharges the native application's
alternative. Exact-sort image conditions extend through arbitrary binders and
are invariant across equal-erasure source realizations. Consequently both
comparison modes at common typed endpoints and explicit-carrier checking
transport in the same enlarged grammar. Single substitution of any type, and
paired beta-redex comparison from a supplied body certificate at a type
argument, require no recovery of that argument.

Remaining scope: this does not prove arbitrary endpoint beta stability,
substitution by arbitrary non-proof function/structure values, higher-stage
primitive substitution, or completeness of this checker. In particular the
original matched-beta obstruction can involve lambda-valued arguments; they
are not silently included among type images. Next live task: extend the image
criterion to the needed lambda/function arguments or isolate a concrete
obstruction there, while retaining sound binder descent. GOAL.md's proof,
canonical-Eq counterexample, and strictly smaller sufficient obligation
alternatives remain unachieved.

| Finite selected recovery paths for function substitution | **Checked (2026-11-04).** `ProofErasurePathImageSubstitution` replaces literal-sort exceptional images by `SortRootedRecovery` paths at the exact assigned output; `ProofErasureComputedJointPathSubstitution` transports the recursive checker. Type-valued lambdas are covered at their displayed Pi type, including body-certificate paired beta comparisons. Arbitrary assigned types are not covered: the separately appearing, independently checked `SelectedDomainEtaBoundary.typed_lambda_domain_failure` refutes exact-domain coverage after eta conversion. General carrier alignment, higher stages, and completeness remain open. |


## 2026-11-04 11:13 UTC — Exact selected lambda domains fail under eta conversion

Checked `SelectedDomainEtaBoundary.typed_lambda_domain_failure` in
`ProofErasureSelectedDomainEtaBoundary.lean`. In the existing eta context,
let A = F f and B = F (fun x => f x). The non-proof lambda `fun (_ : A) => Prop`
has assigned type `B → Sort 1`, and a rank-one sort-rooted path at its native
`A → Sort 1`. Nevertheless it has neither native recovery nor a sort-rooted
path at the assigned erased Pi. No computation in the entire joint union can
expose this lambda at erased domain B: the lambda and both domains are fixed
normal forms. **Verdict:** exact selected-path coverage for arbitrary typed
lambda images is false, even with a type-valued constant body. This does not
refute the conditional Path substitution statements or strengthening. A live
next route must account for comparison of written and assigned domains, with
binder descent proved rather than assumed; extending path length alone cannot
repair this example. The prospective compared-domain rule must also explain
how its intermediate carrier is realized below removed binders.

| Bypass selected-domain recovery at carriers with no structural exposure | **Checked (2026-11-04).** `ComputedJointCarrierGuard.checked_or_exposed` factors guards of the enlarged recursive checker into ordinary comparison or a computation to a record/Pi. Variable-headed carriers yield ordinary comparison and hence application certificates without function recovery or exact lambda exposure. `ComputedJointCheck.transport_or_inert` integrates this third alternative into the complete recursive transport induction. The eta-assigned boundary's neutral domain meets the local readout criterion; arbitrary whole-body substitution is not thereby proved. Remaining recovery failures with exposed structural carriers and higher stages remain open. |


## 2026-11-04 11:26 UTC — Computed-domain checking survives recursive primitive guards

The arbitrary compared-domain shortcut is not a new smaller obligation:
`JointVariableComparedRecovery.implies_propositionFront` and the existing
reannotation barrier already explain its cost. Recovery-guided eta expansion
also has prior exact-substitution obstructions; it was not reimplemented here.
Instead, completed the missing exact certificate descent for the existing
ComputedJointCheck grammar, then integrated that grammar into general singleton
family guards and specialized Eq-recursion carrier guards at every finite
stage. **Verdict: checked.** Computed lambda domains are reconstructed below
inserted binders, while recursive function comparisons and argument-carrier
certificates descend in the enlarged grammar. All old joint stages embed at
the same bounds. The union is closed under its own guards because every full
comparison/carrier certificate admits a finite stage bound. Exact certificate
descent, semantic descent, primitive-head control, and actual registered-prefix
replay hold throughout. This removes a real restriction of the previous local
and stage-zero results; it does not supply arbitrary image recovery, general
domain conversion, beta stability, or completeness. The next substantive gap
is substitution/repair of these recursive primitive guards while retaining
conversion information, not another assumed assigned-type coverage law.

| Protect neutral domain heads through local beta exposure | **Checked foundation (2026-11-04).** `AnchoredCarrier cut A` places the head variable outside the first `cut` binders; arbitrary local instantiation and protected-head substitutions preserve it. `AnchoredFamilyRecovery` extends selected sort-rooted paths with type families at neutral assigned domains. Its rank-preserving substitution and finite head-exposure theorem yield exact lambda-domain computation OR a protected neutral selected domain. `of_family` accepts converted family typings at their assigned Pi; exact annotation computation is not required. Classification of all substituted native recoveries into this larger invariant, and its full recursive checker specialization, remain open. |

| Recursive substitution by type families at neutral assigned domains | **Checked (2026-11-04).** `proofErase_joint_zero_recovery_subst_anchoredImages` covers every native recovery constructor with native recovery or a protected-family path, including projection exclusion. `transport_anchoredImages` transports the full recursive checker. The concrete eta-converted lambda now transports every common-typed body comparison despite its exact native/sort-rooted recovery and annotation-exposure failures. Arbitrary function/structure images, higher stages for this image class, and endpoint beta stability remain open. |

| Universal native/computed/inert image coverage | **Refuted (2026-11-04).** `StructuralDomainBoundary.typed_structural_domain_failure` wraps the eta-converted neutral domains in Pi. The typed type-valued lambda has no exact native recovery in the full joint union and no computation exposing its assigned lambda domain; that domain is already a Pi, so it is not inert. No `AnchoredFamilyRecovery` at the assigned type exists at any cutoff/rank. This refutes universal coverage by the current three alternatives, not strengthening. |
| Stop a selected recovery path at neutral output types | **Open.** A neutral selected output cannot feed recovery's function or structure-projection branches. A terminal-neutral path constructor could therefore admit arbitrary neutral-typed images and context conversion between neutral binder types. Projection exclusion must use the selected output's rigid shape: its present statement for arbitrary outputs would become false. This does not by itself handle arbitrary structural assigned domains. |


## 2026-11-04 11:40 UTC — Substitute recursive primitive guards using proved image transport

**Checked:** first-layer computations of ErasedComputedJointStage now preserve
exact outputs under both selected-path images and protected neutral-family
images. ComputedZeroGuardSubstitution packages interpretation, binder extension
and transport of both complete stage-zero checking views; both image criteria
supply those fields by existing proofs. General singleton guards transport
under their generated dependent telescope. Eq guards transport directly at
their actual carrier, without a registry-agreement or Eq-to-general encoding
hypothesis. A typed compatible-computation induction realizes each sequential
intermediate in the source relation and extends the constraint only at binders.
The concrete eta-assigned lambda from SelectedDomainEtaBoundary therefore
instantiates every typed first-layer computation, even though it has no exact
assigned-domain recovery/exposure. Verdict: the previous negative example is
now positively covered at a recursive computation layer; this does not restore
the refuted recovery criterion. Higher-stage recovery remains a separate gap:
a selected output conversion under a lambda may need instantiation by an
intermediate argument not covered by the available image invariant. No such
unrestricted instantiation, arbitrary endpoint beta stability or completeness
is assumed by the new theorems.

| Terminal neutral selected outputs and neutral binder conversion | **Checked (2026-11-04).** `AnchoredFamilyRecovery.neutral` stops at protected neutral selected outputs without requiring native image recovery. The full recovery/transport induction remains checked after projection exclusion is tightened to the selected output's rigid shape. Arbitrary values at neutral assigned types now substitute through recursive checking. `AnchoredImageSubstitution.neutral_context` transports comparison/carrier guards under actual equal-domain conversion from a neutral source binder; a retained finite function-body guard can change its domain accordingly. Extraction/transport of arbitrary whole-function guards and structural image coverage remain open. |

| Whole finite function-carrier conversion over neutral domains | **Checked (2026-11-04).** `proofErase_computed_joint_neutral_function_carrier_convert` transports an entire finite guard at a Pi returning a sort along actual equality of its neutral source domain. No normality or retained-body premise is needed: source carrier computation retains/replays Pi-domain reduction, and endpoint computation retains actual typing. `proofErase_structural_eta_application_repair` handles the exact Pi-wrapped recovery boundary by moving the argument guard to the written carrier. This is a checked application repair, not arbitrary body substitution or general structural carrier conversion. |

| Dependent whole function-carrier conversion | **Checked (2026-11-04).** The fixed-sort restriction is removed. `proofErase_computed_joint_dependent_neutral_function_carrier_convert` transports whole finite guards at `Pi A C` along actual equality from neutral `A`, for arbitrary dependent `C`. Carrier computation reconstructs the whole computed Pi, inverts its actual equality, and retains/replays the raw codomain path under the new binder. Proof-valued endpoints and function subsingletons are handled rather than excluded. The old fixed-sort theorem is a specialization. The application corollary needs no target argument guard. Arbitrary domain conversion, structural image coverage, and higher stages remain open. |


## 2026-11-04 12:08 UTC — Consume converted guards in structural-family substitution

Verdict: proved for a new finite structural-family image class. Refactoring the
recursive transport induction to pass already transported function/argument
guards and actual source argument typings avoids demanding exact selected-domain
exposure. StructuralFamilyRecovery retains a beta-exposed sort-valued function
whose assigned domain is Pi A (Sort v), with A protected neutral, and whose
written lambda domain is Pi B (Sort v). The family becomes a type after an
application, so its exposure induction terminates using the existing rank.
Carrier conversion consumes the recursive argument guard, including its
computation prefixes; no future-body oracle is introduced.

The complete stage-zero comparison/carrier transport and first-layer computation
transport now admit these images. The actual Pi-wrapped eta-domain obstruction
instantiates arbitrary typed body comparisons and first-layer computations.
Thus the former three-way coverage failure is repaired for this image class,
not merely for one isolated application. The old negative recovery theorem is
unchanged and still builds. This does not establish arbitrary image coverage,
higher-stage recovery transport, endpoint beta stability, completeness, or
strengthening. Next: extend the structural leaf to dependent inner codomains
and investigate the still-unjustified substitution of arbitrary intermediate
arguments into higher-stage converted body paths.

| Convert recursive neutral binders before anchored instantiation | **Checked (2026-11-04).** `ComputedJointCheck.recursive_neutral` extends the older simultaneous comparison/carrier conversion proof to every computed checking constructor. Actual recovery supplies the changed application domain; the smaller argument guard converts with it. Computed-lambda applications retain their written domains and realized argument typings. `proofErase_computed_joint_zero_compare_inst_converted_anchored` first converts the binder to a recursively neutral-related equal type, then instantiates using an anchored path there. `proofErase_computed_joint_structural_eta_lambda_inst` covers every common-typed stage-zero body for the exact Pi-wrapped eta boundary, although no anchored path exists at its assigned type. This improves the previous root-only repair to recursive body substitution. Arbitrary images and unrestricted endpoint beta stability are not established. |


## 2026-11-04 12:21 UTC — Dependent structural domains and neutral result values

Verdict: checked extensions of the complete structural-image substitution
induction. The structural leaf now admits Pi A C with arbitrary dependent C,
retained as syntax in the written Pi B C annotation. Actual equality of A and B
converts the binder context and proves codomain erasure unchanged. No inner
codomain normality, neutral-head condition or sort shape is needed. The older
literal-sort interface is a specialization. Parametric eta-domain consumers
exercise both arbitrary body comparison and first-layer computation.

A second leaf admits arbitrary functions at Pi A C when A and C have protected
neutral heads (C's head lies outside the function binder). No native recovery
or beta-exposed lambda is required. Under application, the recorded codomain
computation preserves that head and substituting the argument cannot replace
it, so exposure terminates at the existing neutral-output case. The image may
return a retained value instead of a type. A concrete eta-converted input
example returning the original context value now supports full recursive
body instantiation and first-layer computation.

These remove two separate restrictions of the previous class, not the entire
image-coverage gap. Structural leaves still have sort-valued outer results;
the new neutral-result leaf has a neutral input. Arbitrary structural results,
arbitrary domain conversions and higher-stage recovery remain open. Next:
combine converted structural input with protected neutral result, or generalize
finite path classification to recursively convertible selected types while
retaining justified substitution of converted body computations.

| Prove neutral context conversion stage by stage without arbitrary substitution | **Checked (2026-11-04).** `NeutralTypeChange.compute_of_context` follows actual computations, reconstructing both sides at transitive intermediates. It replaces unrestricted primitive substitution with typed recursive-neutral context transport. Recovery and the simultaneous computed comparison/carrier induction use this weaker interface. `erased_computed_joint_stage_neutral_context` discharges it at every finite stage: singleton-family guards move under their generated telescope and Eq carrier guards use the preceding-stage theorem. The closed union is covered too. Converted anchored images consequently instantiate first-layer computations, including the exact structural eta witness. This resolves higher-stage context conversion for this relation, not arbitrary-image substitution or completeness. |

| Additive-stage exact-image substitution for computed checking | **Checked (2026-11-04).** Extended the earlier JointCheck exact-renaming and recovering-substitution proofs to ComputedJointCheck, including appComputed. Images recovered at stage r transport every source computation, selected recovery, comparison and carrier guard at stage n to stage r+n; union primitive transport follows. Generated singleton telescopes and specialized Eq carrier guards use the preceding source stage. Native image recovery remains an explicit premise, not completeness. |

| Higher-stage substitution through a convertible recovered type | **Checked (2026-11-04).** `proofErase_computed_joint_*_inst_converted_recoverable` first transports the whole body across actual recursive neutral binder conversion, then substitutes using exact recovery at the new type. Computation, comparison and carrier guards have the additive stage bound; all three closed-union corollaries are proved. The exact structural eta lambda recovers at its written type at stage zero and consequently instantiates every finite-stage body comparison/computation at the same stage. Its assigned-type recovery/exposure failure is separately proved for the enlarged computed union. Universal image coverage, heterogeneous substitution and strengthening remain open. |


## 2026-11-04 12:35 UTC — Retain finite bodies across selected lambda-domain changes

Verdict: proved. Rather than adding another terminal image leaf for each
combination of structural input and output, SelectedLambdaDomain separates
the domain's finite guard-transfer evidence from the body's finite recovery
path. Exact domains, protected neutral carriers, and dependent function
domains with equal protected-neutral inputs have proved transfer laws. The
neutral case uses ordinary comparison extracted from its inert carrier; the
dependent case uses whole carrier conversion with actual endpoint typings.
The relation survives protected-head substitution.

StructuralFamilyRecovery.lamDomain stores this domain evidence and an arbitrary
smaller body path. Application instantiates that path in the written context;
it need not assert exact recovery at the assigned domain. The exposure theorem
retains the separate selected domain and its original computation. Rebuilding
an application pulls its supplied guard back through that computation and
transfers it to the written domain. A beta constructor also retains finite
beta prefixes. Neither constructor assumes a future-body checking oracle.

This removes the outer sort/neutral-result restriction for covered finite
lambda bodies. A concrete structural eta-domain image returning another
function now instantiates arbitrary typed body comparisons and first-layer
computations. The result type is a Pi, and its body path has positive finite
rank. Actual typing supplies equality of assigned/written annotations when
assembling the exact assigned-type erasure.

No universal finite-body recovery or unrestricted domain transfer is proved.
Arbitrary structure-valued bodies and guarded higher-stage conversions remain
possible gaps, as do heterogeneous substitution and endpoint beta stability.
Next: extend the domain evidence compositionally or add structural-result
paths with justified projection readout, rather than assume every value has
a path at its assigned type. Strengthening and strict-smallness remain open.


## 2026-11-04 — Carry converted recovery forward through lambda computation

Tested extending selected sort-rooted recovery paths to higher computed stages.
The existing exposure proof substitutes an arbitrary actual application argument
into a retained type-conversion path. Core paths support that operation, but
higher-stage paths require the very missing image coverage. The new exact
recovering substitution theorem does not discharge that premise. Verdict:
this direct extension remains open; no impossibility claim or assumed closure.

A different induction avoids backward transport of lambda body paths.
NeutralRecoveringImage records actual image typing at some recovered type,
recursive NeutralTypeChange from the selected raw annotation, and exact native
recovery at that recovered type (vacuous for proof images). When the image is
also typed at the selected annotation, uniqueness supplies actual type equality.
Forward annotation computation simulates on the recovered type; the image's
recovery extends along the simulated path. Verdict: forward closure, body
comparison instantiation and exact body-computation instantiation are proved
for the full computed union.

ProofErasureConvertedLambdaComputation follows each actual lambda computation
and contracts its body at the chosen image in the current binder context.
The transitive case realizes the intermediate lambda, advances the image
certificate, and continues there. No body path is pulled back through a changed
annotation. It returns the exact instantiated output and the image certificate
at the new annotation. Verdict: checked; next use is the full inferred-lambda
comparison induction, including its computation and symmetry cases.


## 2026-11-04 — Paired head beta with converted image recovery

ProofErasureComputedConvertedHeadBeta completes the inferred-lambda comparison
induction for the full computed union. Both displayed annotations carry a
NeutralRecoveringImage certificate. Structural lambda cases instantiate the
common-typed body comparison; computation cases contract both actual paths
with ConvertedLambdaComputation and continue with their new certificates;
symmetry swaps the certificates; typed eta supplies the ordinary beta path.
The recursive checker includes appComputed throughout. Verdict: proved,
without exact recovery at either displayed annotation or unrestricted beta
transport. Common-mode promotion for the computed grammar is also proved.

Proposition-valued paired head beta follows for equal-erasure arguments, and
for distinct arguments computing to a typed shared image with the two converted
recovery certificates. Compatible argument computation uses primitive renaming
only and requires no recovery on the original arguments. The structural eta
boundary's lambda satisfies the new image invariant via its written type, so
every inferred computed-union lambda comparison at its assigned structural
annotation now has paired head beta. Its known assigned recovery failure still
applies. Verdict: checked generalization of the recoverable joined-argument
branch, not arbitrary heterogeneous substitution or global beta stability.

Validation: 665-job isolated build, 14 exact opaque audit roots, largest closure
11,171, only standard axioms and no forbidden dependency or sorry. Arbitrary
carrier-related data arguments need not join, and image coverage remains
restricted. No proof of PropositionFront, canonical-Eq counterexample, or
strictly smaller sufficient irreducible front is established.


## 2026-11-04 12:57 UTC — Compose transport before replacing protected heads

Finite sequential substitution was tested as an alternative to closing the
structural-family image predicate under arbitrary substitution. Verdict: proved.
SequentialSubstitution stores individual certified maps and their finite
compositions. Context interpretation, binder extension, complete stage-zero
comparison and carrier checking, and first-layer computation transport all
compose. Intermediate actual typed endpoints are realized before applying the
next checking theorem. No final composite-image recovery certificate is assumed.

The concrete consumer first substitutes a structural-path image in a context
with an abstract type variable, then specializes that variable to any typed
type. For a type-valued family over that variable, ordinary typing supplies
the initial path; no beta exposure or native recovery premise is necessary.
Recursive comparisons and exact first-layer outputs survive both steps.
Replacing the variable by a sort provably violates global protected-head
preservation, so this is a valid way to discharge that restriction between
successive transport steps. It does not prove the final map lies outside every
existing image class, nor that every typed substitution factors this way.

Universal abstraction of an existing monomorphic body remains unproved: the
consumer requires its checking derivation in the abstract source context.
Changing a concrete domain to an unrelated variable does not itself provide
such a derivation. Verdict: finite-factorization is a live route, with this
source-certificate issue explicit; no universal coverage or strict-smallness
claim. Next investigate which existing comparison constructors can be lifted
to an abstract context, especially those using native projection readout.


## 2026-11-04 — Promote explicit carrier checking with two native type recoveries

Revisited the nonjoining-argument residue. The old common-mode beta invariant
is genuinely false: unit-valued identity applications compare, while their
distinct-variable reducts do not. The previous converted-recovery head-beta
result still needs equal erasures or a computational join. A stronger image
criterion alone cannot make those variables compare in the old grammar.

CarrierRecoveredCompare therefore adds a different, checked operation: recover
both endpoints at one literal raw carrier and use an explicit carrier guard
there, in either checking mode. Compatible application/projection/lambda/Pi,
computation and symmetry close this enlarged relation; all existing computed
comparisons embed. This revisits the earlier recovered-type promotion idea
with the full contextual explicit-carrier checker, whose unit case supplies
the missing nonjoining leaf. No old grammar or primitive is silently changed.

Verdict: full arbitrary-block semantic descent proved. Both native recoveries
reconstruct actual lower types. Injectivity of erasure lifting gives the same
lower erased type; existing erasure reflection aligns their actual types.
The original computed carrier certificate then descends at that lower carrier.
The compatible induction retains the usual inferred/common typing conditions.
No strengthening inverse, arbitrary substitution, or beta stability is used.
This changes the certificate language; it does not assert a missing closure
property of the old computed checker. Next test: arbitrary shared templates at
nonjoining unit images, including lambda-valued images.


## 2026-11-04 — Heterogeneous shared bodies at nonjoining unit and lambda images

CarrierRecoveredCongruence proves exact interpreted renaming of the enlarged
comparison. Pointwise inferred image comparison then extends through every
typed syntactic template. The left typed substitution builds each dependent
binder context; renaming lifts both compared images there. At variable leaves
the new recovered-carrier rule is usable in inferred mode, avoiding the old
failed promotion from an arbitrary carrier guard. Actual single instantiation
accepts distinct images and preserves exact erased endpoints. Shared native
recovery plus an old computed carrier guard is a sufficient image criterion.

Verdict: checked for arbitrary typed bodies, including dependent annotations,
not merely argument-free or first-order templates. CarrierRecoveredUnitImages
constructs two distinct variables at a closed positive empty structure, proves
they cannot compute to any shared shape in ErasedComputedJointUnion, and proves
they have no common comparison in the old computed grammar. Every typed body's
two instances nevertheless compare in the enlarged relation.

The images may themselves be lambdas: two constant functions with literal
universe domains return the two distinct unit variables. Their raw lambda
forms are normal and unequal, so they do not join. The new inferred image
comparison descends and still instantiates every typed body. This addresses a
nonjoining lambda-argument fragment without claiming a computational join or
native recovery of arbitrary images.

Limits: the source is one shared typed body. This is not heterogeneous transport
of an arbitrary existing comparison between different bodies. The new relation
has no proved global beta closure, composition, declarative completeness, or
feedback into singleton primitive guards. It is not a strictly smaller
sufficient front. The next substantive tasks are retaining its certificates
through descent and testing recursive guard saturation/transport; the original
strengthening obligation remains open. Validation: 655-job isolated build,
10 exact opaque audit roots, largest closure 10,998, no forbidden dependencies.


## 2026-11-04 13:13 UTC — Refute uniform abstraction; cover typed terminal images

Uniformly replacing a concrete type by a type variable while retaining the
body was tested in ProofErasureTypeAbstractionBoundary. At Type → Type the
body f Prop is typed and reflexively checked. In [x : S, S : Sort 2] the same
body has no type: substitute Type for S and Prop for x, and a putative typing
would make a sort a function, contradicting proved head separation. Both
contexts are well formed. Native Pi recovery also fails in the abstract
context for every primitive language with the established head restriction.
Verdict: this unrestricted abstraction step is false. It does not refute
sequential specialization, shape-preserving abstractions, or strengthening.

Instead, extend the finite-path image class by actual terminal typing.
TerminalImage covers types and values at rigid constant-headed types with no
registered projections. Such values cannot occupy either elimination position
inspected by native recovery: function application or projection major.
The new StructuralFamilyRecovery.terminal constructor needs no prescribed raw
output shape. Actual endpoint typing excludes any invalid subsequent
elimination. The property survives arbitrary typed substitution and backward
replay of an actual equality, so all finite path cases remain proved.
Verdict: complete recursive stage-zero comparison/carrier transport and exact
first-layer computation transport rebuild with this leaf. Ordinary data images
and terminal-valued lambda bodies need no native recovery or normalization.

ProofErasureExpandedSortInstantiation provides a concrete positive/negative
pair: Prop has an actual beta-expanded Type annotation; exact native recovery
of that annotation fails even in the full computed union, but arbitrary typed
body comparisons and first-layer computations instantiate at that binder.
Unlike a literal universe alias, its assigned raw type is an application,
not a sort. Terminal typing removes that syntactic restriction.

Next live refinement: a fieldless structure still has projection metadata and
is excluded by the current terminal criterion. Replace absence of metadata by
absence of valid projection readouts, using the actual projection typing or
its telescope/index bound. For structures with usable dependent fields, the
projection-result alignment problem remains. General function-domain
conversion, higher-stage finite-path transport, and checker completeness
remain open; no strict-smallness claim or GOAL.md completion alternative.

## 2026-11-04 — Saturate singleton guards with recovered-carrier comparison

**Verdict: checked finite-stage closure and exact certificate descent.** The
new comparison's recovered branch descends both native recovery certificates,
aligns their actual lower types through literal erasure reflection, and retains
the explicit computed carrier guard. No semantic recovery or target soundness
premise is added. General singleton family guards now use this comparison in
ErasedCarrierRecoveredStage; the specialized Eq branch keeps the old computed
carrier guard. The old stages embed at their original bounds. Finite bounds,
union closure, interpreted renaming, head preservation, and actual prefix
replay all hold. Eight lift iff theorems retain exact compute/recovery outputs,
comparison modes and supplied carriers at finite stages and their union.

The enlargement does not yet prove beta stability. In particular, recovered
carrier promotion requires the two native recoveries to reach one literal raw
type. Actual convertible types need not supply that certificate. A live test
is a pair of variables at distinct but convertible parameterized empty-structure
types: old application carrier checking can ignore this native-recovery
mismatch, while a beta reduct may expose it. This is a proposed boundary to
test, not a proved obstruction. Arbitrary distinct-body transport and recovery
coverage remain open.

## 2026-11-04 — Feed shared-template comparisons into canonical Eq computation

**Verdict: checked end-to-end guard feedback.** A common-mode recovered-carrier
comparison of a and b extends structurally to Eq α a a versus Eq α a b. Exact
renaming places it under the fresh proof major of the generated family guard.
Semantic reflection supplies the actual unfolding check, and the existing
singleton registry builds the exact primitive. At stage n the guard enables the
Eq prefix at n+1; the union is closed under this feedback. The whole-proof case
erases to identity. Shared-template image congruence therefore enables actual
Eq prefix computation for endpoints q[x] and q[y], without requiring x and y
to have a common reduct. This uses actual source typing and registry agreement;
it does not decode an arbitrary proposition guard into an old carrier guard.
Global beta stability and the original front remain open.

## 2026-11-04 — Converted native carriers refute unrestricted recovered beta closure

**Verdict: concrete typed obstruction checked, conditional only on a closed
positive empty structure.** CarrierRecoveredCompare.bvar_lookup_join proves
that distinct compared variables have computationally joining native lookup
types. Take p,q:S and F:S→Type at the same positive universe, where S is a
closed empty structure. Unit eta gives p=q, hence P=F p and Q=F q are convertible.
Let A=P→S and B=Q→S, and add x:A and y:B. Conversion types both at A. Their raw
native types cannot join: Pi computation retains a domain computation, and the
neutral domains F p and F q are distinct and fixed in every primitive relation
with constant/projection heads. This includes the entire recovered-carrier union.

The identity applications (λz:A.z) x and (λz:A.z) y nevertheless compare already
at stage zero through the subsingleton carrier A. Their beta reducts x and y
cannot compare in the full new union. The previous bare-unit witness was
repaired, but unrestricted common-mode beta stability is still false after
exact-recovery promotion and recursive singleton saturation. Canonical Eq does
not invalidate this conditional certificate-language obstruction; no claim is
made that canonical Eq alone supplies S. Proposition-only beta stability and
declarative strengthening are not refuted.

Live refinement: allow the two natively recovered types to be compared in
inferred mode instead of requiring a common computational type. The present
witness's native domains already admit carrier-aware application comparison.
Any such refinement must separately prove semantic and certificate descent
using the actual recovered types' sort typings; no completeness assumption may
be smuggled in. Alternatively pursue proposition-only stability without the
refuted unrestricted common-mode induction invariant.


## 2026-11-04 13:27 UTC — Structures with no retained projection fields

Fieldless structures were tested against the terminal-image substitution route.
The existing HasType.proj_index_lt theorem supplies the needed strict field-count
bound from an actual projection typing. Rigid owner injectivity plus projection
metadata uniqueness rules out any competing nonempty owner for the same value.
Verdict: proved and integrated, including indexed fieldless structures; no
constructor exposure or native recovery is needed for their images.

The same argument extends beyond fieldlessness. Existing closed ProofFields
certificates reconstruct an unindexed structure's typed projection expansion.
ProofFields.field extracts a single closed field certificate; its projection
is a proof. TerminalImage now includes arbitrary typed values at such proof-only
structures. Projection recovery excludes a retained projection using source
non-proofness transported by isProof_subst, rather than falsely excluding all
projection typing. Verdict: full recursive checking and first-layer computation
transport are proved for this larger class. Actual family-head equality aligns
the owner; metadata uniqueness aligns the projection information, and the proof
projection is constructed at the original image's universe instance.

The conjunction-shaped two-parameter/two-proof-field constructor telescope
supplies the certificate directly from declaration syntax. Its result universe
is unrestricted, so the major itself need not be a proof. Named consumers cover
both checking and exact first-layer computations for general proof-only images;
a concrete telescope consumer instantiates all common-typed recursive bodies.
This does not cover indexed proof-only structures with fields or retained data
fields, and it does not assume their projections vanish.

Next live direction: use terminal-domain binder conversion to enlarge lambda
input-domain alignment. To avoid a dependency cycle through SelectedLambdaDomain
and StructuralImageSubstitution, first investigate adding terminal leaves to the
older SortRootedRecovery/PathImageSubstitution layer, whose exposed lambda domains
are exact. That lower transport could supply conversion for terminal-valued
binders independently of selected-domain guard conversion. This is a plan, not
a proved carrier-conversion law. Retained projections may separately propagate
a typed terminal result (e.g. a sort-valued field) instead of being excluded;
that requires a new proved recovery alternative, not the present terminal rule.

## 2026-11-04 — Compare native recovered types instead of joining them

**Verdict: checked descending extension, including exact certificates.**
CarrierAlignedCompare retains the previous checker and adds two distinct rules.
Common mode needs only the left native recovery and a guard at that carrier:
the supplied common actual endpoint typings and uniqueness align the right
endpoint. Inferred mode retains both native recoveries and recursively compares
their selected types in inferred mode before using the left carrier guard.
During descent those recovered types have actual sort typings, so the recursive
comparison safely aligns them. No computational join or semantic recovery rule
is assumed. Interpreted renaming, primitive inclusion, exact certificate descent,
arbitrary shared-template image congruence, and generic lift iff are proved.

This targets the converted-native-type obstruction without claiming global
beta closure. The new relation is currently parameterized over existing
primitive relations; it has not been saturated into a new singleton stage
system. Arbitrary comparison substitution, recovery coverage and declarative
completeness remain open.

## 2026-11-04 — The converted-function peak is repaired in inferred mode

**Verdict: checked on the same actual typed witness, already at stage zero.**
CarrierAlignedConvertedUnit retains the previous negative result: after beta,
the two distinct variables cannot compare in the entire exact-recovery union.
Both variables nevertheless have native recoveries. Their function types
compare by Pi congruence; the neutral domain applications use the unit guard at
their arguments and native recovery of the family variable. The aligned rule
therefore compares the two beta reducts in inferred mode at stage zero. The
result extends through every shared typed body via interpreted renaming in the
existing recovered-carrier union. No common computational native type is
manufactured, and no old negative theorem is applied to the enlarged grammar.


### 2026-11-04 13:44 UTC — terminal-valued input domains and whole function guards

Verdict: proved terminal-domain context conversion and whole dependent function
carrier conversion at stage zero, then integrated them into selected lambda
domains and actual comparison/first-layer computation instantiation. The lower
anchored path layer, rather than SortRootedRecovery, accepts terminal leaves;
this avoids a dependency cycle without weakening the earlier sort-rooted API.
TerminalDomain means the actual generic variable is a TerminalImage. It is
stable under typed substitution and ordinary type equality; universes, rigid
data without projections, fieldless structures, and unindexed structures with
all proof fields supply it. Terminal projection exclusion uses actual typing
and proofness, not the false claim that terminal images cannot be structures.

The carrier proof consumes the entire finite guard. In its computation case,
ordinary type equality transports terminality to the reduced input while the
codomain computation is replayed under the target binder. In its function case,
the independent anchored substitution law transfers the eta-body check across
the converted context. No future body-comparison oracle or native recovery law
is assumed. SelectedLambdaDomain.dependentTerminal then supports arbitrary
finite structural lambda-body paths and their existing substitution consumers.

Checked witness: a lambda written with input (Sort 1 -> Prop) but assigned an
input (Sort (imax 1 1) -> Prop). The universe input is terminal and is not a
protected variable-headed carrier. The image preserves all common-typed
stage-zero comparisons and exact first-layer computation outputs. Exact native
recovery at its assigned type nevertheless fails in the full computed union:
the written normal annotation cannot compute to the syntactically different
assigned annotation. This is a recovery obstruction, not a strengthening
counterexample. Existing structural-domain recovery obstructions still compile.

Boundary: this converts whole Pi carriers with a terminal-valued inner input
and the same dependent codomain expression. It does not prove direct arbitrary
carrier conversion between terminal data types, arbitrary function-valued input
conversion, or arbitrary higher-stage substitution. The original theorem is
still open, and no strictly smaller sufficient irreducible obligation follows.
Live next direction: extend recovery through retained projections whose actual
field result is terminal, or establish a recursive domain-conversion invariant
for function-valued inputs. Neither may be replaced by a blanket transport
assumption. The previous converted-unit beta obstruction remains relevant to
any proposal requiring computational joins of native annotations.

## 2026-11-04 — Type endpoints retain sort and Pi exposure after alignment

**Verdict: checked typed head exposure, with no recovery completeness premise.**
ComputedCarrierTypeChecking turns a carrier guard between independently
sort-typed endpoints into ordinary computed comparison if either endpoint has
that actual carrier. Structure and function carrier cases contradict the
endpoint's sort typing; compatible carrier and endpoint computations replay
at actual originals. This prevents the new promotion rules from hiding a
sort or Pi head in typed comparison. CarrierAlignedTypedExposure proves
common-to-inferred mode conversion at type endpoints, sort/Pi exposure, and
Pi exposure from an existing native recovery whose selected output compares
with an actual assigned Pi. The recovered Pi may have a different literal
domain; no equality of erased domains or computational join is inferred.

Next live problem: transport the guards and body certificates through the
newly exposed domain and changed native outputs. Existing recovery plus a type
comparison is still an explicit input, not a consequence of arbitrary typing.
This head-exposure result does not supply full substitution, beta stability or
a strictly smaller sufficient front by itself.


### 2026-11-04 13:56 UTC — recursive substitution through retained terminal fields

Verdict: proved recursive checking and exact first-layer computation
instantiation for structures whose retained projections have terminal results.
This advances the retained-data-field gap without assuming forward conversion
of the dependent field carrier. TerminalFieldShape is a concrete declaration
shape: a universe, a rigid constant application with no projections, or a
fieldless registered structure. Its arguments may depend on parameters and
prior fields. It survives arbitrary term substitution and universe
specialization. StructureReplay.TerminalFields requires that shape for each
field in the registered finite constructor telescope.

The crucial proof uses a projection's own typing inversion, including its
actual universe instance, parameters, source major and admissibility guard.
It reconstructs the native field typing at that source and applies the static
field-head certificate. Owner injectivity aligns a separately certified major
with the actual projection owner. No projected constructor expansion is assumed,
no assigned type is resynthesized, and no forward computation of a dependent
field type is required. Indexed structures are allowed when the projection is
actually typed; there is no blanket projection-admissibility claim.

ProjectionTerminalImage includes the old terminal images and typed majors
with this telescope certificate. StructuralFamilyRecovery.projectable retains
this case at an arbitrary selected raw output. In native recovery transport,
a retained projection whose major loses exact recovery now returns a terminal
result certificate instead of deriving a contradiction. The full recursive
stage-zero comparison and first-layer computation consumers inherit the case.

Checked dependent telescope: a Type field followed by a value of a rigid data
family applied to that earlier type. Its declaration satisfies TerminalFields.
For a positive registered record with that telescope, an actual projection is
typed at Type and is not erased, hence its major cannot satisfy TerminalImage.
This proves the image extension is genuine relative to the previous class.
Concrete and generic body-comparison consumers use the new certificate.

Boundary: arbitrary function-valued fields and fields whose instantiated types
have unprotected variable heads remain outside this class. Global higher-stage
substitution and strengthening remain open; this is not a smaller sufficient
front. Live next direction: replace the one-projection terminal condition by
an inductive finite field certificate, allowing a projection to return another
certified record. Substitution preserves the rigid head while recursion proceeds
through the finite declaration certificate, rather than assuming normalization
or a future comparison law. This extension has not yet been implemented or
proved. Mixed proof/data fields and general function-valued fields need further
arguments; the existing all-proof-field case remains available separately.


### 2026-11-04 14:09 UTC — finite nested projection coverage and its parameter boundary

Verdict: finite recursive projection-field coverage is proved and connected to
full stage-zero comparison and exact first-layer computation instantiation.
ProjectionClosedType is an inductive tree with TerminalFieldShape leaves and
registered record nodes whose declared field domains carry child trees. The
record premise is declaration syntax, not a future comparison or transport law.
Substitution and universe specialization change occurrence arguments while
preserving the declared tree. ProjectionClosedImage combines actual typing at
such a tree with the earlier terminal-image cases, including proof-only images.

The projection theorem uses actual projection inversion and the constructor
field-type equation to instantiate the child tree at the native source's
parameters, universe levels and earlier projections. Its result belongs to
ProjectionClosedImage again. StructuralFamilyRecovery gains a projectionClosed
leaf; its exposure and recovery-substitution proof carry that closed class
through repeated projections. The former projection_terminal theorem is
replaced by projection_closed: immediate terminality would be false for the
enlarged class. Earlier terminal-field APIs embed through
ProjectionTerminalImage.closed and their consumers still compile.

Positive separation: a positive wrapper record around the preceding retained
type/data record has two actually typed retained projections. Its first result
is not terminal, so its major cannot satisfy ProjectionTerminalImage, but it
has a ProjectionClosedImage certificate. The wrapping constructor rule is
repeatable, and the full recursive comparison consumer handles nested records
without fixing a projection path in advance.

New checked boundary: a polymorphic box whose field type is its type parameter
has no declaration-only field tree even at the concrete occurrence Box Type.
The actual projection is typed at Type and retained. The major has no
ProjectionClosedImage certificate, including via another ordinarily convertible
type: terminal alternatives contradict the retained projection, and rigid-owner
injectivity forces any record alternative back to the same parameter-field
schema. This refutes universal image coverage by this certificate alone, not
strengthening or coverage by every other native/structural alternative.

Next live direction: occurrence-specific field certificates, initially for
positive unindexed structures. Specializing constructor parameters before
classifying the remaining field domains could cover Box Type. Actual field
typing must be reconstructed from the original major and projection guards;
positive result universes make those guards available, and existing structure
reconstruction may supply the needed telescope typing. Typed substitution must
transport the specialized field syntax and its certificate. No such law has
been assumed or proved here. General function-valued fields, mixed proof/data
fields and arbitrary higher-stage substitution remain separate gaps. No
strictly smaller sufficient strengthening obligation has been established.


## 2026-11-04 — Pi exposure retaining the inferred type residual

**Verdict: checked residual exposure; exact assigned-type recovery is unnecessary.**
ComputedTypeResidual and CarrierAlignedTypeResidual strengthen the earlier
head-exposure lemmas. Given an existing native recovery and an inferred or
common comparison with an actual assigned Pi, they expose a native Pi and
retain an inferred comparison with the original assigned Pi. A typed replay
returns actual original domain/codomain expressions, a typing of the function
at that Pi, and the exact native recovery together. This uses the computation
constructors already present; no transitivity or beta-stability premise is
added. In the computed-comparison case the reduced left endpoint is compared
with the original right endpoint by retaining its right computation.

A checked witness in CarrierAlignedNativePiExample declares a variable at an
identity-beta expansion of a Pi. The written and assigned domain universes are
equivalent but syntactically distinct. Native recovery exposes the written Pi
and retains its comparison, although exact recovery of the assigned Pi fails
in the full old carrier-recovered primitive union. This is a type-level identity
computation, not a canonical-Eq cast or a strengthening counterexample.

Next live obligation: transport an application argument guard from the assigned
domain to the exposed native domain and instantiate the changed codomains.
The new residual supplies the comparison that was previously discarded, but
neither native recovery nor that comparison follows here from arbitrary typing.
Paired substitutions also change binder annotations: a right image typed at the
right substituted domain cannot silently be treated as typed at the left one.
Recursive carrier guards still contain the old comparison language. General
transitivity is not justified by native recovery alone, which does not certify
all raw argument typings. Original strengthening and every GOAL.md completion
alternative remain open.


## 2026-11-04 — Paired beta with joining bodies and nonjoining images

**Verdict: checked paired beta beyond one shared body template.**
CarrierAlignedPairedBeta compares two beta contracta when their erased bodies
have a finite common beta reduct and their argument images compare in inferred
mode. The written lambda domains may differ; common actual function typing
aligns the argument typings. The proof replays the left body path to a typed
shared template, applies the proved image congruence there, and instantiates
both beta paths. It needs no native recovery at the written annotations,
argument computation join, arbitrary primitive substitution, or comparison
transitivity.

CarrierAlignedPairedBetaExample uses the converted-fieldless-structure witness.
The two common-typed variable images provably have no computational join in the
full carrier-recovered primitive union, and the old checker cannot compare them.
Nevertheless every finite body-beta join instantiates at those images in the
aligned checker. The positive fieldless-structure declaration is an explicit
hypothesis, not a consequence asserted from canonical Eq alone.

The explicit body join remains a restriction. Live extension: permit distinct
body reducts with recursively universe-equivalent annotations, then investigate
carrier and eta comparisons without replacing the entire missing substitution
law by a premise. This paired-beta fragment does not close PropFront.


### 2026-11-04 14:23 UTC — instantiated field trees repair polymorphic boxes

Verdict: the parameter-box boundary is repaired by an occurrence-specific,
inductive field tree. InstanceProjectionType.record stores exact native field
readouts at a fresh major variable with the occurrence parameters already
lifted and instantiated. Each valid field has a child tree of the same type.
The finite table and recursive children contain no comparison or transport law.
The new record case requires a positive result universe and zero indices; prior
ProjectionClosedType leaves preserve the earlier indexed/declaration-only cases.

Arbitrary term substitution transports the entire tree under the fresh major
binder using fieldType_subst_some. InstanceProjectionImage supplies actual
image typing, equality replay, non-functionality and closure under retained
projection. StructureReplay.positive_projection_native reconstructs the actual
constructor expansion from the original major and its positive projection
guard, then extracts the native field typing. Thus a competing projection may
use another convertible parameter instance or source major: owner injectivity
aligns its owner, and reconstruction uses the original certified instance.
No field typing or expanded-constructor typing is assumed.

StructuralFamilyRecovery.instanceProjection carries the enlarged image class
at the selected raw output. Its expose result and recursive projection recovery
return InstanceProjectionImage. The old generic projection_closed conclusion
would now be false for Box Type and is replaced by projection_image; all earlier
image classes and instantiation consumers remain available through embeddings.

The exact earlier Box Type witness now has InstanceProjectionImage while
retaining the proved negation of ProjectionClosedImage and its actual retained
projection. The parameterBox rule inherits any actual parameter tree, and its
iteration proves arbitrary finite nesting of the same polymorphic wrapper.
Actual nested image typings feed full stage-zero comparison and exact
first-layer computation instantiation. No normalization or native readout of
the image is required.

Remaining boundary: callable fields are still excluded by the non-function
image invariant; mixed proof/data field schemas and non-positive/indexed new
instance schemas are not supplied by this constructor. Global higher-stage
substitution and declarative strengthening remain open.

Next live direction: preserve actual selected-carrier typing through native
recovery replay before repairing an application. Replaying the source function
recovery yields a typed Pi whose erasure is the selected raw Pi; its domain can
then type both original arguments before substitution. This could support a
new callable-image case with universe-valued inputs and a certified result tree.
At such type-valued arguments, the existing committed theorem
proofErase_computed_carrier_types_checked converts a carrier guard to ordinary
comparison, provided the selected carrier has the required actual typing.
The current application helper does not retain that readout explicitly. Prove
and carry it rather than assuming arbitrary guard conversion. Then investigate
function-valued record fields using the same typed elimination tree. This is
an unproved next route, not a claimed generic application-transport law or a
strictly smaller sufficient front.


## 2026-11-04 — Paired beta through structural body variants

**Verdict: checked heterogeneous substitution and paired beta without a literal
body join.** StructuralVariant permits recursive universe conversion in sorts,
constant levels, applications, projections, lambda annotations and Pi types.
CarrierAlignedStructuralBodies transports this relation through two pointwise
inferred-related image maps. Only the left original/map supplies an actual typed
interpretation. Under a binder its substituted domain types the left context;
the right lifted raw map is not falsely required to recover or inhabit that
left domain. This yields paired head-beta comparison with different written
lambda domains and structural variants of the finite body reducts.

Checked strictness: CarrierAlignedStructuralBodyExample gives actual typed
bodies Pi (Sort (max 1 0)) #1 and Pi (Sort 1) #1 under [Sort 1], instantiated
at Sort 0 and Sort (max 0 0). The bodies have no common beta reduct; the argument
images have no computation join in the full carrier-recovered union. The Pi
codomains retain those respective images after instantiation. The new theorem
nevertheless supplies inferred comparison. Thus the preceding literal-body-join
premise genuinely cannot be used for this example.

Boundary: StructuralVariant contains no carrier or eta rules, and body paths
are beta paths. This does not substitute arbitrary recursive body comparisons
or guarded primitive computations. Existing native recovery plus an inferred
comparison with an assigned type remains an input, not coverage. For an
application, weakened recovery must expose a native Pi, move its argument guard
to that domain, and compare instantiated codomains. The latter cannot simply
invoke the desired substitution theorem on a newly produced residual whose
size is uncontrolled. Nor can arbitrary comparison-based carrier conversion be
added without addressing whether its intermediate carrier descends. These are
live proof obligations, not new axioms or a completed smaller sufficient front.


## 2026-11-04 14:39:52 UTC — Callable fields with type inputs

Verdict: checked extension of recursive substitution to finite typed trees of
universe-input calls and instantiated record projections. TypeInputTree embeds
the previous non-functional instance tree, adds functions from a universe with
a certified dependent result, and allows callable children in positive
unindexed record instances. Typed application substitutes the argument into
the result certificate; retained projection selects the instantiated child.
TypeInputImage preserves these trees under ordinary typed substitution and
backward equality replay.

The missing selected-carrier readout is now proved, not assumed by the public
substitution theorem. Source native recovery replays to an actual typed Pi;
uniqueness types both source arguments at its exact erased domain. Substitution
preserves that readout. Callable input typings then show both arguments are
types, allowing proofErase_computed_carrier_types_checked to discharge their
entire supplied guard, including computation and reduction cases. This repairs
application without requiring native recovery for the substituted function.

Two strictness witnesses: a positive polymorphic box may contain a function
from Type to Type, whose retained projection can be applied to Prop; the old
InstanceProjectionImage class cannot certify that box. A lambda written with
input Sort 1 may be assigned input Sort (max 1 0); exact assigned-type recovery
fails in the full computed union, but its tree instantiates recursive stage-zero
comparison and exact first-layer computation. The generic callable-box consumer
also instantiates full body comparisons.

Boundary: this is not arbitrary-domain application or higher-stage substitution.
Free type-variable result heads need additional certificates; mixed proof/data
field schemas and new indexed/non-positive record nodes remain unsupported.
GOAL.md's strengthening theorem and smaller-sufficient-front deliverable remain
open. The preceding goal work was progress; the pending audit now completed
successfully (291 explicit roots, maximum closure 11,317).

Next live direction: preserve carrier-mode guards for function-valued inputs
and compare their dependent results under the actual selected carrier. Do not
blindly promote arbitrary guards to plain comparison: the existing checked
carrier_recovered_nonjoining_unit_images witness has a unit carrier guard
between distinct retained variables but no original ComputedJointCompare.
The new type-input proof succeeds because its endpoints have sort typings;
removing that premise is refuted. A higher-order extension needs a proved
carrier conversion or typed lambda/body exposure, including dependent codomain
alignment, rather than assuming the desired substituted body comparison.


## 2026-11-04 — Recursive extensional checking over native alignment

**Verdict: checked closure with full binder descent, not raw eta replay.**
CarrierAlignedCompare now recursively admits sorted binders, common lambda
bodies, left/right eta bodies, inferred lambda eta and structure-field checks.
The new recover rule aligns two native outputs and then consumes a recursive
common comparison, so new eta-body certificates can participate in inferred
promotion. Each rule retains both semantic and exact certificate descent.
Renaming, typed head exposure and inferred type residuals remain proved.

CarrierAlignedSubstitution supplies two actual typed image maps and pointwise
inferred comparison. Its binder extension proves equality of the two substituted
domains by the existing typed image congruence, converts the right map into the
left binder, and retains both erasure agreements. The symmetric extension uses
the right binder for right eta. This resolves the previously identified paired
binder-context problem without claiming exact native recovery of right images.

Raw erased eta contraction remains unsuitable: the existing ErasedEta boundary
shows that it can hide an inhabitance dependency. The active next proof instead
transports complete primitive-free ScopedCompare certificates using these paired
maps, classifying eta arguments from actual common typings and keeping the typed
short original. Guarded primitive substitution and recursive carrier transport
remain separate, unproved obligations for the full strengthening problem.


## 2026-11-04 14:55:25 UTC — Arbitrary source carriers at dependent type-family targets

Verdict: checked target-structural recursion converts whole computed guards to
finite dependent function families ending in a universe. TerminalTypeFamily
records a TerminalDomain at each input binder and recursively certifies its
codomain in that actual extended context. It survives typed substitution.
The source carrier may have arbitrary syntax, arbitrary computed prefixes,
and a codomain different from the target's; only actual type equality and
source endpoint typings are required.

The function case replays source carrier/endpoint computation, exposes a typed
source Pi, uses Pi injectivity to align the input and result typings, and moves
the entire eta-body carrier guard into the target input context. The recursive
readout hypothesis comes from the strictly smaller target codomain certificate,
not the size of a newly generated comparison. The sort case consumes the guard
using proofErase_computed_carrier_types_checked. No future body comparison or
generic carrier transport is assumed. This extends the earlier conversion that
required a displayed source Pi and identical written codomain syntax.

SelectedLambdaDomain.typeFamily integrates the result into existing structural
image substitution. General and one-function wrappers preserve every recursive
stage-zero body comparison and exact first-layer computation. The checked image
lambda f : (Type → Prop) => f Prop retains and calls its higher-order input.
Its assigned input beta-expands a Pi with different but equivalent syntax in
both universe annotations. It has no exact assigned recovery in the full
computed union, yet the new consumers instantiate it. The source is not a
literal Pi and its beta reduct does not retain the target's result annotation.

Checked boundary: ∀ A : Type, A → Prop is well typed but has no
TerminalTypeFamily certificate. A hypothetical TerminalDomain for the generic
A could be specialized to Prop → Prop, contradicting TerminalImage.not_function
at the fresh function value. Thus increasing the finite telescope depth alone
cannot obtain arbitrary polymorphic predicates. This is a coverage obstruction,
not a counterexample to the goal or to all alternative image certificates.

Next live direction: permit generic type-parameter inputs while preserving the
actual selected-carrier guard. The prior neutral-source context converter cannot
be reversed merely because the target is neutral: ordinary equality permits a
non-neutral beta-expanded source. Prove binder transport into a neutral target,
or a typed exposure invariant supplying the source evidence it needs. Another
live route is a stratified input-image class extending terminal inputs to
callable certified images; its context-conversion proof must avoid circularly
using the very selected-domain theorem being defined. Global higher-stage
substitution, arbitrary dependent carriers and PropFront remain open.


### Full scoped comparison under paired aligned images (2026-11-04)

Verdict: proved, including all recursive eta, sorted-binder and structure-field
cases of ScopedCompare. This replaces the earlier restriction to shared beta
reducts or StructuralVariant bodies. CarrierAlignedSubstitution lifts both actual
maps into one converted target binder; the right eta-body case uses its symmetric
right-binder construction. Typed eta classification supplies the fresh argument,
and two lambda endpoints of a common-typed eta guard have beta-related bodies.
No raw eta contractum is replayed without a typed original.

The generic theorem explicitly requires typed source primitive simulation; its
primitive-free corollary discharges that interface. It assumes inferred-related
image maps, not arbitrary common-related maps. Full joint carrier checking,
higher guarded-stage substitution, and sufficient coverage for PropFront remain
open. This is progress on the live paired-substitution route, not a new sufficient
irreducible obligation or completion of GOAL.md.


### Core paired head beta with nonjoining images (2026-11-04)

Verdict: proved for the entire core ScopedCompare source grammar. Delta/iota
primitive simulation follows from raw core substitution. The inferred-lambda
head-beta proof handles finite source computations that change the written
annotations, using typed lambda-instantiation replay rather than assuming raw
primitive substitution along untyped intermediate terms. Every recursive eta
and structure-field body case is included. Converted positive fieldless-structure
variables still fail the old checker and have no computation join, but instantiate
all common-typed core scoped body checks; a concrete eta-expanded body returns
the substituted parameter beneath a lambda.

This removes the primitive-free restriction for the core source, while retaining
the explicit inferred image comparison. It does not prove higher guarded-stage
primitive simulation, paired transport of ComputedJointCheck carrier rules, or
coverage by the enlarged target checker. Those are the remaining live steps;
no canonical-Eq counterexample or strictly smaller sufficient obligation is claimed.


## 2026-11-04 15:13:22 UTC — Typed specialization detects inert generic values

Verdict: checked whole-guard promotion at values of a generic type parameter,
even when their actual source carrier is only ordinarily equal to that parameter
and is not syntactically neutral. SortSpecialization records an actual typed
interpretation of the whole context in which the image has a sort type. The
witness can retain arbitrarily many local binders above a successor-universe
type parameter. It is existential, not a semantic equality under all valuations.
No inhabitance assumption is introduced.

Such an image cannot currently be a proof, function or structure major:
substitution would preserve that typing, contradicting its actual sort typing.
Weakening extends the same interpretation and ordinary equality replays it.
Induction on the full ComputedJointCarrierGuard excludes its structural cases,
replays carrier computation, and preserves the witness across endpoint reduction.
Either endpoint suffices. The result is ordinary comparison in exactly the same
primitive relation, followed by carrier reindexing and an actual application
consumer. This works for any primitive relation with typed descent, including
the full computed union under canonical Eq and sound definitions.

Concrete evidence: the generic value rejected by TerminalDomain has a checked
specialization. Two fresh values of a generic Type parameter remain separated
at a beta-expanded parameter carrier, even by the full computed-union guard.
The carrier has an application head, so raw neutral-source classification does
not supply this result. Actual endpoint typings and beta equality are proved.

Rejected shortcut: treating SortSpecialization as an arbitrary-substitution-
stable terminal leaf is false. Substituting Prop → Prop for the type parameter
turns the same specializable generic value into a function. The explicit typed
substitution and the negation of target specialization are checked. Therefore
adding this case to the previous recovery tree's unrestricted subst theorem
would be unsound; no such change was made.

Next live route: index recovery paths by a shared actual test interpretation.
Under a lambda its test must be the lift of the parent's test, rather than a
new independent existential witness. inst_of_lifted_test already proves the
required local beta-substitution law using the actual interpreted argument.
Build a path exposure/instantiation proof retaining this coherent test and its
selected raw output, then use it for generic-parameter binder conversion. That
full context transport is still unproved. The terminal-family coverage boundary
for ∀ A : Type, A → Prop is not claimed repaired by guard promotion alone.
Global strengthening and a strictly smaller sufficient front remain open.


### Arbitrary finite structure-singleton computation in paired bodies (2026-11-04)

Verdict: proved. The primitive interface in the paired scoped theorem is not
limited to delta/iota. Existing structure-singleton stages already preserve
interpreted substitutions at their original bounds, including nested general
singleton family checks and explicit structure-carrier Eq prefixes. Their union
embeds stage-for-stage through the application, recursive-singleton, joint and
computed stages into the recovered-carrier union. This discharges the paired
primitive interface for arbitrary finite nesting without defining a new oracle
or assuming substitution of the larger recovered-carrier union.

The nonjoining-image witness now instantiates every common-typed scoped body
comparison over this guarded source union. A second explicit consumer constructs
actual common typings and an inferred scoped certificate for lambdas whose
annotation computes to Prop and whose body returns the parameter. A canonical-Eq
unit-prefix example supplies that annotation computation at structure stage one.
It establishes actual guarded coverage, not exclusion of all alternative core
computation paths.

Remaining boundary: recovered-application and mutually recursive carrier guards
are not members of this source union. Their selected Pi/domain must survive
substitution together with its argument guard. The existing fresh-variable test
for JointCarrierDomainResynthesis requires recovery of arbitrary non-proof
function images, so merely reusing its interface would reintroduce a substantive
missing theorem. Native Pi residuals retain comparisons when the assigned type
already has a certificate; they do not yet supply that certificate for all typed
images or transport the entire recursive carrier guard. This remains the next
live step. PropFront and the original strengthening goal remain open.


## 2026-11-04 15:29:02 UTC — Shared test interpretations repair generic binder conversion

Verdict: proved through the complete stage-zero computed checker. A recovery
path indexed by one actual typed interpretation lifts that same interpretation
under every lambda. A typed commuting substitution square transports the path;
local beta contraction constructs the square by substituting the interpreted
argument in the test context. Rank decreases through head exposure, retaining
the original selected raw output and exposing exactly its Pi domain.

The source-variable image invariant is native recovery or such a path. It
extends through arbitrary typed local binders and transports the whole recursive
stage-zero comparison/carrier checker. It therefore converts any source binder
to an ordinarily equal target whose generic value has a SortSpecialization.
There is no assumed target comparison, native recovery, semantic head exposure,
or unrestricted substitution closure of existential specialization.

SpecializedTypeFamily combines the previous terminal inputs with specializable
generic inputs. Its carrier readout consumes arbitrary equal actual source
carriers and recursively converts both binder contexts and codomains. The
previous negative target, ∀ A : Type, A → Prop, now has a certificate and full
carrier conversion. A checked strict-extension theorem combines its actual
formation, new certificate, and the old TerminalTypeFamily impossibility.

Boundary: this target grammar is not asserted arbitrary-substitution stable.
The fresh parameter's specialization can disappear if an external parameter is
instantiated by a function type (the earlier checked counterexample remains).
Thus adding this grammar directly to SelectedLambdaDomain.subst would require
another invariant. A live next step is to track which specializing parameters
are local to a closed family, so tests on those parameters can be rebuilt after
outer substitution; alternatively extend the shared-test interpretation through
the guarded stages themselves. Neither global computed-guard transport nor
PropFront coverage follows merely from the present stage-zero theorem. The
original strengthening goal and a strictly smaller sufficient front remain open.


## 2026-11-04 15:39:43 UTC — Preserve locally bound specialization parameters under substitution

Verdict: proved and integrated into recursive instantiation. The earlier
SpecializedTypeFamily was intentionally not arbitrary-substitution stable.
ParameterizedTypeFamily instead records only the universe parameters introduced
by its own finite target tree. Terminal input nodes shift this list; a universe
node adds its fresh parameter; a generic input references a recorded parameter.
A separate TypeParametersRealized invariant constructs actual InstN witnesses
for replacing each recorded parameter by its predecessor universe. This proves
specialized carrier readout without putting a checking law in the grammar.

Substitution only needs to fix the recorded variables, and lifting proves that
condition under every new binder. The public PolymorphicTypeFamily starts with
an empty parameter list, so every actual typed outer substitution is admitted.
Actual specialization witnesses are rebuilt in the target context; the refuted
unrestricted substitution principle for existential SortSpecialization is never
used. The grammar includes every TerminalTypeFamily and strictly extends it on
the well-typed ∀ X : Type, X → Prop target. A second example records two separate
universe parameters and references the older one through subsequent binders.

SelectedLambdaDomain now has a polymorphicFamily constructor with proved subst
and guard methods. The unchanged structural recovery and recursive checker
transport proofs therefore yield complete stage-zero comparison instantiation
and exact first-layer guarded computation through such lambda inputs.
PolymorphicExample's image applies its polymorphic predicate argument to an
external X : Type and x : X. Its assigned input beta-expands its written family,
and exact assigned recovery fails even in the full computed union. Both positive
instantiation consumers are checked from actual typing and a finite body path.

Next live route: extend the shared-test path to finite callable/projectable
images and use that independently for higher-order binder conversion. Existing
TypeInputImage already preserves actual typed call/projection trees, but using
the whole StructuralImageSubstitution theorem inside its own selected-domain
carrier proof would create a dependency cycle. A lower recovery invariant or
an explicit mutual/staged argument is required. General guarded-stage transport,
unrestricted typed image coverage, and the implication to PropFront remain
unproved. This is not a smaller sufficient irreducible front or a solution of
canonical-Eq strengthening.


### Native Pi selection retaining domain evidence (2026-11-04)

Verdict: proved for the enlarged CarrierAlignedCompare. Actual sort typings
reduce native carrier promotions to computed type checking; structural Pi
exposure then retains common domain comparison through finite computations.
Actual selected Pi replay upgrades that domain certificate to inferred mode.
The assigned Pi need not be recovered exactly. The existing identity-redex and
universe-alias witness now has the selected-domain certificate while exact
assigned-Pi recovery still fails in the entire recovered-carrier union.

Nullary unit transfer is also constructive. Typed aligned comparison with a
primitive-inert nullary family exposes that family at the selected type, so its
unit guard can be rebuilt there. The selected Pi, actual function typing,
inferred assigned-to-selected domain comparison and argument guard are returned
together. Raw and actual-erasure application consumers close the computed
application rule; the latter also handles proof-marker erasure. Rigid-head
exclusion is proved for the full recovered-carrier union from environment
rigidity and exclusion from the definition table.

Boundary: arbitrary parameterized family exposure does not follow from the
nullary proof. Applications of type-valued functions expose recursive function
comparison, including native carrier promotion; the current root-shape argument
cannot simply discard that case. Arbitrary carrier transfer and the existence
of initial native recovery/type comparison remain open. Next live extension:
retain universe equivalence during nullary exposure, then transfer nonempty
structure-field guards and their proof-field admissibility. This is not claimed
to solve general re-synthesis or furnish a smaller sufficient PropFront.


## 2026-11-04 15:49:32 UTC — Independent callable recovery breaks the binder-conversion dependency cycle

Verdict: proved and integrated. Reusing StructuralImageSubstitution to prove a
new SelectedLambdaDomain guard case would be circular. TypeInputRecovery is a
lower finite path whose leaves carry actual TypeInputImage call/projection trees
and whose other nodes are lambda, application, and core selected-output
conversion. It has ordinary typed substitution, decreasing-rank exposure, exact
selected-domain lambda exposure, and typed projection closure. Callable leaves
consume the existing argument guard using actual source-selected carrier typing;
no target comparison or semantic head-exposure principle is assumed.

CallableOrRecoveringImages extends through every typed binder and transports all
native recovery constructors, including retained projections. The interpreted
CallableImageSubstitution then transports the entire stage-zero comparison and
carrier checker. CallableDomain classifies the generic value by an actual finite
call/projection tree, is typed-substitution stable, and yields full identity
context conversion to an ordinarily equal target binder. The lower theorem
closures are explicitly checked not to reach the selected-domain or structural
recovery layer, nor SpecializedTypeFamily or PolymorphicTypeFamily.

SpecializedTypeFamily and ParameterizedTypeFamily now admit callable inputs.
Full carrier readout and PolymorphicTypeFamily.subst extend with the proved lower
context theorem. Existing selected-lambda recovery, complete recursive comparison
instantiation, and exact first-layer guarded computation rebuild unchanged.
CallableFamilyExample uses the input (Type → Type) → Prop. Its generic inner
value is callable and is proved neither terminal nor sort-specializable. The
image actually passes a type-valued lambda to its higher-order parameter; the
assigned input is beta-expanded, exact assigned recovery fails in the full
computed union, and both positive instantiation consumers hold.

Remaining boundary: callable-tree function nodes accept universe inputs. The
new family grammar permits those callable values as arguments, but the lower
image tree does not yet classify functions accepting arbitrary certified
higher-order or generic inputs. A live next route is a finite hierarchy of
image trees and carrier-family readouts. Its next callable level needs either
argument comparison promotion or exact function-domain recovery after input
conversion; carrier reindexing alone is insufficient. That hierarchy must retain dependent result
certificates and actual selected carrier typings; merely adding an arbitrary
function leaf would assume the missing argument-guard transport. General typed
image coverage, guarded-stage transport, and PropFront remain open. No smaller
sufficient irreducible front or canonical-Eq counterexample is claimed.


### Fieldwise native-carrier transfer across universe variants (2026-11-04)

Verdict: proved beyond the empty-field case. Nullary aligned exposure now retains
pointwise equivalence of the original and exposed universe lists. Individual
closed proof-field certificates transport in both directions through equivalent
well-formed universes; dependent preceding constructor domains are converted
explicitly. Actual family typings reconstruct universe well-formedness and arity.
The selected carrier therefore retains projection admissibility and every static
proof-field omission, while reusing all supplied recursive projection comparisons.

Native Pi selection returns its actual typing, exact recovery, inferred domain
comparison and rebuilt fieldwise guard together. Raw and actual-erasure application
consumers close the computed application rule. A concrete full-union consumer
discharges primitive descent, head and inertness premises from the environment.
The example telescope P : Prop, h : P compares projection zero and skips projection
one; its source universe is [max 0 0], while its selected carrier beta-expands
an instance at [0]. The two actual carrier types provably have no computation
join, yet the selected carrier guard is obtained. This tests universe comparison
and proof-field transport, not merely a shared-reduct workaround.

Remaining boundary: source guards whose fields themselves carry recursive carrier
guards require transport of their dependent projection-type recipes. Current
consumers explicitly require ordinary computed comparisons of retained fields.
Parameterized family exposure and initial native recovery/type-comparison coverage
also remain open. Do not identify this fieldwise constructor case with arbitrary
ComputedJointCarrierGuard transport or general re-synthesis. Original strengthening
and a strictly smaller sufficient irreducible front are still unproved.


## 2026-11-04 16:12:47 UTC — Preserve native higher-order heads instead of promoting their arguments

Verdict: exact protected recovery, native family-image closure, and higher-order
application reconstruction are proved. General carrier-guard promotion at
function-family endpoints remains unresolved; no counterexample to that
promotion is claimed. Merely reindexing a carrier is insufficient for ordinary
application, so this turn develops the alternative native-domain premise.

RecoveryHeadsAbove records a conservative syntactic footprint: recovery follows
application functions and projection majors, not application arguments or lambda
domains. ProtectedOracleSubstitution interprets the whole substitution but
requires exact variable/oracle transport only at the protected heads. Its local
binder extension, whole-renaming introduction, and one-binder instantiation are
proved. ScopedTypeRecovery.subst_protected preserves exact outputs using the
footprint and primitive transport; inst_protected retains both recovery and the
footprint. The erased actual-typing wrapper needs no assigned recovery of the
replacement image.

NativeFamilyTree permits finite dependent functions whose inputs have the
already proved PolymorphicTypeFamily readout. NativeFamilyImage combines actual
typing, that tree, native recovery at its own actual carrier, and the footprint.
It survives protected typed substitution and local beta instantiation; actual
application follows the dependent result tree without querying the argument's
native type. application_checked converts the supplied full argument guard from
its source-selected carrier to the native image's actual domain and uses
appCarrier. Ordinary guard-to-comparison promotion is not used.

The concrete ProtectedNativeExample accepts TypeFunctionExample.image, whose
assigned input contains a beta-expanded function type and whose exact assigned
recovery is impossible even in the full computed union. A local application
body queries only its protected function variable. Exact recovery of that body
at Prop survives instantiation by the unrecoverable argument, with its footprint
retained. The same protected native head accepts arbitrary full argument guards
at any ordinarily equal input carrier. Actual typings and the argument family's
certificate are constructed, not assumed as recovery completeness.

Next live step: integrate NativeFamilyImage as a finite selected-output recovery
leaf. Path substitution must carry ProtectedOracleSubstitution, unlike the old
unrestricted callable-image substitution. Its actual weakening and local beta
instances have exact oracle transport; the new typed instantiation law is ready.
A naive copy of the earlier exposure proof is insufficient: its backward
ordinary-equality replay does not supply native recovery of the original term.
One candidate invariant instead pairs an actual native carrier with the source's
selected raw output. A family-tree leaf handles arbitrary equal selected types;
a Pi wrapper retains exact domain syntax and recursive codomain alignment.
Application would instantiate that codomain alignment while retaining native app
recovery directly, avoiding backward replay after beta. This invariant and full
checker transport/binder-conversion integration are not yet proved.
Arbitrary function-image coverage, general guarded-stage transport, PropFront,
and canonical-Eq strengthening remain open.


### Dependent projection recipes and nested subsingleton fields (2026-11-04)

Verdict: proved universe transport for complete dependent projection recipes,
and used it for native projection recovery and a nested-carrier fragment.
Actual level-equivalent terms erase to StructuralVariant shapes. Binder contexts
are converted explicitly, so proof classification remains justified; arbitrary
common raw substitution preserves the variants. Two ProjTele witnesses for
one constructor at equivalent universes have pointwise level-equivalent domains.
Their erased field recipes therefore compare structurally after the same raw
parameters and preceding projections are substituted, including dependent fields.

A major's native type, aligned with its assigned nullary family, computes to
an actual family instance while retaining pointwise universe equivalence. Native
projection recovery at that instance returns an actual field type and an inferred
comparison with the source projection recipe. If the assigned field already
has that recipe, the comparison can feed another native projection step. This
does not synthesize initial native recovery or align an arbitrary converted field
type without its source-recipe certificate.

Structural subsingleton carriers survive raw structural variants, including
parameterized empty structures and dependent functions into them. Thus a retained
field can use either ordinary computed comparison or a structural-subsingleton
carrier. These mixed nested guards transport to an exposed nullary carrier and
then to a selected native Pi domain. Concrete full recovered-union consumers
supply primitive descent, heads and inertness from canonical Eq, sound declaration
computation and the projection family's rigidity.

The checked example has a single retained field Prop → Inner, where Inner is an
empty structure in Sort 1. The outer instances [max 0 0] and [0] have no
computational join. The field is proved non-proof at both instances, yet the new
carrier guard needs no projection comparison premise. This tests recursive
function-carrier checking rather than an omitted proof field.

Still open: arbitrary computed and recursively nested record field guards,
parameterized family head exposure, and initial native recovery/type-alignment
coverage. General universe transport of primitive computation must account for
Definitions.unfolds being indexed by exact level syntax; arbitrary sound D does
not provide a LevelCompatible certificate by definition. Existing ofEnv
compatibility and levelClosure remain live routes, not refuted alternatives.
No strengthening proof, counterexample or strictly smaller sufficient irreducible
front is claimed.

## 2026-11-04 16:29:27 UTC — actual native carriers aligned to selected outputs

**Verdict: proved complete recursive transport for this image fragment.**
The backward-native-recovery gap in beta exposure is avoided by retaining the
original term's recovered actual carrier, with a finite alignment to the source
selection. NativeCarrierAlignment has actual NativeFamilyTree leaves, dependent
Pi wrappers with their written domains, and forward computation on the selected
side. Its typed substitution theorem requires no recovery of substituted values.
Application retains native recovery at the original application; its actual
input is either a certified polymorphic family or computes to the selected raw
input. Whole-guard family conversion or carrierCompute discharges that input.

AlignedNativeRecovery now passes every source recovery constructor under
NativeAlignedOrRecoveringImages. The forall case recovers actual sort levels on
both children and reconstructs a new native sort; aligned structure majors are
excluded by actual sort/Pi-versus-rigid head inversion. The exact branch handles
ordinary projections. The resulting full ComputedJointCheck transport covers
recursive comparison and carrier guards, and gives identity binder conversion
to any NativeFamilyTree target with higher-order inputs. No protected-head
condition is required. A checked higher-order lambda both lacks exact assigned
recovery in the full union and violates RecoveryHeadsAbove 0, yet satisfies the
new image condition and transports every common-typed body comparison.

This is still a sufficient image fragment, not a proof of native coverage for
arbitrary actual terms. Its family leaves use the existing PolymorphicTypeFamily
readout; they do not certify all dependent inputs or arbitrary structure-valued
native results. Live next direction: stratify the family grammar using the newly
proved native-family context conversion as an additional input readout layer,
or extend aligned actual carrier trees to genuinely projectable result leaves.
The ordinary TypeInputRecovery beta-exposure route remains independently useful;
no general NativeFamilyImage.back or general guard-to-comparison promotion has
been established. GOAL.md's original strengthening problem remains open.


### Recursive record transport with beta-exposed carriers (2026-11-04)

Verdict: proved transport at arbitrary finite record depth, rather than only
one layer of structural-subsingleton fields. RecordCarrierGuard embeds in the
existing ComputedJointCarrierGuard. Its leaves can use the full computed
comparison language or structural subsingletons; recursive records, ordinary
field checks, symmetry, arbitrary endpoint computation and finite carrier beta
paths are included. Primitive computation of the carrier and general function
carrier guards are the explicit remaining constructor cases.

StructuralVariant now supports paired raw substitution and telescope captures.
Spine inversion retains both equivalent universe lists and pointwise variants
of family parameters. Consequently dependent projection recipes vary correctly
when both constructor universes and their parameters change. Finite beta paths
also have matching paths from a structural variant, with variant reducts;
this includes annotations and newly created redexes, without normalization.

Typed recursive carrier transport reflects the original majors' equality,
reconstructs source and target projection recipes from actual typings, and
recurses on the field guard. Beta carrier paths are replayed on both actual
types. Endpoint computations keep their context and raw paths unchanged, so
no universe-stability assumption on arbitrary primitive declarations is needed.
This proves a real recursive case while leaving primitive carrier simulation
and function-binder context conversion visible.

Native Pi selection now consumes these recursive record argument guards at a
selected nullary domain. The result includes the actual Pi typing, exact native
recovery, inferred domain comparison and reconstructed argument guard. Actual
application erasures close the existing computed application rule, including
proof-valued results. A full recovered-union consumer discharges primitive
descent, head and family inertness; initial function recovery/alignment remains
an input rather than a completeness assertion.

The checked example has an outer beta-expanded field type Inner (Sort u),
where Inner is a parameterized one-field box whose field type is its parameter.
Both source fields are proved non-proof. Changing u from max 0 0 to 0 changes
both the inner universe and its dependent parameter; beta exposure precedes
the second record check. Only the deepest projections supply an ordinary
comparison. Both guards exist despite the outer carrier types having no
computation join. Source typings and valid environment metadata are explicit.

Still open: primitive carrier computation, general function-carrier conversion,
parameterized family head exposure, and the required native coverage interfaces.
The original strengthening theorem and a strictly smaller sufficient irreducible
front remain unproved. The next structural route is universe-compatible primitive
simulation for carrier paths, or function-binder transport retaining native
outputs; neither has been rejected merely because it is larger.

## 2026-11-04 16:44:19 UTC — finite native-input hierarchy without a fixed higher-order bound

**Verdict: proved at every finite level, with a uniform syntax coverage theorem.**
One more hard-coded family constructor would repeat the previous proof at each
higher-order input. Instead, NativeFamilyFramework.InputLaws packages precisely
typed substitution and whole-carrier guard conversion for an input predicate F.
The complete native alignment, recovery substitution, recursive checker transport,
and binder-context conversion are now proved once with those explicit laws.
The generic theorems are conditional on InputLaws; the final ranked results
supply all of those laws by finite induction, rather than assuming completeness.

Extension F admits old polymorphic targets and telescopes whose inputs are native
Tree F certificates. Its substitution law uses F's substitution law; its carrier
readout uses the proved native binder conversion for F, then recurses on its
codomain. Ranked 0 is PolymorphicTypeFamily and Ranked (n+1) is Extension (Ranked n).
ranked_inputLaws proves both laws at every level. Monotone embeddings allow a
single uniform level for every finite SortPiTree (universe leaves and Pi nodes
nested on both input and result sides). Thus there is no fixed bound on
higher-order depth in this fragment; neither normalization of terms nor a
native recovery completeness hypothesis is used.

The actual typed target (((Type → Prop) → Prop) → Prop) has a level-one certificate
and is proved outside PolymorphicTypeFamily: its generic input is a function
whose own input is a Pi, excluded by the old literal-sort callable readout, and
it is not terminal. SelectedLambdaDomain.rankedFamily consumes the new readout,
so the existing structural recovery route now supports arbitrary finite levels
for complete recursive comparison and exact first-layer guarded computation.

Still missing: coverage of arbitrary dependent type syntax and general native
recovery. SortPiTree has no variable, constant, or application leaves; the larger
Ranked grammar retains earlier polymorphic leaves and dependent telescopes but
is not proved to cover all types. The generic framework can now accept further
proved input laws without redoing the checker induction. Extending parameter
tracking through new native-input telescopes, and integrating genuinely
projectable native results, remain live routes. No sufficient strictly smaller
irreducible front or canonical-Eq counterexample has been established, and the
original strengthening theorem remains open.

## Concrete carrier computation across universe variants

Verdict: proved beyond beta-only record transport. StructuralVariant now
simulates each context-independent ErasedIotaPrimitive: actual declaration
unfolding uses the existing level-compatibility theorem; projections select
corresponding captures; concrete quotient/capture and fixed-template iota rules
rebuild their checks from actual typed matches. Templates vary both their own
universe annotations and all captures. Finite compatible computation follows
by induction, replaying both sides at composition points to recover intermediate
typings. Lambda and Pi bodies may have different actual contexts. No termination,
normal forms, arbitrary primitive stability, or intermediate typing assumption
is introduced.

RecordCarrierGuard.core stores a finite core path and the concrete compatibility
evidence. Its embedding uses the existing carrierCompute rule; recursive record
variant transport simulates the path, realizes its endpoints, and continues at
the reducts. Existing native record application consumers inherit the extension.
For WF.params and Definitions.ofEnv, declaration soundness, level compatibility,
concrete pattern provenance, and core inclusion in the recovered union are all
discharged. The stored-type-alias theorem transfers a record guard between
universe-equivalent instances even when their unfolded bodies have different
universe syntax.

Remaining: general function-carrier guards change the context of their recursive
child, whereas this record transport keeps endpoint checks in their original
context. Context conversion of the record certificate itself is a concrete next
step; transporting only its old ComputedJointCarrierGuard image loses the
recursive certificate needed for another carrier variant. General parameterized
native head exposure and arbitrary recovery coverage also remain open. This is
a verified fragment extension, not a sufficient smaller front or a solution of
UniqueTyping.weakN_iff.

## 2026-11-04 17:01:18 UTC — locally generic values as dependent family results

**Verdict: proved a dependent result extension outside every previous finite level.**
The earlier Ranked hierarchy increased input depth but every certificate still
ended in a literal sort. A locally introduced successor-universe parameter can
instead serve as the final result carrier. The existing actual specialization
lemma reads a full guard at any ordinarily equal source carrier as ordinary
comparison when the target is that parameter. No existential-specialization
substitution closure is assumed: DependentFamily records local parameters and
its substitution theorem explicitly fixes them; empty-parameter roots rebuild
the witnesses under their own binders after arbitrary outer substitution.

DependentFamily combines old parameterized leaves, generic result leaves,
terminal/callable/native inputs, universe binders, and parameter inputs.
ValueRanked iterates this grammar using the generic native InputLaws framework.
Its complete laws are proved by finite induction, it is monotone, and every old
Ranked n certificate embeds in ValueRanked n. The inhabited identity carrier
∀ X : Type, X → X has a level-one certificate but is proved outside Ranked n
for every n, using the old grammar's final-sort invariant. Whole-carrier readout
and native binder conversion for functions accepting such identity values are
concrete consumers. SelectedLambdaDomain.valueFamily connects the new laws to
complete comparison and first-layer computation through selected body paths.

The checked example accepts a polymorphic identity function, applies it to Prop
and an ambient proposition, and has a beta-expanded assigned input. Exact native
assigned recovery is refuted in the full computed union; comparison and exact
first-layer computation nevertheless transport through the image. This extends
both the previous finite input hierarchy and its actual substitution consumers.

Still open: native coverage for arbitrary dependent applications. The proved
outer-substitution law does not assert that a generic result's specialization
survives instantiating its own universe parameter by an arbitrary type. Native
Tree certificates still require sort-ending actual result trees. Consequently
this result is not a native context-conversion theorem for every polymorphic
value itself. Tracking selected/native alignment through dependent parameter
instantiation, or integrating additional projectable result classes, remains
live. No general strengthening proof, canonical-Eq counterexample, or strictly
smaller sufficient irreducible front is claimed; GOAL.md remains active.

## Full core joint checking across universe variants of binder contexts

Verdict: proved, including function carriers. The record-only transport boundary
is no longer needed for the context-independent core. Native recovery now
simulates StructuralVariant changes of both the context and term, covering all
constructors: variable oracle, sorts, constants, lambdas, applications, Pis,
projections and conversion. The projection result varies the major as well as
universes and family arguments, so preceding-field captures remain related.
Actual recovery replay reconstructs the types at conversion points.

A simultaneous induction over the existing ComputedJointCheck transports ordinary
comparison through equal actual contexts with structural variants of their raw
entries, and transports full carrier checking through structural variants of the
assigned carrier. Application recovery can select a changed domain; its argument
guard is rebuilt by the carrier induction. Function guards extend both actual
contexts with their changed domains; their recursive child is handled by the
same induction. Nested record recipes use the proved paired-parameter universe
transport and source/target projection typings. Every existing constructor is
covered; no new comparison constructor or future-stability certificate is used.

The generic theorem names two computation requirements: exact endpoint context
transport and typed structural simulation. Both are proved for the entire
concrete ErasedIotaPrimitive core. Well-formed structural context variants imply
actual IsDefEqCtx, so the core context consumer does not need that equality as
an input. Actual WF.params/ofEnv carrier transport discharges declaration and
pattern compatibility. A function-to-record example builds its source guard
from ordinary finite retained-field checks under the source domain and obtains
the target guard under the varied domain.

Remaining: the two computation requirements are not yet proved for recovered
singleton or Eq-prefix stages. Context transport of those rules must transport
their family/argument certificates; structural simulation additionally changes
captured endpoint syntax. The current theorem transports comparison endpoints
unchanged across context conversion, and is not itself arbitrary endpoint-
variant closure. Native recovery and checking completeness for arbitrary terms,
parameterized aligned head exposure, and the original strengthening front all
remain open. This is a closed core-fragment theorem, not a sufficient strictly
smaller irreducible front.

## 2026-11-04 17:27:34 UTC — exact dependent result alignment resumes unrestricted native recovery

**Verdict: proved recursive transport with arbitrary aligned result carriers.**
The previous native Tree/Alignment grammar stopped at sort results. Merely adding
a generic parameter leaf would lose its specialization when an application
instantiates that parameter. Instead, preserve exact agreement of the selected
and actual dependent result. Added Alignment.exact for any actual carrier and
Alignment.input for a certified changed input plus an aligned dependent child.
Substitution preserves exact agreement even when the result becomes a function,
structure, or another arbitrary typed carrier; no specialization witness needs
to survive that change.

Exposure now returns either a finite native tree, actual-carrier computation to
selection, or a Pi with its retained input route and child alignment. Application
uses the exact-computation branch to resume ordinary native recovery; typed
forward replay embeds that exact recovery back into the relation. The forall
case still recovers an actual sort, and the projection case now recovers the
selected structure major exactly instead of excluding all structure results.
The complete source-recovery induction and recursive checker transport pass
with this enlarged relation. The old shape and not_projection APIs were updated
to expose the exact branch and require exclusion of exact recovery, respectively.

ImageSubstitution.aligned_context and both full checking consumers now convert
binders using an alignment rather than a sort-ending tree. In particular, equal
input annotations with identical dependent codomain syntax suffice with no
shape restriction on that codomain. A more general constructor also permits
forward core computation from the actual result erasure to the selected one.
The concrete example converts a polymorphic identity binder whose universe
input was beta-expanded. Its target is outside Tree F for every input predicate
F, yet all recursive carrier guards transport. Applying the native identity
parameter at an arbitrary Type resumes exact recovery at that actual type; a
concrete instance recovers Prop → Prop after both applications, with no recovery
premise for the argument.

Still missing: arbitrary result annotation change known only by ordinary
semantic equality. Exact erasure or retained forward core computation is a real
restriction, not a general equality-to-computation theorem. This does not prove
native coverage for every dependent function or eliminate the original front
obligation. General alignment of differing dependent results remains live;
no strengthening proof, canonical-Eq counterexample, or strictly smaller
sufficient irreducible front is claimed. GOAL.md remains active.

## Repair exact native carriers by explicit universe computation

Verdict: proved for the level-extended core, without changing the recovered
comparison judgment. Rather than requiring two structural variants to have an
old computational join, add theory-only primitives at sort and constant nodes
for equivalent target universes with proved well-formedness. Their arbitrary-
block descent follows from LEquiv.defeq and exact erasure/proof-status arguments.
Compatible closure computes from any structural variant to a typed target.
These rules do not change the executable and do not normalize terms.

A generic finite simulation lemma uses typed semantic replay at composition
points, so the operational PatternCompute representation is no longer required.
The old iota/delta primitives simulate as before; a universe step simulates by
an empty path, composing structural variants. Thus the level-extended core has
both exact context transport and structural computation simulation. Full native
recovery and ComputedJointCheck transport remain available over that base.

At a recovered comparison node, simulate both native recoveries, select the
left output's actual typed representative, convert the right output to it using
explicit universe computation, and transport the full carrier guard to that
output. This retains CarrierRecoveredCompare.recovered with one literal common
carrier. Induction covers the entire recovered comparison language under
structural context conversion. The regression theorem exhibits sorts at max 0 0
and 0: they have no common native output even in the old recovered union, but
one successor-level conversion gives a shared output in the new base.

Finite recovered singleton/Eq-prefix stages over the new base embed all old
stages at the same indices; their union has proved arbitrary-block semantic
descent. This does not yet prove higher-stage context/variant certificate closure.
The new sort primitive also means the old constant-or-projection PrimitiveHead
interface cannot be reused unchanged. Arbitrary equal carriers can differ in
term syntax, beyond universe annotations, so neither general native completeness
nor the original strengthening front follows. Next: transport typed singleton
family guards under structural context conversion, including their generated
residual telescopes, then examine higher-stage structural endpoint simulation.

## 2026-11-04 17:44:57 UTC — Substitute native values whose assigned carriers join their outputs

Verdict: **proved full repaired-core substitution and a concrete boundary of
forward exact-result alignment**. Extend simultaneous carrier/oracle reduction
to ComputedJointCheck, including appComputed. Require each retained variable
image to natively recover a reduct of its substituted assigned carrier; native
output conversion also admits any common reduct of assigned and native types.
This image law lifts through arbitrary binders. Induction on every native
recovery constructor preserves it; the conversion case uses typed core
confluence, while application and projection propagate computed components.
The complete recursive checker then transports, using forward carrier reduction
for each recovered application's already-transported argument guard. This gives
single-instantiation consumers and unrestricted-shape binder conversion when
both annotations compute to a common carrier.

A beta-expanded generic type binder transports to the type variable itself.
The old NativeFamilyFramework.Alignment cannot align that variable to its
expansion, for any input predicate: its shape theorem forces forward computation
from a bare variable, which is fixed. This distinguishes the new computational
image method from that grammar, without claiming inclusion of every old family
certificate or completeness for arbitrary ordinary equality.

The scope remains ErasedQuotCore.Step with QuotRegistered and concrete-pattern
hypotheses. Exact native recovery of arbitrary non-proof images, arbitrary
ordinary-equality carrier joins, and confluence at guarded singleton stages have
not been proved. A useful next step is to combine this common-reduct image law
with the independently proved finite-family alignment cases, then determine
which source singleton-stage substitutions still lack certificates. No smaller
sufficient irreducible strengthening obligation is claimed; GOAL.md stays open.

## Close every guarded stage by converting structural variants back first

Verdict: **proved exact context transport and structural simulation at every
finite level-extended recovered stage and at their union**. A typed structural
variant converts by explicit universe steps back to the original raw term.
Exact context transport can then replay the original computation with literally
the same output. Consequently stage-n context transport implies its simulation;
the full recovered checker transports singleton family guards through generated
residual telescopes, and joint checking transports Eq-prefix guards, supplying
stage-(n+1) context transport. This closes the induction with canonical Eq and
sound declarations alone, without level-compatible declarations, concrete
patterns, or a per-stage simulation assumption. Finite certificate bounds prove
that the union is closed under its own singleton and Eq-prefix guards.

The literal binder example changes Sort (max 0 0) to Sort 0, proves the raw
contexts unequal, and transports arbitrary finite-stage computation without
raising its stage. Structural variation still preserves term constructors:
arbitrary beta-related annotations and general semantic carrier conversion are
not covered. Next, restore exact native recovery outputs by the same backwards
universe path and transport the entire aligned comparison language. Original
PropFront and weakN_iff remain open; no smaller sufficient front is claimed.

## Restore exact native outputs and transport full aligned checking

Verdict: **proved without enlarging the comparison or recovery grammars**.
After structural context transport, native recovery initially returns a universe
variant of its old output. The old actual carrier is still typed in the new
context, so explicit level computation converts the new native output back to
that literal original output. This removes even the existential output variant
from context transport. The entire CarrierAlignedCompare induction then closes:
its independently recovered type endpoints remain fixed; actual uniqueness
puts them at a common sort for recursive type comparison. Sorted binders, eta
bodies, structure fields and both native-promotion rules are included.

A separate endpoint law converts arbitrary structural variants back to the
typed original comparison endpoints. Combined with the proved stage/union laws,
this yields full aligned checking across structural context and endpoint
variation at every finite stage and the closed union. It needs an existing
source comparison certificate and common actual source endpoint typings; it
is not declarative comparison completeness. Arbitrary beta-shaped changes of
context annotations and guarded-stage joins remain outside this result. The
original strengthening question and its required deliverables remain open.

## 2026-11-04 18:02:08 UTC — Combine computational joins with finite native family alignment

Verdict: **proved a single substitution law containing both earlier methods,
with a checked inhabited case requiring their combination**. NativeJoinFramework
retains a core computation from the selected type to an intermediate type
already covered by NativeFamilyFramework.Recovery. Typed confluence closes
forward selection conversion; backward selection just composes paths. Application
first reduces the selected Pi and its full argument guard, then applies the
finite input-family readout. Projection exposes a rigid intermediate carrier
and computes its field recipe. All recovery and full checker constructors
transport. Both earlier image and interpreted-substitution laws explicitly embed.

The law also discharges ComputedZeroGuardSubstitution: all generated singleton
and Eq-prefix guards transport beneath their residual telescopes. Complete
first-stage computations retain the exact substituted output at stage one;
paired beta-redex comparison and single-instantiation consumers are supplied.
No higher-stage confluence premise or semantic checking oracle was introduced.

The source example combines a max 0 0 universe annotation with a beta-expanded
generic result. The target uses universe 0 and the unexpanded result. A concrete
well-formed context contains the generic type and its value; one function
inhabits both annotations. The combined intermediate certificate is proved,
while direct finite Alignment fails for every input predicate and the complete
annotations have no common ordinary-core reduct. Thus this is not merely an
external disjunction of the previous methods. This boundary is specifically
about the original core and these two earlier certificates, not all alternative
methods or independently enlarged universe-computation cores.

Remaining: arbitrary well-typed substitution images still need coverage by the
combined Recovery relation. The native-recovery induction remains at repaired
core stage zero; the stage-one computation result uses transported base guards
and does not establish stage-one native recovery or arbitrary-stage confluence.
Next, examine which singleton-stage recovery conversions can preserve this
invariant without assuming a confluence law for the full guarded computation.
GOAL.md remains open; no sufficient strictly smaller irreducible front is claimed.

## Recover native head exposure and full argument guards after universe steps

Verdict: **proved precise root laws and full nullary-domain guard transfer**.
The old PrimitiveHead interface is false at every level-extended stage: a typed
Sort (max 0 0) to Sort 0 primitive is a checked witness. Pi domain exposure only
needs exclusion of Pi roots, which all these stages satisfy. Rigid nullary
families are not inert under explicit universe conversion, but their roots
preserve family and pointwise equivalent levels. Generalizing the existing
exposure inductions to these exact laws retains both old public APIs as
corollaries and recovers native Pi/domain selection in every stage and union.

After exposing a selected nullary family, full joint structural transport moves
an arbitrary existing carrier guard to the exposed universe instance. A final
carrier computation lifts it to the selected domain. Thus the argument premise
is the complete existing ComputedJointCarrierGuard, not a separate finite record
grammar. The selected domain may have different term syntax; it must have an
existing aligned comparison with the assigned nullary family. Actual application
erasures, including proof results, are covered. For actual environment
registries and registered structures, soundness and rigid-family exclusion are
discharged. Native recovery and its type comparison remain source premises.

This removes the old head-interface incompatibility and the restricted argument
guard grammar for nullary domains. Parameterized families, arbitrary Pi carriers
and general comparison/native completeness remain open. In particular the
new theorem does not supply arbitrary beta-context transport or a sufficient
strictly smaller front. Original weakN_iff and GOAL.md remain unresolved.

## 2026-11-04 18:22:43 UTC — Exact native images through every guarded stage

- Replace the mixed native/family framework's core conversion paths by guarded
  paths: still open. The conversion case would need a suitable join, and a
  path inside a dependent codomain must survive argument substitution. Actual
  prefix confluence alone does not supply erased residual guard certificates.
- Use exact native image recovery at finite stage k and transport a source
  certificate at stage n to n+k: proved. Forward replay types each selected
  source carrier before transporting its conversion; no guarded confluence or
  backward recovery is needed. Both full computed-joint checking views, native
  recovery and computation are covered, including singleton and Eq guards
  below their generated telescopes.
- Collect per-image union bounds and compose certified images: proved. Finite
  source contexts give one common bound. Image composition adds bounds; union
  images are closed under typed composition. A previously established
  neutral-unit Eq-recursion image recovers its function type at stage one,
  cannot do so in any old compared-K stage, and now instantiates arbitrary
  finite computed-joint computations with the n+1 bound.
- Make exact image recovery universal: rejected by existing checked converted
  input examples (ProofErasureTypeInputConvertedExample.assigned_recovery_failure
  and ProofErasureTerminalDomainExample.assigned_recovery_failure), which already
  obstruct exact recovery over the computed union. This is a complementary
  higher-stage transport theorem, not a replacement for mixed native/family
  alignment or an unrestricted substitution theorem.

Validation: 785-job build, 102 selected modules, 773 dependency roots (41 new),
maximum closure 12,790; standard axioms only. The original strengthening
sorry remains. No GOAL.md deliverable is claimed; extending higher-stage repair
to images without exact assigned-type recovery remains an open mathematical step.

## Separate parameterized computed exposure from aligned eta instantiation

Verdict: **proved exposure and parameterized fieldwise application checking
for the complete computed grammar**. SpineRootLevels allows primitive universe
conversion at a rigid family while preserving its term arguments. Finite
computation then retains the family, equivalent universe list, and one scoped
computation for every argument. These root laws hold at every level-extended
recovered stage and at the union.

ComputedJointCompare.const_spine_levels_exposure covers every constructor,
including appCarrier and appComputed. All three application rules retain an
inferred function comparison; its exposure path supplies the head computation.
The appComputed case does not need to instantiate its chosen lambda or assume
confluence of that path with the exposed function path. Typed mode conversion
extends this to either mode at type endpoints. Exposure retains universe
equivalence and arity even when both parameter lists change through computation.

Native Pi selection retains a domain comparison in the computed grammar.
Family exposure plus the existing universe/proof-field theorem then transfers
all ordinary retained field comparisons to the selected parameterized carrier.
No equality of parameter syntax, literal carrier join or semantic head premise
is required. Actual application erasures are handled at every finite stage and
the union; the actual registry discharges soundness and rigid-head exclusion.

Full CarrierAlignedCompare still adds a distinct issue at partial family heads:
its native carrier promotions can lead to function guards or eta bodies under
a fresh binder. The raw spine induction alone does not instantiate those bodies
at arbitrary supplied parameters. This is an unresolved proof case, not a
counterexample to full aligned exposure. Carrier-valued dependent field guards
also remain beyond the new fieldwise consumer. Next investigate native sort
selection for typed family arguments and the image evidence needed to instantiate
these eta bodies. General native/comparison completeness and original PropFront
remain unproved; no strictly smaller sufficient irreducible obligation is claimed.

## Exact universe selection from native aligned evidence

Verdict: **proved certificate selection, with coverage still explicit**.
SortRootLevels captures the root law actually satisfied by the level-extended
stages: a sort may move to a syntactically different equivalent universe.
Finite computation preserves that equivalence. A paired induction over the
complete computed, recovered and aligned comparison grammars then exposes a
sort with equivalent level at the other actual type endpoint. Actual typings
exclude function/structure carriers; native promotions reduce to the existing
typed computed checker. Neither the false old PrimitiveHead interface nor a
semantic head-exposure premise is used.

An existing native recovery of e : Sort u, together with an existing aligned
comparison of its output to Sort u, now selects exactly Sort u at the same
finite stage. The exposed sort's equivalent universe is repaired by one explicit
level primitive. The closed union has the same consumer. In fact existence of
such aligned native evidence is equivalent to exact assigned-sort recovery;
this is a certificate equivalence, not universal native coverage.

The earlier inhabited-proposition recovery test was checked before introducing
this interface: even that restricted any-output coverage forces sort recovery
and yields PropositionFront in the old joint union. Thus a universal recovery
premise cannot be silently substituted for the remaining problem. The present
result can supply exact type-argument images only when its native and alignment
inputs are already available. It does not yet instantiate arbitrary eta bodies,
cover arbitrary supplied family parameters, or establish a sufficient strictly
smaller front. Original weakN_iff and GOAL.md remain open.

## 2026-11-04 18:39:45 UTC — Universe-converted native images through recovered guarded stages

- Generalize native-image transport over the computation relation instead of
  treating the old computed stages as fixed: proved and factored into shared
  NativeImages/NativeImageRecovery modules. All nine original public signatures
  of ExactStageImages/ExactStageRecovery remain unchanged and their clients build.
- Combine the shared induction with explicit universe conversion and recovered
  singleton-family guards: proved. LevelRecovered stages transport computation,
  native recovery, full joint checking and CarrierRecoveredCompare from n to n+k
  for stage-k native images. The new family case preserves the literal common
  native output of both endpoints and transports the existing full carrier guard.
  The image class composes; finite-context bounds give union consumers.
- Permit a structural universe variant of the assigned native output: proved.
  Typed universe computation converts the native output to the exact assigned
  type at the same stage. Both TypeInputConvertedExample and TerminalDomainExample
  now have stage-zero native recovery and unchanged-stage instantiation at every
  guarded layer, despite their checked old-computed-union recovery failures.
- Infer arbitrary image coverage from these repairs: refuted. The new
  TypeFunctionExample.level_assigned_recovery_failure proves that the genuinely
  higher-order image with a beta-expanded assigned input still has no exact
  recovery in the entire level-extended recovered union. A Pi written domain
  remains Pi-shaped under its forward domain computation; the assigned input
  has an application head. This survives universe conversion and recovered guards.

Validation: 839-job build, 113 selected modules, 831 audited roots (58 new),
maximum closure 12,797; standard axioms only. These are checked transport
and boundary results, not a strengthening proof or a sufficient smaller front.
The next unresolved repair must handle assigned domains beyond forward native
computation and structural universe variation. GOAL.md remains active.

## Full aligned native-image transport and certified eta instantiation

Verdict: **proved for exact native images, including sort-selected images**.
The shared native-image transport previously stopped at CarrierRecoveredCompare.
A typed induction now covers every CarrierAlignedCompare constructor: recursive
native-type alignment, recover/common-carrier promotion, sorted binders, eta
bodies, eta-lambda guards and retained structure fields. Existing recovery,
computed-carrier and recovered-comparison transport discharge all callbacks.
Actual source typings align independently recovered types before recursively
transporting their comparison; literal substituted outputs remain unchanged.

Finite-stage full aligned certificates transport from n to n+k for stage-k
native images. The union transports without choosing one global finite bound
for the aligned derivation: existing computation transport collects the needed
image bounds locally. Actual-erasure substitution and single instantiation
follow. The previous exact-sort selection now supplies image recovery from an
existing native output plus its aligned comparison to the assigned universe.
Thus arbitrary full aligned bodies under a type binder can be instantiated at
such certified arguments. Explicit eta consumers replace the fresh eta argument
and return comparison with the actual application, including proof-valued
instantiations.

This closes full aligned eta instantiation for certified native arguments, not
unrestricted substitution. The committed TypeFunctionExample level-union
boundary still excludes a higher-order image whose assigned input is a beta
expansion of its written Pi domain. Sort selection does not eliminate that
counterexample or produce native evidence for arbitrary type arguments.
General full aligned parameterized-family exposure still needs analysis of
partial-function carrier checking and the available supplied-argument images;
it is not implied merely by the new substitution theorem. Original weakN_iff
and PropFront remain open, with no smaller sufficient irreducible front claimed.

## 2026-11-04 19:03:21 UTC — controlled backward beta expansion

Verdict: checked positive progress. Replace the forward-only computation
restriction by two source-reconstructible expansion rules. ConstantExpansion
wraps a retained source in a lambda with an unused Type binder and applies it
to the closed argument Prop. NativeIdentityExpansion wraps a source in an
identity lambda whose annotation is supplied by preceding-stage native recovery.
The former introduces no free variables; the latter descends its annotation
using the existing source-typed native recovery theorem. Both primitives have
arbitrary-block descent without strengthening. Proof markers cannot undergo
the displayed constant expansion; typed substitution preserves that necessary
non-proof guard. Native recovery already excludes proof-marker sources.

ErasedExpansionStage retains universe conversion, core computation, recovered
singleton-family guards and full computed Eq-prefix guards. Identity expansion
uses the preceding stage. All old level-recovered stages embed at the same
index. The union is closed under its own guards by finite-certificate bounds.
Exact native-image substitution transports computation, native recovery, full
joint checking and recovered-family comparison from n to n+k; composition and
union consumers are included. New primitive transport uses the shared native
recovery theorem rather than a semantic annotation-completeness assumption.

Two strict checked improvements: TypeFunctionExample.expansion_repair pairs the
old full level-union failure with new stage-zero recovery at the beta-expanded
assigned Pi domain. Its actual higher-order image now instantiates every finite
expanded computation and full recursive comparison at the unchanged stage.
The generic_type_identity_repair theorem pairs old full-union computation
failure with a new stage-one identity expansion of an actual generic Type
variable. The identity-forward theorem also admits dependent annotations when
native recovery supplies them; it is not limited to literal universe domains.

Limits: this does not authorize arbitrary backward beta expansion, whose
redex can introduce variables not present in its reduct. The controlled rules
do not establish arbitrary assigned-type recovery or declarative comparison
completeness. Previous no-Pi-root exposure lemmas cannot be applied to the new
system: constant expansion intentionally sends a Pi to an application.
Next investigate native recovery and exposure with these source-reconstructible
expansions, retaining the exact guard-transport invariant. Original weakN_iff
and PropFront remain open; no smaller sufficient irreducible front is claimed.

Validation: 774-job build, eight new modules, 69 audited roots including
primitive constructors and recursors, maximum dependency closure 11,096.
Opaque bodies and recursor rules were traversed; all global and framework
independence exclusions passed. Only propext, Classical.choice and Quot.sound
occur. Artifacts and hashes: /tmp/expansion-validation.json and associated
/tmp/expansion-* files. No executable change, PR extraction or coordination.

## Demand-shaped recovery versus native common reducts in the guarded union

- Restrict exact image transport to Pi-shaped recovery demands: **refuted**.
  The actual higher-order TypeFunctionExample image remains typed at its
  beta-expanded assigned type. A fresh variable at that type natively recovers
  a Pi; substituting the image cannot recover the instantiated demand even in
  the complete level-extended recovered union. The checked
  level_pi_demand_instantiation_failure makes the source demand and failed
  substituted output explicit. Thus inspecting the outer recovery head alone
  does not avoid the old exact-output obstruction.
- Postpone explicit universe steps until after beta: **proved**. Every mixed
  finite path factors into a beta path followed by StructuralVariant. Existing
  beta/variant simulation handles composition and redex creation. Typed beta
  confluence then supplies an exact beta/universe join; replay of one residual
  provides the level well-formedness needed for the final explicit conversion.
  No normalization or general guarded confluence is assumed.
- Identify guarded paths for which this confluence applies: **proved** for
  PureLambda, the raw grammar without constants or projections, retaining
  arbitrary applications, lambdas, Pis, sorts, variables and proof markers.
  Beta and level conversion preserve the grammar. The stage-root classifier
  excludes every old primitive head at every intermediate node. Consequently
  all finite-stage and union computations from this syntax use only beta and
  universe steps, even after created redexes are contracted. Typed confluence
  follows for paths from different stages, with pure beta/universe residuals.
- Repair selection by a common reduct instead of the exact expanded output:
  **proved at all guarded stages for typed pure carriers**. An existing native
  output reached from the assigned carrier joins every later selected reduct.
  The residual uses only beta/universe steps, so native recovery stays at its
  original stage. The higher-order counterexample has such native evidence
  already at stage zero and retains it through every later guarded selection,
  while its exact assigned recovery remains impossible.

This closes a concrete forward-selection join case beyond the prior core-only
native-join framework. It is not unrestricted image substitution. Substituting
an arbitrary actual argument into a dependent pure codomain can introduce
constants or projections, leaving the proved confluence class; the resulting
guarded beta residuals still need justification. Generic function-carrier
reindexing also still needs binder transport. No reduction of arbitrary
PropositionFront to this grammar, canonical-Eq counterexample or sufficient
strictly smaller irreducible obligation is claimed. GOAL.md remains open.

## 2026-11-04 19:14:38 UTC — retaining expansion certificates and local beta squares

Verdict: checked progress on the exposure problem created by controlled
expansion. Added arbitrary-block certificate descent for every expanded stage
and its full union. Universe steps use raw retraction only after semantic
descent has reconstructed a lifted target. Identity expansion descends its
native annotation certificate as well as its actual typing. Singleton guards
retain their lower generated-telescope certificates. Computation and native
recovery at prescribed lifted outputs are invariant under insertion of unused
binders, at the same finite stage.

The constant-wrapper square now deletes its unused binder after arbitrary
expanded body computation, retaining a lower computation of the original
payload. Any resulting annotation and argument beta-contract to that lower
payload. The identity-wrapper square handles arbitrary expanded body and
argument computations using only the ORIGINAL argument's native certificate.
Reify the computed body, instantiate its computation using the original image,
and then compute all argument occurrences using primitive renaming. The join
bound is max(n+k,m), for body stage n, original native image stage k and argument
stage m. Neither native recovery of the computed argument nor a no-Pi-root
hypothesis is needed. Full-union consumers collect finite bounds separately.

Concrete rejection: arbitrary reverse beta, even restricted to typed upper
endpoints, does not satisfy source-typed primitive descent. A closed Prop
expands above one inserted Type variable to (fun _ : Type => Prop) x. The
redex is actually typed, and its erasure retains x; no lifted lower proof shape
has that raw target. erased_typed_reverse_beta_descent_failure formalizes this
for every Params environment, including canonical-Eq environments. This is
NOT a counterexample to strengthening: it refutes the proposed expansion rule.

Exposure remains open: local body/argument squares do not by themselves show
that an arbitrary interleaving of guarded roots and expansions has a Pi reduct,
and they do not retain the domain comparison needed by native Pi selection.
Next live approach: a forward finite-observation invariant at the empty
constant interpretation. PrimitiveHead sources (constant/projection-headed
spines) have no such observation, so their root cases should be vacuous;
universe steps preserve head observations and the controlled expansions are
beta-reversible. Adapt PureObservation to proof shapes, or encode proof shapes
into VExpr with an opaque constant for the proof marker, proving beta reflection
and forward observation transport. Operational adequacy could then give Pi/sort
head persistence without guarded confluence. This is an unimplemented idea,
not a proven exposure theorem. The observation model's known failure as an
equality-reflection model does not reject its narrower operational use here.

Validation: 710-job build of three new modules; all 18 exact roots passed
the opaque-body/constructor/recursor dependency audit and framework exclusions,
maximum closure 11,089. Only propext, Classical.choice and Quot.sound
occur. Original weakN_iff remains open; no smaller sufficient irreducible
obligation is claimed. No executable modification, PR extraction or coordination.

## Pure-context confluence with controlled beta expansions

- Extend the pure beta/universe argument to the expanded stages: **proved**,
  with a pure-context hypothesis. Constant and native identity expansions
  beta-contract back to their source. A forward-only factorization is no
  longer appropriate, so use BetaLevelJoin: beta reducts related by structural
  universe variation. Raw annotated beta confluence follows by lifting the
  parallel-development diamond to its reflexive-transitive closure. This makes
  BetaLevelJoin transitive, symmetric and congruent at every constructor.
- Keep expanded computations inside the pure grammar: **proved** when every
  context entry is PureLambda. Scoped native recovery then returns a pure
  output whenever the source is pure and the primitive roots preserve purity.
  Induction on expanded stages closes this premise, including identity
  expansion's recovered annotation. The context hypothesis is explicit;
  pure source syntax alone does not constrain variable-type lookups.
- Join arbitrary expanded paths in this fragment: **proved** at every pair
  of finite stages and at the union. Contextual paths yield raw join
  certificates; typed endpoint replay turns the final structural variation
  into an explicit level path. Both residuals use only forward beta and level
  conversion, although the original paths may contain arbitrarily many
  expansions and nested guard certificates. No normalization is used.
- Preserve native selection under these paths: **proved**. Existing native
  common-reduct evidence stays at the same native stage. A raw join to a
  well-formed sort yields a forward path to that exact sort, so an expanded
  computation from an assigned sort to an existing native output can be
  reversed for exact native sort selection. This does not create native
  evidence where none was supplied.

Next live specialization: extract a Pi head and raw domain join from a
BetaLevelJoin against a displayed Pi. Beta reduction preserves Pi heads and
reduces both components, while StructuralVariant preserves their constructors.
Typed domain replay should turn the domain join into a computed comparison.
This could retain a selected Pi domain through arbitrary expanded paths in
this fragment, without the false no-Pi-root law. It is not yet implemented.
General guarded head exposure, image coverage and declarative comparison
completeness remain open; these fragment results do not complete GOAL.md.

Validation: main and isolated 874-job builds; 137 source modules byte-identical;
708 exact roots audited through opaque bodies, constructors and recursor rules,
maximum closure 11,507. Only standard logical axioms; no sorry or forbidden
strengthening/framework dependency. Original weakN_iff remains open.

## Pi/domain selection from expanded raw joins

The specialization proposed in the preceding entry is now **proved**.
BetaLevelJoin.pi_exposure uses beta reduction of both components of a Pi and
structural-variant inversion to return a beta Pi reduct with joins of its
domain and codomain against the displayed Pi components. Typed replay of the
domain join supplies an inferred-mode ComputedJointCompare whenever the target
relation includes explicit level steps. Existing native evidence can therefore
select this Pi while retaining its domain comparison at the original native
stage. Finite expanded paths and union paths from a pure assigned Pi instantiate
the result in pure contexts; the selection path can use an unrelated stage.
No canonical-Eq hypothesis is required for this specialization: only raw
expanded join certificates and typed beta/universe replay are used.

The returned codomain is raw-beta/universe-joined to the original codomain;
it is not asserted to recover the exact original Pi annotation. Nor is native
coverage produced for arbitrary typed sources. To use this in a full carrier
transport, the remaining question is how to transport dependent argument and
codomain certificates when the newly selected domain is related by computation
rather than structural universe variation. Existing exact-native-image
transport does not automatically discharge that obligation.

Next concrete candidate: transport pure native recovery between contexts whose
lookup types have BetaLevelJoin certificates, allowing the transported native
output to be joined to the original output instead of equal to it. For an
application, the Pi-exposure lemma would select the transported function's Pi;
raw join compatibility with instantiation would then retain the output join.
For conversion, pure expanded computation already supplies a raw join. This
requires lifting and substitution lemmas for BetaLevelJoin and a paired context
lookup lemma; it is not yet proved. It may avoid reproducing expanded guards
in the target context, but using joined outputs inside full carrier comparison
still needs a separate argument.

Validation: 709-job main and isolated builds of the new module; all five exact
roots pass opaque-body/constructor/recursor auditing with standard logical
axioms only, maximum closure 8,696. Source bytes match across the two checkouts.
No forbidden dependency or new-source warning. Strengthening remains open.

## 2026-11-04 19:28:25 UTC: finite observations restore expanded head exposure

**Proved:** beta-only finite observations at the empty constant interpretation
survive every expanded primitive and compatible computation, at every finite
stage and in the full union. Opaque primitive heads have no observations to
destroy; controlled expansions preserve them by reverse beta. Operational
adequacy and an exact beta replay through the proof-shape encoding yield
literal raw Pi/sort reducts. The encoding is not an equality reflection model.

Native lambda recovery consequently reselects a Pi after arbitrary conversions,
including whole-type expansions and without purity assumptions on domains.
Existing native Pi certificates can follow arbitrary expanded type computation
and select a Pi again at the same stage. Existing native certificates for actual
Pi types recover their exact assigned sort using universe equality. A typed
whole-Pi expansion example verifies applicability beyond literal-head persistence.

**Still open:** observations do not retain domain comparisons. These results
neither prove arbitrary native coverage nor comparison completeness. Next test:
a lambda typed at a constant-headed recursive carrier may refute exact assigned
native coverage even for the full expanded union, because its native outputs
always retain a Pi observation. This would require a common-reduct interface
rather than exact coverage. Strengthening itself remains open.

Validation: 701-job build, 42 exact declaration roots audited through opaque
bodies, constructors and recursors; maximum closure 11,200. Only standard
logical axioms; no excluded strengthening/framework dependency or new warning.

## 2026-11-04 19:34:30 UTC: exact native coverage refuted; computed-carrier repair checked

**Refuted, including for the full expanded union:** every retained typed term
has native recovery at its exact assigned carrier. A native lambda always has
a Pi observation at its output. A constant/projection-headed output has none.
The recursive family R f := (R f → Prop) types its retained diagonal at R f,
so no choice of definitions or finite expanded guard depth yields exact native
recovery of that assignment. The actual extension preserves canonical Eq and
has a separately proved proposition front: this is an interface obstruction,
not a strengthening counterexample.

**Also refuted:** exact assigned native evidence survives typed beta contraction.
The typed identity cover of that diagonal has exact recovery already at stage
zero; its beta reduct has none even in the full union. Recovering substitution
covers therefore cannot establish exact-image coverage by contracting afterward.

**Concrete weaker repair proved:** with the actual recursive equation installed,
the assigned carrier computes to its unfolded Pi and the diagonal recovers that
same Pi at stage zero. The native source is unchanged. This succeeds in the
same canonical extension where exact coverage fails, without purity or a
normalization assumption. It validates common computed outputs as a candidate
interface for this obstruction, not a general coverage theorem.

**Next live obligation:** obtain native recovery together with computation of
the assigned carrier to the selected output for general retained typed terms,
and preserve dependent argument/domain certificates when Pi exposure changes
the selected binder. The new head-observation theorems provide exposure but do
not retain domain comparison. This remains distinct from, and has not been
shown to imply or be strictly smaller than, PropositionFront. Goal unchanged.

Validation: two modules, 703-job build, eight audited exact roots through
opaque bodies/constructors/recursors, maximum closure 9,943; standard
logical axioms only, no forbidden dependency or warning in the new sources.

## Joined native outputs survive context change and substitution

- Transport existing native recovery through computationally related context
  entries, retaining a joined output: **proved** for pure source syntax and a
  pure source context. The target context need not be pure. BetaLevelContext
  gives joined lifted variable-type lookups; application uses Pi exposure;
  Pi formation exposes equivalent sorts and uses imax congruence; conversion
  composes raw joins. The transported recovery uses beta alone. Thus arbitrary
  pure expanded native evidence has a beta-only native representative modulo
  BetaLevelJoin, even after context change.
- Extend this to genuinely substituted expressions: **proved**. Raw oracle
  renaming preserves beta-only native recovery without an interpreted context
  substitution premise. This proves weakening under arbitrary annotations and
  closes JoinedNativeImages under binders. Every raw image recovers a type
  joined to its substituted oracle assignment. Source recovery at any expanded
  stage or the union then substitutes to beta-only recovery with a joined
  output. Images and target contexts may contain constants/projections; only
  the original source context and source syntax must be pure. The raw image
  condition explicitly quantifies over every variable index.
- Retain usable demands and actual assigned types: **proved**. Joined-image
  substitution selects demanded sorts exactly at expanded stage zero; native
  Pi demands retain a selected Pi and inferred-mode domain comparison. Typed
  substitution retains a join and computed comparison to the actual substituted
  assigned type. A pure expanded image can itself be converted to beta-only
  joined evidence before instantiation. These results still require supplied
  native evidence; they do not assert universal native coverage.
- Test whether the image condition really improves on exact recovery:
  **strict improvement checked**. TypeFunctionExample's actual higher-order
  image has no exact assigned recovery in the old full level union, but its
  beta-only native output satisfies JoinedNativeImages. It instantiates every
  pure expanded native certificate, retaining the joined dependent output.
- Claim universal joined coverage merely by imposing purity: **refuted**,
  including for the new expansion union. The existing eta example has native
  type F f and assigned type F (fun x => f x). Their beta-normal raw shapes
  cannot be StructuralVariant. Every expanded native output of the variable is
  joined to F f by pure-context computation, so none can be joined to the
  assigned type. The actual context, source and assigned erasures are all pure,
  and an empty base context suffices in every Params environment, including
  canonical Eq. Nevertheless the full aligned checker compares the native
  output and assigned type at stage zero. This is a limitation of raw joins,
  not a counterexample to strengthening or to native type comparison.

Judgment: the proposed joined context/substitution transport is closed, but
using beta/universe joins as the universal image invariant is now decisively
excluded. General carrier transport needs eta-aware alignment, such as the
existing full checker or a stronger finite NativeCarrierAlignment certificate.
The older NativeAlignedImageSubstitution already handles a finite carrier
fragment; do not repackage that result as unrestricted coverage. A subsequent
extension must retain dependent codomain alignment and selected-domain
transport, not just a Pi head. Full strengthening remains open.

Validation: 789-job main and isolated builds, 33 exact new roots across seven
modules, maximum audited dependency closure 8,736, standard logical axioms
only. All 764 transitive local import sources match the pre-build snapshot and
isolated checkout. No sorry or forbidden strengthening/framework dependency.

## 2026-11-04 19:49:23 UTC: exact neutral readout removes the identity-wrapper stage cost

**Candidate checked and rejected:** add unrestricted erased eta contraction to
make computed-type coverage handle eta. Existing ErasedEta.target_representative_iff
shows that an apparent eta contractum can require an unavailable proof below;
ErasedEtaDomains.canonical_domain_obstruction separately shows that inferred
contraction needs domain alignment even when both endpoints are represented.
The current joined-native eta boundary also rules out beta/universe joins as a
universal assigned-type interface. No unrestricted eta primitive was added.

**Proved:** a new neutral finite-demand interpretation tracks an exact variable
instead of only a Pi/sort head. It has no literal type-head or constant rules;
the base demand can denote beta reduction to any chosen expression. Every
expanded stage and the union preserve its demands. Consequently every expanded
computation starting at bvar i has an exact raw beta path back to bvar i, and
that path survives arbitrary raw substitution without native image evidence.

**Stronger identity result:** every expanded descendant of lambda A (bvar 0)
beta-returns any supplied argument. This allows computation of the entire
identity function, including outer expansions, not only its body. Independent
argument computation therefore closes the identity-wrapper square at the
argument's unchanged stage, even when the argument has lost native recovery.
After the wrapper beta step, a computed bound-variable body instantiated by the
changed argument still beta-returns it. Both results supply ComputedJointCompare
in either mode using only the argument computation relation; the function/body
may have evolved in the full expanded union.

The proof-shape observation encoding now tags genuine constant names, separating
them from its opaque proof marker. Its new syntactic injectivity gives exact
beta reflection at arbitrary targets, including proof markers; this is not
semantic equality reflection. All earlier head-exposure consumers were rebuilt
and reaudited after this representation change.

**Next live step:** retain the marked Pi origin and its domain computations
through arbitrary interleavings of expansion-generated wrappers. Exact identity
readout closes one residual case without the false premise of beta preservation
of native recovery. It does not yet transport domain comparisons through a whole
computed checker certificate, prove general compared native coverage, or give a
strictly smaller sufficient front. The strengthening goal remains unchanged.

Validation: nine affected modules, 706-job build, 94 audited declaration and
constructor/recursor roots; maximum closure 11,200. Only standard logical
axioms, no excluded dependency, new-source warning or source hash discrepancy.

## Native eta expansion repairs the eta-assigned input

- Extend computation by eta expansion with a recovered binder: **proved safe**.
  NativeEtaExpansion requires native Pi recovery of its short source and a
  DomainSort witness for that recovered domain. Recovered-Pi descent produces
  an actual lower domain; DomainSort.descend fixes its universe and therefore
  the retained/proof-marker fresh argument. The actual short source already
  exists below, so its ordinary eta expansion gives the required lower target.
  This avoids the hidden-proof-dependency problem of reconstructing an erased
  eta contractum. Exact renaming and exact native-image substitution preserve
  the complete expansion recipe.
- Close finite recovered stages over this additional guard: **proved**.
  ErasedEtaExpansionStage contains every previous expansion stage at the same
  index and retains singleton, Eq-prefix and identity guards. Every layer has
  arbitrary-block source-typed descent and exact renaming. The union descends;
  native eta guards over the union have finite bounds. Computation, recovery,
  both computed checking views, recovered comparison and full aligned comparison
  transport with bound n+k for exact native images at stage k. Actual typed
  instantiation wrappers preserve exact dependent erasures.
- Repair the checked eta-coverage failure concretely: **proved**. In the
  existing EtaRecoveryJoinBoundary context, native F f computes to the assigned
  F (fun x => f x) by one native eta expansion of f. The variable at F f now
  recovers its exact assigned type at stage one, in every well-formed base.
  In the same pure context, the previous controlled-beta union still has no
  native output beta/universe-joined to that assigned type. The repaired image
  instantiates arbitrary full aligned dependent comparisons and computations,
  with one additional stage. This is a strict repair of that obstruction.
- Infer universal exact coverage from increasingly rich primitives:
  **already excluded by a general earlier theorem**, now explicitly specialized
  to the eta-expanded union. scoped_identity_captured_not_recovered applies to
  every source-typed descending relation: a lifted identity can be assigned a
  beta-expanded Pi retaining a fresh proposition, but its exact raw annotation
  has no lower preimage. EtaNativeLimits preserves the actual assigned typing
  and proves failure in the new union. The same identity and assigned type
  have base-stage native common-reduct evidence. Do not attempt to defeat this
  capture theorem by adding more descent-preserving computation rules.

Judgment: controlled native eta expansion is an available constructive tool
for eta-aware type alignment and dependent application. It repairs the eta
example while the capture example still requires common-reduct selection.
The previous pure beta/universe confluence invariant is not claimed for this
larger system: eta expansion is not generally a BetaLevelJoin. The live work
is transport of native common-reduct or full aligned evidence in the eta-aware
system, including dependent selected domains and codomains. General confluence,
coverage modulo comparison, and checker completeness remain open. This is not
a smaller sufficient irreducible obligation or a GOAL.md deliverable.

Validation: main and isolated 737-job builds; 36 exact public roots, including
two abbreviations, pass opaque-body/constructor/recursor auditing; maximum
closure 11,133, standard logical axioms only. All 712 transitive local import
sources match their pre-build hashes and isolated counterparts. No forbidden
strengthening/framework dependency or new-source warning. weakN_iff remains open.


## Native eta application squares and retained image instantiation (2026-11-04)

- Apply native eta expansion at an actual argument, allowing the recovered Pi
  domain to differ from the assigned domain: **proved**. Forward native replay
  reconstructs the recovered domain; Pi injectivity types the original argument
  there. The erased fresh eta slot instantiates to the actual argument erasure,
  also for proof domains. The long raw application beta-contracts to the short
  one. Argument computation preserves this exact beta square by typed replay.
- Demand native recovery of proof arguments for substitution: **unnecessary**.
  The image invariant only covers retained variables. Typed substitution
  reflects proofness, so the fresh proof variable is excluded. Generic
  Images.inst_retained requires recovery only under a non-proof hypothesis;
  Images.inst_proof discharges that requirement vacuously. No native recovery
  of `.proof` is constructed or assumed.
- Compute inside eta bodies before application: **proved with explicit retained
  image evidence**. Eta-stage body and argument computations meet at the exact
  substituted outputs, at max(n+k,m), with no native evidence for the computed
  argument. The union version collects finite bounds. Full aligned comparison
  also instantiates two independently chosen proofs of the same domain at the
  original stage, without comparing the proofs or recovering their types.

Judgment: these local squares handle native eta expansion in function position
and dependent proof substitution. They do not establish eta-aware confluence,
Pi-domain persistence through arbitrary compatible paths, non-proof native
coverage, or comparison completeness. The non-proof body square still requires
exact native recovery at the selected domain; the known captured-assignment
obstruction prohibits treating this premise as universally available. General
common-reduct/full-alignment transport remains live. This is intermediate work,
not a GOAL.md deliverable; weakN_iff remains open.

Validation: main and isolated 711-job targeted builds; 13 exact public roots
pass type/opaque-body/constructor/recursor audits, maximum closure 11,114,
standard logical axioms only. All 686 transitive local source hashes and isolated
copies agree. No new-source warnings or forbidden strengthening dependencies.

## 2026-11-04 20:06:01 UTC: retained Pi components and exact backward context transport

**Proved:** PiReadout records a raw beta path to Pi X Y together with computation
from the assigned A to X and from B to Y under the original A binder. Raw beta
confluence preserves it through further beta steps. Constant expansion, every
outer-root expanded primitive, arbitrary root/beta sequences, and whole computed
identity functions or contracted identity bodies preserve the component paths.
Existing native evidence at the assigned Pi can recover the exposed Pi using
just these paths, without paying for the surrounding wrapper guard depths.

**Dependent consumer proved:** native readout reifies actual D,C and retains
both component computation paths. Type uniqueness aligns the selected binder;
erasure invariance moves C back to the original A scope. This gives inferred
comparisons for both components, including the dependent codomain. Application
then recovers C.inst x and a path from the assigned B.inst x. Ordinary substitutive
component primitives admit every typed argument; expanded guarded components
use native recovery at the original A only, with the existing additive bound.
No native recovery at the newly selected D is required.

**New context step proved:** if A computes to D, the variable in context A can
recover the lookup type used in context D by the weakened domain path. Older
lookups agree. These exact native identity images transport computation, native
recovery, computed comparison and the full aligned checker backward from D::Γ
to A::Γ, preserving raw outputs and checking modes, at stage n+k. This uses
actual domain equality and requires no purity or finite-family restriction.
Full-union computation transport is also proved. The direction matters: this
does not prove forward native recovery through a reduced binder.

**Continuation proved:** a second codomain computation under the newly selected
domain can now be pulled back and appended to the original codomain path. Both
component histories survive two phases and any subsequent outer-root/beta path.
This closes the literal-Pi continuation case of the proposed origin invariant.

**Remaining live obligation:** cover arbitrary compatible expanded computation
from an original Pi with such component histories. Root steps, beta steps,
computed identity wrappers and successive literal-Pi component phases are now
handled. General application-shaped intermediate terms still require tracking
the originating payload through computed constant-function wrappers. The local
constant-wrapper certificate-descent square is available, but no full mutual
head-normalization/origin proof has been established. These are results for the
controlled beta-expansion stages, not a claim about arbitrary eta-expanded stages.
No general coverage theorem or smaller sufficient strengthening front is claimed.

Validation: five modules, 722-job build, 30 exact roots with opaque-body,
constructor and recursor audit; maximum closure 11,222; standard logical
axioms only, no forbidden dependency or warning in the new sources. Goal active.


## Compute eta bodies before substitution using the existing expansion (2026-11-04)

- Add an enclosing-application primitive to recover an argument at the domain
  selected by its function: **unnecessary for the local eta-body path**.
  Existing native eta expansion already exposes that binder at the enclosing
  application. Compute the body under it, independently compute the argument,
  then beta-contract. No transport of the body certificate by substitution and
  no native argument recovery are needed. The finite bound is
  max(k+1,max(n,m)); a direct union theorem needs no chosen image bound. The
  actual type-valued application starts at its exact erasure even when the
  recovered domain differs from its assigned one.

Judgment: this removes the image premise from the eta-specific path at the
cost of eta expansion, whereas general body-substitution transport still needs
retained native images. It is a composition of existing computation rules,
not a new primitive or a confluence theorem. In particular it starts at the
original application, not at an independently chosen beta reduct. Joining
that reduct with the computed eta body is still unresolved. Do not mistake
this construction for general beta stability or a smaller sufficient front.

Validation: main and isolated 712-job builds; three exact public roots audited
through opaque bodies, constructors and recursor rules, maximum closure 8,247;
standard axioms only, no forbidden dependencies. All 687 transitive source
hashes match isolated copies. No new-source warnings; weakN_iff remains open.


## 2026-11-04 20:16:56 UTC — Lambda exposure before body-origin factorization

**Verdict: proved operational exposure, origin factorization remains open.**
An arbitrary expanded computation starting at a literal lambda beta-exposes a
lambda, even with unrestricted annotations and a divergent body. The finite
observer gives lambda heads a base demand independent of body observations;
substitution, beta preservation, and operational realization are proved. Opaque
primitive roots cannot consume this demand, and both controlled expansion roots
preserve it. Finite stages and the full union are covered, without source typing
or native argument recovery. A typed retained source additionally reconstructs
an actual lambda at its original type and unchanged computation stage.

**Constant-body improvement: proved at the unchanged stage.** Any well-formed
unused binder can be discharged from a computation of a lifted typed payload.
The exact body output is a lift of a lower computed term. This works directly
under a changed annotation: no comparison or computation back to the wrapper's
original binder is needed. Arbitrary final annotations and arguments beta-return
the lower term. Further beta paths have a common residual with its lower path.

**Next live target: literal-lambda endpoint factorization.** Exposure reduces
the whole-function problem to a computation from an original literal lambda to
a selected literal lambda. What is still missing is factorization into domain
and body computation (possibly after further beta), with the body path in its
original scope. For a constant wrapper, that body history would feed the exact
unused-binder readout. Typed equality of the two lambdas does not provide this
operational history. No arbitrary PiReadout coverage, sufficient smaller front,
or proof of strengthening follows yet. The original sorry remains.

Validation: three modules, 722-job build, 41 exact dependency roots including
all new observation constructors and recursors; maximum closure 11,140;
only propext, Classical.choice and Quot.sound, with no excluded dependency or
warning in these sources. Goal active; no PR extraction.


## Exact eta substitution fails; joined and readout repairs succeed (2026-11-04)

- Transport an arbitrary typed eta-body computation to its exact substituted
  endpoint, allowing any target guard depth: **refuted**. NativeEtaBetaPeak
  uses the existing captured Pi assignment for the closed identity. A variable
  of that declared type eta-expands at stage one. After substituting the
  identity, the eta endpoint retains the fresh proposition in its annotation.
  No source-typed descending computation from the closed identity reaches that
  exact raw endpoint, even over the whole eta union. The witness includes
  actual body/argument typings and a well-formed source context. This is now
  a computation counterexample, beyond failure of exact native recovery alone.
- Interpret that failure as nonconfluence: **excluded for this witness**.
  A typed identity-wrapper application beta-reduces to the ordinary identity
  or eta-expands its bound variable and then beta-reduces to the captured eta
  endpoint. The latter beta-cleans its annotation and body back to the ordinary
  identity. Exact forward residual transport fails; a common reduct exists.
- Repair an assigned eta annotation using joined native evidence: **proved**.
  BetaLevelJoin of a native output with the assigned Pi exposes a native Pi
  and a domain join. Actual uniqueness fixes its domain sort. The two eta
  expansions have a beta/universe common reduct. Eta stage k+1 realizes the
  short branch; the assigned long branch uses only beta/universe conversion.
  Exact recovery of the assigned Pi, purity, and native argument images are
  not premises of this local repair.
- Substitute joined native images before eta repair: **proved for the existing
  pure controlled-beta source recovery**. The prior joined-image transport
  gives beta-only native evidence after substitution; the new repair then
  gives a common target at eta stage one. Target contexts and images need not
  be pure. Source purity and the joined-image evidence remain explicit; this
  is not transport of arbitrary eta-stage recovery.
- Use retained Pi components instead of raw beta/universe joins: **proved**.
  PiReadout selects an actual native Pi and retains a computation from the
  assigned domain to its selected domain. That path moves the assigned eta
  expansion to the native eta target directly. This works for arbitrary
  guarded component computation and impure sources, at max(k+1,n), and over
  the full eta union. Recovery and component relations may differ.

Judgment: exact endpoint substitution is definitively the wrong general
closure law. Both positive repairs permit the assigned eta endpoint to change.
Pi readout now has a concrete eta consumer as well as its application consumer.
Arbitrary readout coverage, full aligned-image transport and beta/eta confluence
remain open; none of these results is a smaller sufficient irreducible front
or a strengthening counterexample. Original weakN_iff remains sorry.

Validation: four modules, 416 Lean lines and 21 new public declarations.
Main and isolated 732-job builds; 104 exact roots audited including changed
transitive dependencies, maximum closure 11,092, standard logical axioms only.
All 707 transitive local source hashes and isolated copies agree. No forbidden
dependency or new-source warning. Goal stays active.


## 2026-11-04 20:32:56 UTC — Full dependent Pi origin by marked finite observations

**Verdict: full PiReadout coverage proved for the controlled expanded union.**
The application-shaped gap left by dff97a88 and 35559229 is closed. Rather than
first factor arbitrary lambda computations, mark each Pi payload with its
actual lower component representatives and both computation histories. The
observer's depth counts only temporary control binders. Its payload rule lifts
the entire marked Pi past that prefix. FixedTail substitutions may change all
control variables but fix original variables, so beta contraction transports
the exact payload certificate. Finite realization returns a raw beta path to
one marked Pi; no normalization of components is assumed.

**Typed computation preservation proved.** A root-beta induction principle
exposes individual contractions while retaining the child computation proofs.
All expanded roots preserve the marked demand. Application and lambda control
frames use typed replay and the observation substitution law. At a literal Pi,
certificate descent removes the temporary prefix independently from each child
path. The retained domain path and actual equality pull subsequent codomain
computation back into the initial binder. This is the only payload-specific
closure law, and it is proved for the concrete origin invariant.

**Consumers proved.** Every expanded union path from a typed Pi yields its full
PiReadout. Finite input stages yield a finite later component bound. An assigned
Pi path to an existing native output now supplies both inferred component
comparisons automatically. Native application obtains an exact selected-result
certificate plus an expanded path from its assigned result carrier, using native
recovery only at the original argument type. Recovery's relation/stage remains
independent of the component histories. No purity restriction or assumed Pi
readout remains in these consumers.

**Remaining main-goal gap.** Existence of an expanded assigned-Pi path to an
arbitrary native output is not established by this theorem; neither is general
native coverage or checker completeness for declarative equality. Eta-containing
conversions remain outside this controlled-beta observation proof. The general
lambda endpoint factorization target was bypassed for Pi coverage, not proved.
Do not claim a sufficient smaller strengthening front from this result alone.
The next task is to use the full readout in native carrier alignment and assess
the remaining type-conversion/eta cases against the known coverage boundaries.

Validation: four modules, 731-job build, 41 exact roots including every new
observer constructor and recursor, maximum closure 11,383; standard axioms
only and no forbidden dependency. All 706 local transitive source hashes were
unchanged through build/audit. No warnings in the new files. Goal active; no PRs.


## Retain eta certificates and Pi histories below wrapper binders (2026-11-04)

- Extend ordinary eta-stage descent to retain the exact lower certificate:
  **proved at the same stage**. Native Pi recovery descends together with its
  domain/codomain erasures and its native certificate. The lower domain-sort
  witness then reconstructs a genuine native eta guard. All finite eta stages
  and their union retain primitive and compatible computation certificates.
  Compute and native recovery at prescribed lifted outputs reflect through
  arbitrary inserted binder blocks without increasing the stage.
- Descend full PiReadout histories rather than only their selected head:
  **proved generically from primitive certificate descent**. The domain and
  codomain paths descend in their original scopes. Once both selected
  components are known lifts, raw beta retraction gives the lower readout.
  The selected raw endpoint need not have a supplied lower typing. Exact
  renaming gives the converse, hence same-stage and union readout lift iff
  theorems for eta-aware computation.
- Remove constant-wrapper control binders after arbitrary eta-aware body
  computation: **proved**. A generic certificate-descent theorem reads the
  output as an exact lift of a lower computed term. Every final annotation
  and argument beta-returns that term. Raw beta confluence joins any further
  beta continuation with the lower path. Eta stages retain the original
  finite bound; the union version needs no uniform bound or native image.
- Use unrestricted raw observations to preserve eta-aware Pi origins:
  **not justified**. A raw valuation can assign a Pi/sort demand to a function
  variable; eta expansion hides that demand. Proof-domain eta slots also
  require typed argument information. A live next approach is a typed control
  observation that constrains the demands of temporary wrapper variables.
  Closed simple control types built from sorts and arrows may supply such an
  invariant, or fulfilled typed demands may suffice. No such observer or
  eta-aware head-persistence theorem is claimed here.

Judgment: these results supply exact binder removal for eta-aware origin
tracking and close its unused-body beta residual. The newly committed full
controlled-beta Pi origin theorem c43e9bb1 does not yet cover eta primitives;
its typed preservation step needs an additional invariant for those roots.
General native coverage, comparison completeness and strengthening remain
open. This is not a sufficient smaller front or a completed GOAL.md result.

Validation: three modules, 300 Lean lines, 14 new public roots. Main and
isolated 727-job builds; 49 roots audited including changed dependencies,
maximum closure 11,114, standard axioms only. All 702 transitive local source
hashes match isolated copies; no forbidden dependency or new-source warning.


## 2026-11-04 20:41:41 UTC — Full lambda origins and whole-function beta exchange

**Verdict: the general controlled-expansion lambda-origin gap is now closed.**
Extend the marked finite-observation method to lambda payloads. A payload lambda
satisfies the base demand, while a control lambda introduced by expansion has a
functional demand on its body. Beta inversion selects only the functional case;
compatible lambda computation either updates a payload's component histories or
transports a control-body observation. FixedTail substitution and root-beta
induction are reused from the Pi-origin development. Actual payloads may have
arbitrary body types, with no normalization or purity assumption.

**Proved:** full lambda readout for every retained typed lambda under arbitrary
controlled expanded computation; a finite later component bound; and literal
lambda endpoint factorization into original-scope component paths meeting beta
residuals of the final components. This is the factorization previously bypassed
for Pi coverage, rather than a mere lambda-head exposure result.

**Beta consumers proved:** the body/argument square now needs native evidence
only for the original non-proof argument. Full lambda readout supplies the body
history automatically after arbitrary whole-function computation. Proof arguments
need no native certificate; computed arguments need no recovery. An arbitrarily
computed constant function beta-returns the same lower computed payload for every
raw argument, without any typing or recovery assumption on that argument. This
closes the whole constant-function wrapper case originally left open.

**Eta connection proved:** full Pi readout discharges the readout hypothesis in
the native eta-annotation repair when there is a controlled expanded assigned-type
path. The short function uses the eta union; its assigned eta expansion reaches
the same target using only the controlled beta-expansion union. A finite-stage
version exposes the max(k+1,later) bound. No purity or beta/universe join is assumed.

**Remaining:** neither all native outputs nor all original non-proof arguments
have exact assigned-type recovery; known boundaries prohibit asserting that
coverage. General beta strip therefore still requires residual repair for
arguments with only joined/common native carriers. The new origin invariants
cover controlled beta expansion, not arbitrary native eta stages. General guarded
confluence/checker completeness and the original strengthening goal remain open;
no sufficient strictly smaller front is claimed.

Validation: five modules, 740 jobs, 44 exact roots (opaque bodies, constructors,
recursors), maximum closure 11,402; standard axioms only, no excluded
dependencies or new-source warnings. All 715 local imported sources stayed
unchanged through validation. Goal active; no PR extraction.


## 2026-11-04 20:52:09 UTC — Common carriers do not repair exact expansion residuals

**Verdict: replacing exact native argument recovery by a common native carrier
while retaining the exact directed output is refuted already by plain controlled
identity expansion.** The witness has an actually typed argument and body. Its
argument has beta-only native recovery, and its assigned type beta-reduces to
that same recovered carrier. Nevertheless, expanding the bound variable at its
captured declaration and then substituting retains a fresh proposition inside
the annotation. The original instantiated term is a lifted closed identity.
Every source-typed descending target relation forbids a path to that exact
captured output, including the entire controlled expansion union under canonical
Eq. The counterexample does not use native eta expansion or recursive definitions.
Its failed endpoint beta-contracts to the instantiated source, so it does not
refute confluence or strengthening.

**Positive repair:** universe conversion, constant expansion and native identity
expansion have raw beta/universe joins regardless of source syntax or context
purity. Their entire compatible closure substitutes up to a common reduct, with
no native image premise and no restrictions on how the source identity guards
were recovered. The same method closes whole-function head-beta squares for
these paths against arbitrary controlled expanded argument computation. It
allows impure bodies and annotations, unlike the earlier pure-source joined
native transport result. Both residuals are explicit computations; the function
branch requires only beta/universe steps.

**Next:** exact recovery remains a valid sufficient hypothesis for exact
transport, but common-carrier transport must allow common reducts. Transparent
expansion steps no longer need image recovery in that weaker conclusion. General
paths involving singleton/Eq-prefix guards (and ordinary non-beta primitive
computation) still need residual transport and composition with beta cleanup.
The original strengthening theorem and the sufficient-smaller-obligation
alternative remain unproved. Goal active; no PR extraction.

Validation: two modules, 731 jobs, 16 audited public roots, maximum closure
11,099; standard axioms only, no excluded dependencies or new-source
warnings. All 706 local imported sources stayed unchanged during validation.


## Closed control types preserve Pi origins through native eta (2026-11-04)

- Type the marked control frames by closed universes and nondependent arrows:
  **proved and sufficient for all eta-stage roots**. Constant wrappers add
  the fixed Type domain; native identity wrappers reuse the payload's assigned
  control type. Their displayed annotations may differ: uniqueness supplies
  the conversion. Every control type has a positive canonical universe.
- Exclude the bad untyped eta valuation without restricting payload purity:
  **proved**. A sort-assigned source cannot recover a Pi type. At a control
  arrow, every selected eta domain has positive universe and the fresh
  argument is retained. Finite demands follow the assigned control type, so
  function variables cannot receive Pi-head demands.
- Preserve these observations under ordinary substitution and compatible
  computation: **proved**. Valuations retain assigned control types. Beta
  uses ordinary typed argument substitution, without native argument images.
  Identity context substitution transports observations across changed lambda
  annotations; exact oracle preservation is unnecessary for that transport.
- Close the marked Pi component condition for eta-aware computation:
  **proved**. Same-stage certificate descent removes temporary prefixes;
  eta-stage native identity images pull codomain histories backward across
  previously computed domains. Full eta-union PiReadout now holds for every
  typed Pi source, including impure and non-normalizing component paths.
  Finite input stages have finite later bounds for the component histories.
- Repair assigned eta against a native output reached by an eta-aware
  assigned-Pi computation: **proved**, with no separate component-readout
  premise. This extends the earlier controlled-beta type-path square. It
  still assumes the assigned-Pi-to-native computation itself; this is not
  general assigned-type coverage, confluence, or equality completeness.

Judgment: the previously live typed-observer idea closes the entire eta-aware
Pi-origin gap, not merely another primitive case. General native coverage and
residual joins for guarded computation remain live obligations. No proof or
counterexample of strengthening, or strictly smaller sufficient irreducible
front, is established here. GOAL.md remains active.

Validation: six new modules, 896 Lean lines, 61 public roots. Main and isolated
builds pass 738 jobs. All 87 selected roots, including two newly synchronized
import modules, pass structural dependency audit; maximum closure 11,464,
standard axioms only. All 713 local imported sources are hash-stable and match
the isolated checkout. No new-source warnings or forbidden dependencies.


## 2026-11-04 21:06:43 UTC — Common native carriers through the first recovered guard stage

**Verdict: common-carrier substitution is now constructive for the entire first
recovered singleton/Eq-prefix stage, with no purity or exact assigned-image
recovery premise.** This is the existing `ErasedCarrierRecoveredStage D 1`,
whose guards compute in the ordinary core. It is not the expanded stage one
that also admits universe conversion and native identity expansion. The exact
identity-expansion residual refutation from the previous turn therefore remains
consistent with this result.

The main bridge is typed core joinability. Every contextual path whose primitive
roots have core common reducts retains a core common reduct; source replay gives
the typed middle terms required by core confluence. Thus arbitrary ordinary-core
computation mixed with constant/native identity expansion is core-joinable,
without purity or normalization. Source native guards may use the entire
controlled expansion union. This is a concrete confluence result for that mixed
fragment, not an assumption about the whole guarded union.

Native recovery over mixed paths can then be replaced by ordinary-core recovery
whose output is a forward core reduct of the old selected output. Common native
images transport this recovery on arbitrary typed sources. Independently
transported recoveries in a recovered-family comparison are aligned by typed
core confluence, and their full dependent carrier guard follows the forward
carrier path. This closes the complete recovered-family checker transport and
discharges both general singleton and specialized Eq-prefix guard substitution
under their generated dependent telescopes. All finite first-stage compatible
paths substitute exactly. A whole first-stage body path commutes with arbitrary
expanded argument computation; only the original argument needs a mixed native
output core-joined to its assigned type.

The concrete native/guard results use the quotient-repaired ordinary core, its
`QuotRegistered` hypothesis, and concrete-pattern correctness, as exposed in
their statements. Generic mixed-path join results accept any sound core with
proved typed-source confluence. Neither result asserts these conditions cover
all environments of GOAL.md or that all terms supply common native images.

**Remaining:** explicit universe-conversion roots in mixed core paths; recovered
guards whose computations use higher singleton stages; general common-reduct
composition when guarded steps and identity expansion interleave; universal
image coverage; and the strengthening conclusion. General core-family joins
transport through mixed endpoint computation, but arbitrary recursively checked
families are not equated with core joins. No sufficient smaller front is claimed.

Validation: five modules, 733 jobs, 35 public roots, maximum closure
11,720; standard axioms only and all exclusions clean. All 708 local imported
source hashes remained stable; no new-source warnings. Goal active; no PR extraction.


## Native eta residuals at lambda endpoints (2026-11-04)

- Derive a type path from native recovery of a literal lambda instead of
  assuming assigned-type coverage: **proved**. Recovery first selects a body
  type under the displayed binder, then computes from the corresponding Pi.
  Full eta-aware Pi readout joins the original domain to every selected native
  Pi domain: the original domain computes in the eta union, and the selected
  domain needs only beta cleanup.
- Join native eta of a retained actual lambda with the original lambda:
  **proved without an assigned-type path premise**. The original side computes
  only its annotation; the eta side beta-reduces to the same annotation and
  exactly the original body. Actual uniqueness classifies the eta argument,
  including a proof marker when the selected domain is a proposition. Finite
  guards give a finite later annotation bound.
- Commute native eta with arbitrary function computation ending in a lambda:
  **the entire body residual is proved generically**. Run the function path
  under the selected domain by exact weakening, replay its lambda endpoint,
  and beta restore that endpoint's exact body. The selected annotation stays
  fixed. Neither native recovery of the computed function nor native images
  for its fresh argument are required. In finite eta stages, the long residual
  retains exactly the function path's bound, independently of the guard depth.
  A join of the final and selected annotations then joins the whole peak.
  Construction of that annotation join for arbitrary paths remains open.
- Require a common type reduct instead of an assigned-Pi-to-literal-native
  path for general eta repair: **proved**. Follow the native branch by native
  conversion, then use full Pi readout on the assigned branch. Both branches
  may use eta-aware computation, with independent finite bounds. This changes
  the remaining coverage target to existence of a common reduct; it does not
  prove that such reducts always exist.

Judgment: literal-lambda native eta is now an unconditional checked residual
case. General function/eta residuals isolate annotation joining rather than
body transport or proof-marker substitution. These are concrete steps toward
confluence, not a sufficient strictly smaller strengthening front. General
native coverage, annotation joins, equality completeness, and GOAL.md remain
open. The previous turn was verified progress; this turn adds new proofs.

Validation: three modules, 285 Lean lines, 11 public roots; main and isolated
742-job builds. Structural audit maximum closure 11,470, standard axioms only,
all exclusions clean. All 717 local imported sources stayed unchanged and
match isolated copies; no new-source warnings.

### 2026-11-04 21:18:19 UTC — Postpone universes, then join mixed function paths

**Verdict: proved for the universe-extended ordinary core and its controlled
beta expansions; singleton roots in the function path remain open.** The
previous common-core argument omitted explicit universe conversion. Every
source-typed finite level-core computation now factors into ordinary core
computation followed by structural universe variation. The transitive case
replays both intermediate terms and uses the already proved concrete structural
simulation; it does not assume normalization or guarded-stage confluence.
Ordinary typed confluence therefore extends to the level core.

A concrete instance uses precisely actual stored definitions. Definition
patterns replay as stored unfolding; iota patterns have disjoint heads. The
separated confluence theorem then gives ordinary typed confluence in this exact
collection, and stored-body universe compatibility supplies the new extension.
This avoids needing a universe-compatibility theorem for the extra selected
structure and proposition-source quotient equations. It does not prove such a
theorem for that larger collection or replace its native-recovery coverage.

Ordinary computation, explicit universe conversion, constant expansion, and
native identity expansion can now interleave arbitrarily and still have exact
level-core common reducts. Native guards may use any descending relation,
including the entire expanded union. Whole-path actual substitution needs
only erasure agreement, not native images, when the output is requested up to
common reduct. Common level-core guards also survive independent mixed
endpoint paths. These statements concern core joins, not arbitrary recursive
carrier comparisons.

For a retained lambda, its common reduct is again a lambda with separate
level-core histories of the original annotation and body. The latter substitutes
freely. Consequently a whole mixed function path and arbitrary full-expanded
argument path join the original beta contractum **without native certificates
for either original or computed argument**. This extends the transparent
function square to ordinary definitions, iota, and projection computation
interleaved with universe changes and controlled expansion. The function path
still excludes singleton/Eq-prefix roots; the argument path can include them.

Remaining: higher guarded function computations and recursive carrier-family
forward stability; general native-image coverage; universe compatibility for
the augmented declaration collection if that native route is used; and the
strengthening conclusion. No new strictly smaller sufficient front is claimed.

Validation: four modules, 730 jobs, 22 public roots, maximum dependency closure
11,511; standard axioms only, all forbidden dependencies absent, 705 local
import-source hashes unchanged, and no new-source warnings. Goal active; no PR
extraction.


## Joined native guards transport eta; beta need not preserve core recovery (2026-11-04)

- Replace exact transport of an eta guard's selected Pi by joined native
  transport: **proved for arbitrary source guard relations with descent**.
  Reconstruct its actual Pi and domain sort, substitute them ordinarily,
  then use full eta-aware Pi readout at a common target type. Both residuals
  start at the exact substituted short and long raw shapes. No source/target
  purity, exact assigned-type recovery, or native argument image is imposed
  by this generic eta step once the joined guard image is supplied.
- Obtain that joined guard image for mixed ordinary-core and controlled-beta
  native recovery on arbitrary typed sources: **proved using the committed
  mixed-core recovery transport**. Common native images suffice, with no pure
  source/context restriction. Guards can interleave ordinary reductions,
  constant expansion and native identity expansion. The recovery relation
  inside identity guards need only descend. The quotient-repaired core's
  QuotRegistered and concrete-pattern hypotheses remain explicit.
- Apply the result to a beta cut: **proved**. An original argument whose
  assigned carrier computes to a core native output transports a complete
  native eta body primitive to a common eta-union reduct. The two starting
  points are the exact erased instantiated short body and expanded body.
- Preserve native recovery modulo beta/universe joins through arbitrary
  ordinary beta reduction, to recover computed arguments automatically:
  **refuted, not used**. Every retained typed p:A has an identity wrapper
  (lambda x:A. x) p with exact native A, independently of p's native evidence.
  In the pure eta-assigned neutral example, one beta step returns p, which has
  no native output beta/universe-joined to A even in the entire old expansion
  union. Thus source reduction can lose joined evidence, not just exact
  syntax. This is not a negative result about eta-aware joins, which repair
  the underlying eta-assigned example.

Judgment: eta primitive substitution now consumes common guard reducts and is
instantiated for arbitrary typed mixed-core guards. The new beta boundary rules
out an unsound source-reduction shortcut for extending it. Higher eta/singleton
guard transport and universal eta-aware common native coverage remain live.
No strengthening proof, canonical-Eq counterexample or sufficient strictly
smaller front is claimed; GOAL.md remains active.

Validation: three new modules, 184 Lean lines, six public roots. Main and
isolated 762-job builds pass; 54 roots audited including eight synchronized
import modules, maximum closure 12,060. All 737 local imported sources remain
hash-stable and match isolated copies. Standard axioms only; exclusions clean;
no new-source warnings. The audit parser now excludes nested comments before
collecting declaration roots, after a documentation line was misidentified as
a structure declaration; the corrected complete audit passes.

### 2026-11-04 21:30:39 UTC — Ordinary output residuals inside universe-native recovery

**Verdict: proved; full common-image guard substitution now includes the first
universe-extended recovered singleton stage.** Trying to replace every old core
path directly with a level-core path loses literal sort and projection-universe
inversion. Instead factor the path from the assigned type into an ordinary
path followed by structural universe variation. Replay supplies the ordinary
intermediate's actual typing, so reverse the structural variation with a
proved level path and convert the native certificate to that intermediate.
The new native certificate uses the level core, but its output is an ordinary
reduct of the old selected output. This stronger asymmetric invariant closes
all native recovery constructors, including dependent applications and projections.

The same construction gives asymmetric confluence: two typed level-core paths
have a common reduct with an ordinary residual on the chosen right branch.
This is enough for the simultaneous recursive checker induction. Its carrier
conversion case joins the requested ordinary carrier reduct with the original
level computation, then recurses along the ordinary right residual. Native
applications choose new ordinary-reduced domains; full carrier guards follow
them. Context oracle reduction is derived from the new joined-image identity
substitution instead of reproving native recovery under context changes.

Consequences now checked: mixed ordinary/universe/controlled-expansion recovery
collapses to level-native recovery with an ordinary output residual; arbitrary
simultaneous images may use mixed native certificates joined to their assigned
carriers; all computed and recovered comparison/carrier constructors substitute;
and general singleton plus specialized Eq-prefix roots transport through their
whole generated telescopes. Arbitrary finite `ErasedLevelRecoveredStage D 1`
paths preserve exact substituted outputs. An entire such body path combines
with arbitrary expanded argument computation. Only the original argument needs
a mixed native output joined to its assigned carrier; its computed endpoint
needs no native certificate.

The concrete instance uses actual stored definitions. Soundness, rigidity,
universe compatibility and ordinary confluence are all discharged, with no
quotient-registration requirement. Generic statements permit any collection
satisfying these proved interfaces; no compatibility theorem for the earlier
augmented quotient/selected-structure collection is silently assumed.

Remaining: higher singleton-stage carrier computation, endpoint forward
stability of arbitrary recursive guards, whole guarded/expanded confluence,
and universal native/common-carrier coverage. The new stage is the existing
level-recovered stage one, not expanded stage one (whose native identity roots
still have the exact-substitution obstruction). No strengthening proof,
canonical-Eq counterexample, or strictly smaller sufficient front is claimed.

Validation: eight modules, 737 jobs, 49 public roots including context-record
constructor, recursors and projections, maximum closure 11,580; standard
axioms only, exclusions clean, no new-module warnings. All 712 local imported-source
hashes checked unchanged. Goal remains active; no PR extraction.


## Nested literal-lambda eta is core-joinable at every finite depth (2026-11-04)

- Strengthen the literal-lambda eta residual to a common ordinary/level-core
  reduct: **proved generically**. If native-guard computations are core-joinable
  and the core cannot reduce a Pi root, lambda-recovery inversion supplies an
  actual typed initial Pi path. Inverting both common-reduct branches yields
  a core join of the displayed and selected domains. Typed eta beta restores
  exactly the original body, including proof-marker argument cases.
- Close repeated native eta guards by induction on finite guard depth:
  **proved for literal-lambda sources**. Stage zero mixes ordinary primitives,
  universe changes and controlled constant/identity expansions. Each next
  stage allows native eta on a literal lambda with guards using the complete
  preceding stage. Every stage and their union have source-typed descent,
  core joinability, confluence and ordinary substitution up to a core join.
  No native evidence for substitution images is needed. Base identity guards
  may independently use the full descending eta union. The new stages embed
  into the existing full eta union, rather than adding unsound computation.
- Commute whole nested-lambda-eta function paths with head beta:
  **proved with arbitrary full-eta argument computation**. Core lambda readout
  gives separate original-domain/body histories; the latter substitutes freely.
  Neither original nor computed arguments require native recovery. The
  computed-application branch uses only level-core computation. Stored
  definitions discharge compatibility/confluence premises, and an explicit
  actual-environment theorem needs only WF and canonical Eq for confluence.
- Extend that same core-join invariant to neutral eta roots:
  **refuted structurally**. A variable remains fixed under level-core
  computation, while its native eta output retains a lambda head. Their
  common level-core reduct is impossible. Neutral eta therefore needs a
  different target invariant; it cannot be added to the stage induction as
  one more core-joinable primitive.

Judgment: this closes whole paths and arbitrarily nested guard depth for the
literal-lambda eta fragment, removing its native-image hypothesis rather than
merely checking one root. The checked variable boundary identifies why it does
not prove full eta confluence. Neutral eta, singleton/Eq-prefix function paths,
general common native coverage and strengthening remain open. No sufficient
strictly smaller irreducible front is established; GOAL.md remains active.

Validation: three new modules, 411 Lean lines, 21 public roots. Both explicit
builds pass 759 jobs. Structural audit covers 43 roots including four newly
synchronized dependency modules; maximum closure 11,569, standard axioms only,
all exclusions clean. All 734 local imported sources are hash-stable and match
the isolated checkout. No new-module warnings.

### 2026-11-04 21:35:21 UTC — Full-expanded coverage boundary and universe-native eta transport

**Verdict: universal non-eta common-native coverage is refuted, even with the
entire expanded union on both join branches. Eta-aware coverage remains live.**
The earlier boundary excluded beta/universe joins. Purity of native recovery
now promotes it to a counterexample for exact common reducts using every
controlled-beta singleton stage. The typed source, assigned type and context
are pure; every recovered native type stays pure; both expanded join paths
would imply the forbidden beta/universe join. This works for every declaration
collection without additional environment registrations, so it also applies
under canonical Eq and to actual stored definitions.

The new level-core common-image invariant is therefore not universally
inhabited: an explicit well-typed single substitution with erasure agreement
fails `LevelCoreNative.Images`. Increasing non-eta singleton depth cannot fix
that example. Likewise, an exact-native typed identity wrapper beta-reduces to
a value with no native type common-joined to its assigned type even in the full
expanded union. Native evidence cannot be propagated through arbitrary source
reduction by replacing exact syntax with these stronger non-eta joins.

The same witness is positively repaired by eta-expanded stage one, which
recovers the assigned type exactly. This is a strict comparison of certificate
languages, not a counterexample to strengthening. The earlier ledgers' phrase
"universal common-native coverage" must henceforth mean an eta-aware (or otherwise
strictly stronger) notion; it is not an outstanding conjecture for the old
non-eta union or the level-core image invariant.

**Positive bridge proved:** native eta primitive substitution now accepts type
guards that mix ordinary computation, explicit universe conversion, constant
expansion and native identity expansion. Joined level-core images transport
those native certificates to ordinary output residuals; the existing eta-aware
Pi readout then joins the exact substituted short and long expressions. At a
beta cut the original argument may itself have a mixed native certificate merely
level-core-joined to its assigned carrier. Neither exact assigned-type recovery
nor purity is required. Actual stored definitions discharge soundness, rigidity,
ordinary confluence and universe compatibility, with no quotient-registration
hypothesis. General eta/singleton computations in the native guards, full
eta-aware common-native coverage, and the strengthening conclusion remain open.

Validation: two modules, 772 jobs, 10 public roots, maximum dependency closure
11,960; standard axioms only and exclusions clean. All 747 imported local sources
were hash-stable and no new-module warnings occurred. Goal active; no PR extraction.


### Neutral eta: compare the two long branches (2026-11-04)

**Proved for variable/constant application spines.** The prior checked obstruction
says a variable cannot core-join its eta expansion. That does not prevent two
independently selected eta expansions from core-joining each other. Typed native
replay and sort uniqueness first align the fresh argument's proof classification.
A core join of the selected Pi types then joins the two domains, leaving identical
long-form bodies. Native recoveries of a variable start from the same lookup;
constant recoveries start from the same declaration; application recovery joins
codomains and substitutes the same unrestricted argument. Thus independent native
guards with core-joinable typed paths yield joined native outputs on every
variable/constant-headed application spine. No argument native evidence, purity,
termination, or assigned-type recovery is required.

The guard relations may be independent unions with arbitrarily nested eta on
literal lambdas. Two root neutral eta expansions remain core-joined after
independent lambda-eta-union paths on their long branches. All four base identity
guard relations may differ and need only source descent. Actual well-formed
environments with canonical Eq instantiate the theorem using stored definitions
and full-eta-union base identity guards, without quotient registration.

**Boundary:** this is a long/long root-peak result, not full neutral-eta confluence.
It neither core-joins the short source to a long form nor permits arbitrary neutral
eta and singleton-prefix computations inside the guards or continuations. Changed
neutral sources, projection-headed recovery, full eta-aware coverage, and the
remaining global confluence/strengthening argument are still open. This result is
not a new sufficient obligation strictly smaller than PropFront. Next live step:
relate independently recovered guards across a changing source, rather than demand
an impossible core join between that source and its eta expansion.

Validation: five modules, 471 Lean lines; both explicit builds completed 764 jobs;
19 public-root audits (including the new spine inductive's constructors and recursor
rules), maximum closure 11,605, standard axioms only and forbidden dependencies
absent. All 739 imported local sources were hash-stable and identical to the isolated
copy. No new-module warnings. Artifacts: `/tmp/carrier-neutral-eta-*`. Goal active.

### 2026-11-04 21:43:51 UTC — Augmented environment core and lambda-eta native guards

- **Finish universe compatibility for the repaired quotient collection.**
  Accepted and proved: the closed quotient value is a fixed two-universe
  template; equivalent universes preserve its source-zero guard and structural
  value. Selected structure compatibility was already proved in
  `StructureLevelCompatibility`; the missing component was the quotient branch.
- **Require quotient registration globally to use the enlarged core.**
  Unnecessary: reuse `FullHead.quotDefinitions` and add selected structure
  programs. The resulting collection has soundness, rigidity, level compatibility,
  typed ordinary/level confluence, and exact actual quotient-prefix replay in
  every environment. A prefix certificate supplies its own registration.
- **Transport native guards through nested literal-lambda eta.**
  Accepted and proved: the existing lambda-eta common-core theorem discharges
  `LevelCoreNative.recovery_of_compute_join`; the recovered output retains an
  ordinary residual. This yields native eta substitution under joined images
  and a first-stage body/full-eta argument square. The concrete augmented core
  discharges all declaration interfaces, including quotient/structure equations.
- **Infer universal native coverage from the broader lambda-eta guard grammar.**
  Rejected: the guard paths still collapse to level-core native recovery, so
  the previous neutral assigned-eta common-carrier obstruction remains. These
  are conditional transport tools, not a smaller sufficient strengthening front.

Validation: four modules, 397 Lean lines, 24 public roots; 777-job build;
transitive dependency audit maximum 12,236; only standard Lean axioms.
No strengthening, sorryAx, or excluded recovery/front dependencies. No executable
changes or PR extraction. The full GOAL.md deliverable remains open.


### Reconstruct native eta after neutral arguments compute (2026-11-04)

**Proved, without target or argument native evidence.** The preceding neutral
long/long diamond supplied independent recoveries at both endpoints. A stronger
source-changing result now constructs the new recovery when a fixed variable or
constant head's arguments have independent core common reducts. Induction on the
original native certificate transports the selected output to a forward core
reduct. In an application, Pi inversion supplies the codomain residual, and both
argument paths instantiate it at their common reduct. In a conversion, typed
core confluence at the original recovered type joins the transported output and
the guard's core readout. No arbitrary assigned-type coverage premise occurs.

For an original native eta guard, the transported output remains a Pi; its domain
is a forward core reduct of the original selected domain and retains that domain's
sort witness. Thus native eta is reconstructed on the changed short branch, and
the two long forms core-join. Typed spine computations with arbitrary lambda-eta
paths in every argument supply the needed structural argument joins. The original
guard and argument paths may use independent unbounded lambda-eta unions. The
computed short branch closes at eta stage one, independent of those depths;
the original long branch uses only level-core computation. Arbitrary lambda-eta
continuations of that long branch can be absorbed too. The actual-environment
wrapper needs only WF and canonical Eq, with full-eta base identity guards.

**Boundary and next live case:** the spine head and application structure are
preserved; argument internals are unrestricted by purity or native recovery.
This does not cover head beta/delta contraction, projections, arbitrary neutral
eta inside guards/arguments, or higher singleton-prefix steps. Unrestricted native
source stability is already refuted, so the next head-changing case must keep
its specific Pi/eta demand explicit rather than assume general output stability.
The result is a new critical square, not full confluence, a strengthening proof,
or a sufficient smaller obligation. Goal remains active.

Validation: three modules, 300 Lean lines; explicit main and isolated builds each
completed 766 jobs; all 15 public roots audited, including inductive constructors
and recursor RHSs. Maximum closure 11,611, standard axioms only, forbidden paths
absent. All 741 imported local sources stayed hash-stable and byte-identical to
the isolated copy. No new-module warnings. Artifacts: `/tmp/carrier-spine-eta-square-*`.


### Head beta with an explicit lambda readout (2026-11-04)

**Proved:** `BetaLambdaReadout` records a literal lambda or a finite nest of
literal-lambda applications whose body has a readout before substitution. Its
indices give the exact exposed domain and body, and a checked finite beta path
reaches them. Arguments and the final body are unrestricted. Any core-native
certificate for such a source selects a Pi whose domain is a forward core reduct
of the exposed domain. This follows by syntactic native inversion, Pi preservation,
and raw substitution of codomain paths; no argument native certificate is used.

Collapse descending core-joinable native guards to core recovery, apply this
readout, and use typed eta's function-to-lambda residual to restore the exact
exposed body. The original short source and its native eta expansion then share
a level-core reduct. This handles eta before these head-beta steps, including
arbitrary finite wrapper depth, without separately recovering the contractum.
Starting native eta evidence remains required; this is not universal recovery.

The resulting beta-lambda eta stages allow this broader source grammar at every
native guard depth. Whole typed paths core-join, independent paths are confluent,
and arbitrary actual substitutions preserve paths up to core joins without native
image evidence. The literal-lambda stages embed at the same index; the broader
stages embed into the full eta union. Whole-function beta squares accept these
paths while their arguments compute in the full eta union. The augmented actual
environment core discharges the interfaces under WF and canonical Eq, retaining
its optional quotient and registered structure equations.

**Boundary:** a lambda created by substitution into a variable/neutral body is
not a `BetaLambdaReadout`; neither are arbitrary head delta or projection paths.
Do not infer general head-beta core joins. The next concrete test is an identity
wrapper carrying an eta-converted Pi annotation: its contractum has a lambda
readout, but comparing the two selected domains may require genuine eta in the
annotations rather than this core invariant. General neutral eta and higher
singleton-prefix guards, eta-aware native coverage, whole-union confluence, and
strengthening remain open. No smaller sufficient obligation is claimed.

Validation: four new modules, 363 Lean lines, 19 own public roots. Both explicit
builds passed (772 jobs). The complete isolated audit checked 41 roots including
newly imported public definitions, transitive types, opaque proof values,
constructors and recursor RHSs; maximum closure 11,912 and standard axioms only.
All 747 local source imports were hash-stable and byte-identical to isolated
copies. No new-module warnings. Artifacts: `/tmp/carrier-beta-lambda-eta-*`.

### 2026-11-04 21:59:30 UTC — Function eta still omits unit/structure eta

- **Prove universal common-native coverage after adding function eta.**
  Rejected for the present language by a checked conditional obstruction: in
  every canonical-Eq environment with a closed positive empty structure, take
  distinct unit variables x,y, a variable F : Unit → Type, and p : F x. Unit-like
  equality also types p at F y, but full function-eta computations from F x and
  F y have no common reduct. Native recovery of p starts at F x. All singleton
  stages, explicit universes, controlled beta expansions and native function eta
  are allowed. The actual augmented core retains quotient/structure equations.
- **Use typed neutral observations with an opaque carrier.**
  Accepted and proved. Extend closed control types by a positive closed atom
  separated from Pi types. This excludes native function eta at the atom while
  admitting it at control arrows. Beta, changed binder contexts and every eta
  stage preserve neutral demands. A raw identity test at F reads the exact
  opaque variable, and raw beta confluence separates the two family outputs.
- **Hope beta preserves common-native evidence in the function-eta union.**
  Rejected by the same witness: (λ z : F y, z) p has exact stage-zero native
  assigned-type recovery, but one typed beta contraction loses all full-union
  common-native evidence. The example needs no recursive definitions.
- **Repair the computation language with native unit/structure eta.**
  Live next direction. The missing operation is expansion of opaque unit or
  record inhabitants to their constructors, not more function-eta guard depth.
  Native family recovery could guard a descending unit expansion; general
  structure expansion additionally needs its admissible projected field recipe.
  No repair or general confluence theorem for that extension is claimed here.

The theorem assumes actual positive empty-structure registration; it constructs
all four context variables and their typings. It does not construct a complete
canonical-Eq environment, refute declarative strengthening, or supply a smaller
sufficient front. Validation: six modules, 894 Lean lines, 89 audited public
roots, 751-job build, maximum closure 11,467; standard axioms only.


### Native Pi at both beta endpoints still does not give core joining (2026-11-04)

**Refuted the proposed generalization from readout to arbitrary beta exposure.**
Use the existing eta-equal pure domains `F f` and `F (fun x => f x)`. A literal
lambda with the former domain is assigned a Pi with the latter domain, then
wrapped by the identity at that assigned Pi. The wrapper natively recovers its
exact assigned Pi; its beta contractum also natively recovers a Pi at stage zero.
Native eta at the wrapper uses the assigned domain. Beta cleanup of this long
branch and of the wrapper produces two lambdas with the same constant body and
the two different domains. Those pure beta-normal domains do not join even up
to universe variants. Thus the original short source and its native eta expansion
have no level-core common reduct, despite a literal-lambda beta contractum and
native Pis at both endpoints.

The same typed peak has an explicit eta-stage-one repair: native eta inside the
contractum's domain changes `F f` to `F (fun x => f x)`; the original long branch
needs only beta. The obstruction is to the core-join invariant, not confluence.
A general replay lemma also shows that common endpoints of typed core-joinable
paths force core joins of the sources. Consequently no finite depths of the
beta-lambda eta union can join this peak, even with full-eta base identity guards.
An actual-environment wrapper discharges all interfaces under WF and canonical Eq.

**Research update:** beta reduction creating a lambda by substituting into a
neutral body cannot be added to the previous grammar merely by requiring native
Pi availability. Its domain join must allow genuine eta. The newly committed
`a4d2a59a` additionally refutes universal common-native coverage for the entire
function-eta union using positive unit-indexed families (with explicit unit
registration/typing assumptions). Therefore full function-eta coverage is no
longer an open conjecture for that language. Unit/structure eta or a comparison
system accounting for it is required; the beta/domain transport problem must be
addressed in that stronger language. Strengthening remains open, and neither
obstruction is a canonical-Eq strengthening counterexample or a sufficient
smaller obligation.

Validation: two modules, 240 Lean lines, four own public roots; both explicit
builds passed (789 jobs). Audited 47 public roots including newly imported modules,
maximum closure 12,050, standard axioms only and forbidden dependencies absent.
All 764 imported local sources were hash-stable and byte-identical to the isolated
copy. No new-module warnings. Artifacts: `/tmp/carrier-eta-beta-limit-*`.


### 2026-11-04 22:07:28 UTC — Recovered unit eta repairs the full-function-eta obstruction

**Verdict: checked positive repair, not universal coverage.** Added native unit
expansion for arbitrary parameterized unindexed empty structures. Its native
family guard determines the entire retained parameter spine; arbitrary-block
descent reconstructs that spine and the registered constructor below insertion
at the source's original assigned type. Integrated it with prior singleton, Eq,
identity and function eta stages, proved renaming and finite-union admission,
and transported exact native-image substitutions with the additive stage bound.

The exact four-variable unit-indexed context now simultaneously witnesses failure
of every old function-eta depth and a stage-one common native type in the new
system. Both indices compute to the constructor. The identity-wrapper beta step
has exact stage-zero native recovery before contraction and repaired common
native recovery afterward. No global native coverage hypothesis was introduced.

Next live direction: general structure eta, with proof-field masks certified
from the closed constructor telescope. General source-computation stability and
confluence remain open; this does not establish strengthening or a sufficient
strictly smaller obligation. Validation: four modules, 30 audited public roots,
757 build jobs, maximum dependency closure 11,343; standard axioms only,
forbidden dependencies absent. Artifacts: `/dev/shm/unit-eta-repair-*`.


### 2026-11-04 22:15:01 UTC — General structure eta from a static proof-field mask

**Verdict: checked for all admissible unindexed structures with native family
recovery, including dependent mixed proof/data fields.** The closed constructor
certificate `StructureReplay.ProofField` is equivalent to proofness of each
projection at every typed expansion. Therefore the output mask can be chosen
from the closed telescope alone: proof fields become proof markers, other fields
remain projections of the retained major. No occurrence-dependent mask guess,
new semantic guard, inverse typing weakening or full native coverage is needed.

Implemented the masked expansion, exact erasure theorem, arbitrary-block descent,
renaming and exact native-image substitution. The new stage language embeds both
old function eta and unit eta at the same index and supports recursive guards,
finite-union admission, and additive-stage native/checker/aligned substitution.
Actual typed structure-eta steps replay whenever the retained major has native
family recovery; proof majors need no recovery. Nonempty proof-only structures
join opaque majors at a constructor with all proof fields erased. Output
computation respects parameter and source computation, producing a source-change
square under explicit native family recoveries at both endpoints.

The square does NOT supply the second native family guard or the parameter path.
Those remain part of the general source-change problem. Common-native coverage
and confluence of the enriched language remain unproved, as does strengthening.
The extension removes a diagnosed omission and supports arbitrary field counts;
it is not a sufficient smaller obligation. Next live work: native recovery under
source computation and comparison of independently selected family instances,
allowing genuine eta joins rather than the refuted core-only join invariant.

Validation: five modules, 627 Lean lines, 43 public roots, 713 build jobs,
maximum dependency closure 11,121, standard axioms only and forbidden
dependencies absent. All 688 imported local sources were hash-stable. Artifacts:
`/dev/shm/static-structure-eta-*`. Concurrent alternate structure-expansion files
were preserved; distinct module names avoid the observed untracked filename
collision. No coordination or PR extraction.


## Closed telescope masks and projection residuals (2026-11-04)

Added an independent constructor-telescope formulation of general native
structure expansion. Proof status of every supplied telescope argument is
exactly proof status of its variable in the closed full telescope; this fixes
masks even for dependent proof fields. The raw recipe commutes with arbitrary
substitution. Native family recovery then supports arbitrary-block descent,
renaming and typed native-image substitution of the whole expansion.

Projection of the expanded constructor computes in the primitive core to the
original field erasure. This includes proof fields and needs no native
certificates for parameters, fields or the expanded major. A separate residual
module connects this result directly to the committed static-mask structure-eta
language. The two mask presentations coexist; no parallel stage hierarchy was
introduced. These are local source-change cases, not general confluence,
coverage, strengthening or a sufficient smaller front.

Validation: four new modules, 386 Lean lines, 20 public roots; isolated explicit
715-job build covering ten changed modules; all 71 public roots in those modules
audited through types, opaque values, constructors and recursor RHSs, maximum
closure 11,121. Only propext/Classical.choice/Quot.sound and no configured
forbidden dependencies. All 690 imported local sources hash-stable and identical
to the isolated copies. Artifacts `/tmp/carrier-native-structure-*`; preparation
`/tmp/prepare-carrier-native-structure.py`. Next live question: native recovery
of the expanded constructor at its original family, then its interaction with
source computation and independently selected family instances. The original
strengthening sorry remains open.


## Dependent projection-type residuals through structure eta (2026-11-04)

The projection critical pair now extends through the entire dependent field-type
recipe. After expanding a major, every preceding projected capture computes to
its original erased field. Typed telescope substitution identifies raw recipes
with their masked capture vectors, so erased proof dependencies require no
reverse computation from a proof marker. This yields primitive-core computation
from the expanded-major projection type to the original type, for arbitrary
dependent fields and parameters.

Consequently, a retained projected field recovers at its original selected type
and reuses every original guard conversion tail, given native recovery of the
expanded major at the selected family. No field or parameter recovery is assumed.
This is a local source-change theorem, not general confluence or coverage. The
next issue is composing this result with exact constructor recovery, then handling
independently selected family instances. A literal constructor walk was checked
locally; the overlapping untracked constructor-recovery work was left untouched
and was not imported or committed by this work.

Validation: one new module, 152 Lean lines, five public roots; isolated 714-job
build; complete transitive dependency audit, maximum closure 8,370, standard
axioms only, all configured forbidden dependencies absent. All 689 imported
local sources hash-stable and isolated-identical. Artifacts:
`/tmp/carrier-structure-projection-type-*`; preparation
`/tmp/prepare-carrier-structure-projection-type.py`. Goal remains open.


### 2026-11-04 22:32:05 UTC — Exact selected-family recovery at eta expansion targets

**Verdict: checked, no post-step native premise.** Every actually typed saturated
constructor of an unindexed registered structure follows its literal declaration
telescope to the exact family at its own parameters. The parameters and fields
need no independent native certificates. Consequently a masked structure-eta
target recovers the exact family chosen by its guard, already at stage zero.
This includes mixed proof/data and dependent fields. Every later conversion
from that selected family can be retained at its original relation.

Function eta likewise preserves its exact selected Pi at the previous guard
stage. Lift the native function certificate, apply it to the correctly erased
fresh variable, and use the typed eta-instantiation identity for proof domains.
All subsequent conversions from that Pi remain available. The source may be
neutral and all prior structure/function-eta guards may occur in its recovery.
These results cover selected eta guards, not arbitrary independently selected
source types and not arbitrary source computation.

Validation: two modules, 220 Lean lines, eight public roots in the combined
789-job source-recovery build; audited maximum closure 11,050; standard
axioms only and forbidden dependencies absent. Artifacts:
`/dev/shm/masked-source-recovery-*`. Strengthening remains open.


### 2026-11-04 22:32:11 UTC — Exact beta recovery where possible; general exact coverage refuted

**Verdict: exact root-beta transport checked for native retained arguments and
unconditionally for proof arguments; universal exact coverage is impossible.**
Extended certificate descent, backward binder transport and marked Pi-origin
readout to the full masked-structure/function-eta stages. A new literal Pi
endpoint extraction gives exact component histories, without a residual beta
normalization of the selected Pi. Thus a native lambda body can recover the
selected codomain in its original written-domain context. Substituting an
argument natively recovered at that written domain preserves the redex's exact
selected result, including all final conversions. Proof arguments impose no
recovery condition. No confluence premise is used.

The condition cannot simply be erased: for *every* primitive relation with
binder descent, a lower-typed source cannot natively recover a type containing
a retained fresh binder. A concrete three-to-four-variable unit-indexed context
assigns p:F x also F y after adding the unused unit binder y. Hence universal
exact assigned-type recovery is incompatible with descent itself, independently
of the chosen computation grammar. The same witness has a common native type
at unit-eta stage one. In the full structure language, an identity wrapper has
exact stage-zero recovery at F y; one beta contraction loses exact recovery at
F y at every finite union depth, while stage-one common recovery survives.

This is not a strengthening counterexample. It rules out universal *exact*
native source stability even after adding all structure eta. Future source
stability must retain common native types (or adequate comparisons); the
remaining task is common-native argument substitution and joins for independently
selected native carriers, allowing genuine eta. Existing exact transport remains
useful locally, especially for proof beta, but cannot be the universal invariant.

Validation: five modules, 640 Lean lines, 26 public roots in the combined
789-job build; maximum audited closure 11,480; standard axioms only,
forbidden dependencies absent. Artifacts `/dev/shm/masked-source-recovery-*`.
Original strengthening sorry remains; no final deliverable or PR extraction.


## Native structure diamonds with proof parameters (2026-11-04)

Equivalent well-formed universe instances have identical static field masks.
Simultaneous parameter/major computations therefore lift to structure outputs
across different selected constructor universes. Two outputs join at any explicit
common parameter vector and major, without typing or recovery of that shared raw
constructor. For two native family recoveries of the same actual typed source,
replay plus family injectivity proves universe equivalence; it is not a further
confluence hypothesis. General retained parameters still require explicit common
computations. This does not restore the refuted universal core-join invariant.

The proof-parameter case discharges that remaining local premise. If every
parameter in the source's assigned registered family is a proof, actual family
injectivity forces any native selected family to have the same name and the same
literal erased parameter vector. Hence any two native masked structure expansions
of that source join by directed level-core computation alone. Their guard
relations can differ and may have arbitrary depth, provided they have source
descent. The theorem admits nonempty dependent proof parameters and arbitrary
mixed proof/data fields. The nullary-family special case is also explicit.

This closes a family of same-source structure-expansion peaks, not whole-language
confluence, universal native coverage, strengthening, or a sufficient smaller
front. Remaining general peak work includes retained parameter joins and
recovery under source changes; the committed dependent projection-type residual
handles one such compatible source-change case.

Validation: one new module, 244 Lean lines, ten new public roots; two-module
isolated explicit 714-job build and complete audit of all 13 selected public
roots, maximum dependency closure 10,963. Standard axioms only and every
configured forbidden dependency absent. All 689 imported local sources were
hash-stable and byte-identical to isolated copies. Artifacts:
`/tmp/carrier-structure-universe-join-*`; preparation
`/tmp/prepare-carrier-structure-universe-join.py`. The earlier changed import was
retained explicitly when regeneration followed the proof-parameter extension.
Other untracked work was preserved; no coordination. Goal remains active.


## Closing the native projected-structure square (2026-11-04)

Combined the now-committed exact constructor recovery with the dependent
projection-type residual. A retained projection of an expanded constructor
recovers the original field recipe and reuses its complete conversion tail,
without any target-major, parameter or field native premise. In the full static
structure union, the source major's family certificate admits the compatible
expansion below the projection; the new projected expression returns to the old
field erasure in primitive-core computation and retains the selected native type.
This handles arbitrary dependent fields and parameters at the chosen family.

The newly committed fresh-binder boundary rules out universal exact native
coverage for every descending primitive relation, not only the current grammar.
The local projection square does not contradict it: expansion preserves the
chosen family and contracts its projected captures back. Next general work must
retain common-native recovery/comparison and join independently selected retained
parameters; universal exact source stability and universal core joining are both
refuted routes. Strengthening and a sufficient smaller front remain open.

Validation: one new module, 86 Lean lines, two public roots. Isolated explicit
718-job build covering the new module and changed committed constructor-recovery
import; all seven public roots audited transitively, maximum closure 10,961,
standard axioms only and no configured forbidden dependencies. All 693 imported
local sources hash-stable and isolated-identical. Artifacts:
`/tmp/carrier-projected-structure-native-square-*`; preparation
`/tmp/prepare-carrier-projected-structure-native-square.py`. No executable changes,
coordination or PR extraction. Goal remains active.


## Common-native instantiation and computed binders (2026-11-04 22:45:25 UTC)

Verdict: common-native single instantiation is equivalent to forward native
recovery transport across one computed binder. Both remain open obligations;
the reduction does not establish a strictly smaller sufficient front. The
argument's assigned type computes to its selected native type. Realize that
type as an actual binder, transport the body's certificate forward, and apply
exact native substitution. Conversely, insert the new binder below the old
one and substitute its generic variable; typed erasure substitution handles
proof arguments without identifying their erasures with raw variables.

A checked necessary consequence explains why the binder problem is substantial:
it implies joining every pair of computations from any typed type in the full
static structure/function-eta union. A retained generic variable tests a fork
at its binder type, and certificate descent removes the generic binder from
both output paths. Wrapping an arbitrary type A as the domain of A -> Prop
makes that generic variable a retained function even when A is a proposition.
Marked Pi readout then extracts a common reduct of the original domains. No
normalization, universal exact coverage, or confluence premise was used in
these implications.

Next direction: establish common-native source recovery together with the
necessary type-fork joins; forward binder transport cannot be treated as a
free context-conversion lemma. Its application case must transport codomain
computations through arguments that native application recovery does not itself
certify. Exact native coverage remains refuted. These results do not close
strengthening or supply the requested strictly smaller sufficient obligation.

Validation: two modules, 301 Lean lines, ten public roots; explicit 768-job
build and full dependency audit (types, opaque bodies, inductive constructors,
and recursor RHSs), maximum closure 11,483; only standard axioms and no
configured forbidden dependencies. All 743 imported local sources hash-stable.
Artifacts: `/dev/shm/common-native-binder-*`; preparation
`/dev/shm/prepare-common-native-binder-audit.py`. Goal remains active; no PR
extraction or executable changes.


## Exact universe readout for common native recovery (2026-11-04)

Implemented typed finite observations of a marked universe, preserving its
level certificate under every finite stage of the full static structure/function
eta language. Arbitrary compatible computations from a well-formed sort have a
beta readout at an equivalent well-formed sort. Constant and identity wrappers,
function eta in control positions, changed lambda annotations, arbitrary guard
depths and level conversion are included. Ordinary control typing excludes
structure expansion and function eta at the universe payload; no confluence,
normalization, native coverage or strengthening is assumed.

A native certificate meeting an assigned sort at a shared computed output can
therefore append beta cleanup and a final universe conversion to recover the
EXACT assigned sort. Dependent function formation follows from common native
certificates for the domain and codomain in their original contexts. This closes
the sort-demand/formation case of common-native substitution; it does not solve
forward binder transport, rigid-family exposure with retained parameters,
general common-native coverage, strengthening or a sufficient smaller front.

Validation: four new modules, 592 Lean lines, 45 new public roots. Isolated
explicit 744-job build and 65-root audit, including three changed committed
imports, maximum dependency closure 11,480. All configured forbidden dependencies
absent, no sorry sources, standard axioms only. All 719 local closure sources
hash-stable and byte-identical to isolated copies. Artifacts:
`/tmp/carrier-static-structure-sort-*`; preparation
`/tmp/prepare-carrier-static-structure-sort.py`. Own new modules have no warnings.
Other untracked files/index preserved; no coordination or executable changes.
Goal remains active.


## Common native application at proof and type arguments (2026-11-04)

Full Pi readout plus exact retained-image computation transport now propagates
a common native function certificate through application. The output retains a
forward path from the original dependent result type; the selected native Pi
may have changed both components. Proof arguments need no image certificate.
For type arguments, common native recovery suffices because the preceding sort
readout restores the exact universe demand. These close two application cases
without confluence or exact coverage for arbitrary data arguments.

The attempted unrestricted declaration-telescope extension still requires native
images to substitute its codomain histories. Ordinary typed substitution alone
does not transport native guards. The newly committed forward-binder/type-fork
reduction independently makes the broader requirement precise: general common
native instantiation contains joining every computational fork at a typed type.
No general telescope transport, type confluence, strengthening, or sufficient
smaller front is claimed here.

Validation: one new module, 124 Lean lines, four public roots; isolated explicit
746-job build, all four roots audited through dependency closure (maximum
11,542), standard axioms only, no sorry sources or forbidden dependencies.
All 721 local closure sources hash-stable and isolated-identical. Artifacts:
`/tmp/carrier-static-common-app-*`; preparation
`/tmp/prepare-carrier-static-common-app.py`. No new warnings or executable
changes; independent committed work reused read-only, no coordination.
Goal remains active.


## Exact transport across erased proof binders (2026-11-04 22:51:11 UTC)

Verdict: the proof-variable branch of forward native binder transport is
closed unconditionally. Definitionally equal proof binders provide exact native
identity images for any image relation: the newest lookup is erased, while
older lookups recover directly from the unchanged tail. The full static
structure/function-eta grammar therefore transports both computations and native
recoveries at the same finite stage and with the exact original output. No
computation in either direction between the binder annotations is required.

This removes a proved branch from the existing obligation: NativeForwardBinder
is equivalent to its restriction to retained generic variables. That remaining
restriction is not asserted, and the previous function-to-sort test means it
still entails all typed type-fork joins. General retained-argument substitution
and the original strengthening theorem remain open; this is not a sufficient
strictly smaller front. The application investigation continues to expose the
uncertified-argument gap when a function's native codomain changes.

Validation: one module, 135 Lean lines, seven public roots; explicit 768-job
build, full transitive audit including opaque values and recursor rules,
maximum closure 11,111, standard axioms only and no configured forbidden
dependencies. All 743 local import sources hash-stable. Artifacts:
`/dev/shm/static-proof-context-*`; preparation
`/dev/shm/prepare-static-proof-context-audit.py`. No executable changes, PR
extraction or coordination. Goal remains active.


## Exact transport at computed universe binders (2026-11-04 22:53:05 UTC)

Verdict: the literal-universe branch of forward binder transport is now
proved with exact outputs and no stage increase. The newly committed sort
readout supplies beta reduction from every full-union reduct of sort u to an
equivalent literal sort. A stage-zero level step returns to the original u.
The existing backward-context image theorem then runs in the needed forward
direction, yielding stage-zero exact native identity images for the computed
binder. Its original domain path may have arbitrary guard depth.

A CommonNativeArgument assigned sort u also yields exact recovery of sort u,
using the committed exact-sort readout. Consequently beta contraction at a
commonly recovered type argument preserves every selected native result
exactly, including its final conversion tail. No general forward-binder,
common-instantiation, confluence, or data-coverage premise is used. Together
with proof-context transport this closes two concrete branches of the native
transport problem. General retained data arguments (and arbitrary nonliteral
annotations merely convertible to universes) remain open; these results do not
close strengthening or establish a sufficient strictly smaller PropFront.

Validation: one module, 109 Lean lines, six public roots; explicit 772-job
build and complete dependency audit (types, opaque bodies, constructors and
recursor rules), maximum closure 11,530, standard axioms only and all
configured forbidden dependencies absent. All 747 local import sources
hash-stable. Artifacts: `/dev/shm/static-sort-context-*`; preparation
`/dev/shm/prepare-static-sort-context-audit.py`. No executable changes, PR
extraction or coordination. Goal remains active.


## Returning computed control types before binder transport (2026-11-04)

A full enriched computation from any well-formed closed control type (universes
and arbitrary nested arrows) now has a path back to its EXACT initial type.
The key general lemma is dependent: if a Pi domain and codomain admit return
paths in their original contexts, so does the whole Pi. Marked readout exposes
both histories; restoring the domain FIRST puts the codomain return in exactly
the context where it was established. No forward binder premise is needed for
this composition, and intermediate syntax is unrestricted.

Consequences: all forks at control types join; common native evidence at such
a type restores its exact assigned output; binders computed from control types
admit exact forward native transport for arbitrary bodies and selected types;
and common-native application extends to arbitrary higher-order control
arguments. A generic backward-context recovery theorem is also explicit.
This is a proved family of forward-binder cases, not general type confluence,
universal common coverage, strengthening, or a sufficient smaller front. The
next extension uses neutral observations to admit dependent type variables.

Validation: one new module, 157 Lean lines, seven public roots; isolated explicit
747-job build and complete seven-root audit (maximum closure 11,543), standard
axioms only and no forbidden dependencies or sorry sources. All 722 local closure
sources hash-stable and isolated-identical. Artifacts:
`/tmp/carrier-static-control-return-*`; prep
`/tmp/prepare-carrier-static-control-return.py`. No new warnings, executable
changes or coordination. Independent untracked files preserved. Goal active.


## Opaque type-variable readout and exact data demands (2026-11-04 22:58:38 UTC)

Verdict: every full structure/function-eta computation from a variable assigned
a universe returns to that exact variable by pure beta. Reinterpret the existing
sort observation with no literal universe payloads and one selected free-variable
demand. The typed transport theorem already rules out structure eta at sort
assignments and prevents a function observation replacing the marked sort
demand. A small parametric realization proof gives the exact variable readout;
no unrestricted normalization or confluence hypothesis is introduced.

This supplies stage-zero exact identity images from an opaque type-variable
binder to any of its computed annotations. Both computations and native recovery
therefore transport forward at the same finite stage and with exact outputs.
Common native evidence for an argument assigned an opaque type variable restores
that exact type, so root beta retains every selected native result without
assuming general common-native instantiation. Proof arguments retain their
vacuous image demand. This extends the exact-demand result to retained data at
opaque types, not only arguments assigned literal universes.

The function-type investigation now has the missing variable leaf for dependent
Pi return trees (including bound type variables). Neutral type applications
such as F x remain outside this return argument: their arguments can undergo
structure eta, so returning to the original index would conflict with the
existing exact-coverage obstruction. General common-native recovery, the full
forward-binder law, and strengthening remain open. No sufficient strictly
smaller front is claimed.

Validation: two modules, 193 Lean lines, nine public roots; explicit 772-job
build and full transitive dependency audit, maximum closure 11,526; only
standard axioms and no configured forbidden dependencies. All 747 local import
sources hash-stable. Artifacts: `/dev/shm/static-variable-context-*`;
preparation `/dev/shm/prepare-static-variable-context-audit.py`. No executable
changes, PR extraction or coordination. Goal remains active.


## Dependent variable/universe/Pi return paths (2026-11-04)

Reused marked-Pi control observations with an EMPTY payload predicate to obtain
neutral demands. Their existing beta interpretation proves exact variable
readout through the full static structure/function-eta language whenever the
variable is assigned a universe, including proposition variables. This avoids
building another observation calculus.

The new UniversePiSyntax grammar admits variables, universes and dependent Pi
binders. Every full-union computation from a typed member returns to its exact
initial erasure, with no restriction on intermediate terms or guard depths.
The Pi case restores the domain first and then the codomain in its original
context. Thus all forks rooted at these types join, common native evidence
restores the exact assigned type, computed binders admit exact forward native
transport for arbitrary bodies/outputs, and common-native application works at
these dependent domains. This strictly extends the closed-control cases.

This is not a claim of general return paths: the existing fresh-argument reverse
beta boundary already prevents that generalization even for a typed pure beta
redex. General joining must allow new common results. Applications and rigid
family types remain outside this return argument; universal common-native
coverage, type-fork confluence, strengthening and a sufficient smaller front
remain open. Independent uncommitted work was preserved, and a source-name
collision was avoided by retaining the neutral-demand proof in its own module;
no uncommitted independent code was imported or coordinated with.

Validation: two new modules, 170 Lean lines, eight public roots (including the
syntax inductive); isolated explicit 749-job build and complete eight-root
audit, maximum closure 11,599, standard axioms only and no forbidden dependencies
or sorry sources. All 724 local closure sources hash-stable and isolated-identical.
Artifacts `/tmp/carrier-dependent-return-*`; prep
`/tmp/prepare-carrier-dependent-return.py`. No new warnings or executable changes.
Goal remains active.


## Returning a neutral type application (2026-11-04 23:05:20 UTC)

Verdict: the first neutral-application return case is proved. For variables
F : Sort u -> Sort v and A : Sort u, every computation of the erased F A in
the full structure/function-eta union beta-reduces back to the exact F A.
Extend the typed sort-demand grammar with a second atomic key; both keys retain
a sort assignment and exclude root structure/function eta. The function demand
uses one key for its argument and the other for its result. A two-target
realization of the existing empty-payload observations then retains both free
variables through beta, eta, constant/identity frames and changed annotations.
No variable-distinctness, normalization or confluence premise is needed.

Common native evidence for any retained value assigned this F A now restores
the exact assigned type. This provides the image certificate used by the
existing exact native substitution and root-beta preservation laws; it does
not assume the general forward-binder obligation. Universes u and v may include
Prop. The argument here is a type variable, not a proof or an arbitrary data
index. General F x with data arguments remains outside this return law, as do
arbitrary type arguments and general dependent constructor spines. Common
coverage, type confluence and strengthening remain open; no sufficient strictly
smaller front is claimed.

Validation: one new 150-line module, five new public roots, and a two-line
extension of the existing typed-demand grammar and its eta proof. Rebuilt all
11 affected source modules (779 jobs). Audited all 39 public roots including
both modified inductives, constructors, recursors, types and opaque bodies;
maximum dependency closure 11,248. Standard axioms only, no configured
forbidden dependencies, and all 747 local import sources hash-stable. Artifacts:
`/dev/shm/static-type-app-readout-*`; preparation
`/dev/shm/prepare-static-type-app-readout-audit.py`. No executable changes,
PR extraction or coordination. Goal remains active.


## Neutral application retains its Pi-argument history (2026-11-04 23:12:05 UTC)

Verdict: every full-union computation of F (Pi A B), for a neutral variable
F at the corresponding universe-to-universe function type, beta-reads as
F (Pi X Y). Its payload retains the actual representatives and complete
computational histories of X and Y in the ORIGINAL component contexts. A and
B are arbitrary typed components, including data-indexed types. They need not
return to their original syntax, have native certificates, or normalize.
The proof adds a second sort demand to marked-Pi control observations and
interprets it as the fixed family applied to the same lower payload.

A checked local consequence reduces every computational fork at F (Pi A B)
to a fork of the argument Pi A B itself. Reassemble the retained component
histories as computations of the original argument, apply the explicitly
supplied argument-joining premise, and lift the join under F after beta
readout. This is a local congruence reduction, not whole-language confluence
or a claimed smaller sufficient front. The established dependent return
theorem discharges the premise for variable/universe/Pi arguments and gives
an unconditional exact return for F applied to those dependent Pi types.

Next direction: replace the literal-Pi marker with an arbitrary sort-typed
argument marker, using certificate descent to update its complete lower
computation history. This would remove the syntactic argument restriction
from the neutral-family congruence reduction. Data arguments at non-universe
domains still expose the native-image/eta difficulty; general common coverage,
forward binder transport and strengthening remain open.

Validation: one new 194-line module with six public roots, and a two-line
extension of the existing marked-Pi demand grammar and its eta proof. All 45
affected tracked modules rebuilt (840 jobs); all 40 public roots in both
changed modules audited, including constructors, recursors, types and opaque
values. Maximum closure 11,614; standard axioms only and no configured
forbidden dependencies. All 725 local import sources hash-stable. Artifacts:
`/dev/shm/static-pi-app-origin-*`; preparation
`/dev/shm/prepare-static-pi-app-origin-audit.py`. Independent untracked work
preserved; no coordination, executable changes or PR extraction. Goal active.


## Dependent demand profiles with ignored domains (2026-11-04)

The closed-control observation restriction was preventing telescope readout at
retained data and dependent parameter domains. Introduced ordinary type profiles
with ignored domains, universe results and dependent arrows. A profile retains
actual well-formed type representatives and ordinary type equality. It transports
through arbitrary typed substitution and context conversion without any native
image premise. Visible profiles have positive universes; ignored profiles supply
no observations and may denote propositions or arbitrary dependent data types.

The typed-node layer now handles lambda inversion, beta interpretation, native
Pi selection and both controlled wrappers with these profiles. Function eta
retains a fresh argument only WHEN its profile is observed; ignored proof
arguments need not survive erasure. Visible profile heads exclude native
structure expansion. This supplies the dependent typing mechanism for neutral
head readout, not common coverage, type confluence or strengthening.

Validation for this foundation and its following observation/readout consumer:
eight selected modules, explicit isolated 747-job build, all 88 public roots
audited (including a changed committed control-observation import), maximum
closure 11,301. Standard axioms only, no forbidden dependencies or sorry sources.
All 722 local closure sources hash-stable and isolated-identical. This foundation
adds three modules, 352 Lean lines and 27 public roots. Artifacts:
`/tmp/carrier-dependent-neutral-head-*`; preparation
`/tmp/prepare-carrier-dependent-neutral-head.py`. No new warnings or executable
changes; independent untracked files preserved and not imported. No coordination.
Goal remains active.


## Neutral head and arity readout with dependent data parameters (2026-11-04)

Dependent-profile finite observations now survive every stage of the full
static structure/function-eta language, including beta, guarded singleton/Eq
steps, arbitrary control wrappers and changed binder annotations. An operational
interpretation with a beta-closed atomic predicate reads a fixed variable head
and arity while deliberately ignoring the exposed argument expressions.

For any saturated variable-headed application whose actual type profile is a
universe-ending dependent telescope, every full-union output beta-reduces to
that same variable head with exactly the original argument count. The telescope
may have arbitrary dependent proof/data parameter domains; arguments need no
native certificates. A literal dependent telescope ending in a universe supplies
the profile directly. Common native evidence against such a neutral type can
append beta cleanup to select a native type with the same head and arity.

This removes a head-exposure assumption for this class of neutral type
applications, but does NOT return retained arguments or provide their computation
histories. Parameter joining, rigid-family heads, and result kinds whose universe
shape emerges only after particular argument instantiation remain outside the
result. The next step must retain argument histories or construct their joins;
head/arity preservation alone cannot solve forward binder transport. General
common-native coverage, full type-fork confluence, strengthening and a sufficient
strictly smaller front remain open.

Validation: four consumer modules, 511 Lean lines, 40 public roots; together
with the preceding three foundation modules and changed committed import, the
explicit isolated build completed 747 jobs and the audit checked all 88 selected
roots (maximum closure 11,301). All 722 local closure sources hash-stable and
isolated-identical; standard axioms only, no forbidden dependencies or sorry
sources. Artifacts `/tmp/carrier-dependent-neutral-head-*`; preparation
`/tmp/prepare-carrier-dependent-neutral-head.py`. No new warnings, executable
changes, coordination or uncommitted independent imports. Goal remains active.


## Observing arbitrary sort-typed arguments (2026-11-04 23:23:00 UTC)

Verdict: marked arguments no longer need variable, universe or literal-Pi
syntax. A new typed observation carries an arbitrary lower argument with its
sort assignment through temporary control prefixes. Interpreted renaming and
substitution fix the original payload context, and beta control frames supply
only their finite demanded observations. The operational interpretation reads
both the argument and a fixed family applied to it.

Whole-argument computations update their lower certificates through the explicit
TypeArgumentClosure interface. All full static structure/function-eta primitives
preserve nonpayload control frames; compatible computation handles payloads,
beta, transitive intermediates and changing binder annotations. The next commit
instantiates this interface with complete actual argument histories. No native
image assumption or whole-language confluence is built into this machinery.

Validation: two foundation modules, 404 Lean lines, 28 public roots. Combined
four-module 779-job build and full 47-root audit; this commit's maximum
dependency closure 11,065. Standard axioms only; no configured forbidden
dependencies. All 754 local import sources hash-stable. Artifacts:
`/dev/shm/type-argument-origin-*`; preparation
`/dev/shm/prepare-type-argument-origin-audit.py`. Executable unchanged, no PR
extraction or coordination. Strengthening remains open; goal active.


## Arbitrary type-argument origins and nested neutral return trees (2026-11-04 23:23:06 UTC)

Verdict: every full-union computation of F A, for F a variable assigned
Sort u -> Sort v and arbitrary A : Sort u, beta-reads as F A'. The output
includes an actual equality A = A' and a lower computation from A to A'.
Certificate descent discharges the entire payload-update interface, so neither
argument syntax, native recovery nor normalization is assumed. Local fork
joining at A lifts to every fork at F A by beta readout followed by congruence.
The argument-joining premise remains explicit; global type confluence is not
asserted.

NeutralTypeTree closes the exact-return fragment recursively under universes,
type variables, dependent Pis and neutral universe-to-universe applications.
This includes arbitrarily nested constructors such as F (G A), as well as such
applications inside dependent Pi domains and codomains. Whole argument histories
let the application case use its recursive return theorem regardless of the
shape of computed intermediates. Common native evidence at any tree assignment
therefore recovers that assignment exactly; computed tree binders transport
native certificates forward exactly; root beta preserves every selected native
result for arguments commonly recovered at these types.

The result does not cover arbitrary data-indexed families, merely convertible
function profiles, or general common-native coverage. A next concrete case is
proof-parameter applications: the independently committed dependent head/arity
readout may combine with typed telescope inversion to force every exposed proof
argument back to the literal proof marker. General retained data histories and
the original strengthening/front obligation remain open.

Validation: two result modules, 235 Lean lines, 19 public roots (including the
return-tree constructors and recursors). Combined explicit 779-job build and
47-root full dependency audit, maximum closure 11,663; standard axioms
only and no configured forbidden dependencies. All 754 local import sources
hash-stable. Artifacts: `/dev/shm/type-argument-origin-*`; preparation
`/dev/shm/prepare-type-argument-origin-audit.py`. No executable changes, PR
extraction or coordination. Goal remains active.


## Exact return of dependent proof-parameter families (2026-11-04 23:30:03 UTC)

Verdict: proved, without native argument recovery. A saturated variable-headed
family whose literal dependent telescope contains only proposition domains and
ends in a universe has exact return under the full static structure/function-eta
union. Head-and-arity readout gives an exposed raw spine. Ordinary typed replay
realizes that spine, and typed telescope inversion at the original head forces
every argument to be a proof. All those arguments erase to the same proof marker,
so beta cleanup alone returns to the original erasure. Dependencies between
successive proposition domains are unrestricted. Intermediates are unrestricted.

`ProofErasureProofParameterReturn.lean` proves substitution stability of the
proof telescope, its typed argument-erasure property, variable-spine inversion,
exact return, exact assigned-type recovery from common native evidence, exact
forward binder transport, and preservation of the selected native result across
root beta. `NeutralTypeTree` now includes these families as leaves, retaining all
its recursive Pi/application return, binder transport and beta-recovery results.
Thus nested constructors can take proof-parameter families as type arguments.

This is a proved fragment extension, not a sufficient smaller obligation and not
a solution of strengthening. Arbitrary retained data parameters, merely
convertible telescope profiles and general common-native coverage remain open.
A direct extension of the argument would need more than head-and-arity readout:
typing no longer determines retained argument erasures. The next substantive
step is to recover computation histories or a joining invariant for those
retained arguments, rather than assume their exact native coverage.

Validation: explicit 787-job build of both affected tracked modules; all 30
public roots (including constructors and recursors) transitively audited through
types, opaque bodies, constructor lists and recursor rules; maximum closure
11,812. Only propext, Classical.choice and Quot.sound; no strengthening,
sorry or configured circular-framework dependency. All 762 local import sources
hash-stable. Artifacts: `/dev/shm/proof-parameter-return-*`, preparation
`/dev/shm/prepare-proof-parameter-return-audit.py`. Executable unchanged; no PRs
extracted and no coordination. The original weakN_iff sorry remains; goal active.


## Caller eta refutes forward histories for retained function arguments (2026-11-04 23:32:42 UTC)

Verdict: the dependent neutral-head/arity theorem cannot be strengthened to
forward histories for every exposed retained argument, even with arbitrary
beta cleanup. In a canonical-Eq environment with a positive empty unindexed
structure S, take old x:S, fresh y:S and K:S->Type. A constant lambda annotated
K x is supplied to a caller H expecting a function annotated K y. Unit equality
makes this application well typed. Eta on H, eta on its newly bound argument,
and beta produce H (fun z:K y => Prop). That endpoint is beta-normal, while
computation of the supplied argument alone cannot introduce the fresh y.
The checked witness rejects every beta-readout argument with such a forward
history, not just the displayed endpoint.

Both original and changed arguments nevertheless compute to the same lambda,
using unit eta to replace x and y by S's registered constructor. This is a
refutation of the proposed argument-origin invariant, not of confluence or
strengthening. Sort-typed payload histories remain unaffected: the obstruction
uses a function-valued parameter. The caller-side eta construction needs no
native recovery of the supplied argument at the caller's selected domain.
A generic no-fresh-index theorem applies to every descending computation.

Validation: two modules, 261 Lean lines, four public roots. Isolated explicit
12-module build succeeded (786 jobs); full 82-root audit includes all changed
imports, maximum dependency closure 11,467, only standard axioms and no forbidden
dependencies. All 761 closure source hashes were stable and matched isolated
copies. Artifacts /tmp/carrier-retained-origin-boundary-*; preparation
/tmp/prepare-carrier-retained-origin-boundary.py. Executable unchanged; no
coordination. Strengthening remains open and the goal remains active.


## Native literal-lambda eta retains its exact selected domain (2026-11-04 23:34:10 UTC)

Verdict: the caller-side annotation obstruction does not occur when eta's
native certificate belongs to the supplied literal lambda itself. Native lambda
inversion starts with its written annotation. Full Pi component extraction
therefore gives a forward computation from that annotation to the exact selected
native domain, with no beta cleanup. The guard may use every finite earlier
structure/function-eta stage; no common-native coverage is assumed.

A native eta step on a retained typed literal lambda consequently meets a path
changing only that annotation. The expanded branch needs only beta, and the
original erased body is retained, including proof-domain eta. This upgrades the
older function-eta residual to the full static structure language and sharpens
its annotation result from a beta join to an exact selected-domain history.
It is a local square, not arbitrary beta/native stability or whole-language
confluence. Caller-side domains still need separate joining evidence.

Validation: one 85-line module, three public roots; isolated explicit 746-job
build; complete dependency audit maximum closure 11,348, standard axioms only
and no configured forbidden dependencies. All 721 closure source hashes were
stable and matched isolated copies. Artifacts /tmp/carrier-static-lambda-residual-*;
preparation /tmp/prepare-carrier-static-lambda-residual.py. Executable unchanged;
no coordination. The strengthening goal remains active.


## Caller canonicalization joins retained singleton parameters (2026-11-04 23:38:36 UTC)

Verdict: a whole-call joining invariant works where individual retained-argument
origins fail. Rechecked the existing caller-eta origin counterexample with a
source-stable build (now commit 3b3f1f99); do not pursue a forward-history law for
arbitrary retained arguments. Its obstruction does not prevent canonicalizing
an argument through the caller's declared binder type.

`static_structure_caller_constant_argument` eta-expands a natively recovered
caller, computes its generic argument to a binder-independent value, and beta
supplies the original argument. The whole application reaches the canonical
application without a native certificate or computation of the supplied value.
A proof-only structure's generic variable reaches its masked constructor; open
parameters, dependent proof fields and empty units are supported. Proof binders
already have the proof marker as their generic eta argument.

`CallerCanonicalTelescope` iterates this construction through dependent domains
instantiated by earlier canonical values. Its computation theorem handles every
raw argument vector of the right length; only the caller and its applications to
canonical values use native recovery. The proof and proof-structure constructors
supply explicit finite computations, not an assumed normalization principle.

Neutral head/arity readout now gives a fixed common target for EVERY full-union
computation from a saturated variable-headed family with such a declared caller
telescope. Lookup supplies the head's native certificate. Arbitrary forks join
at that target, and a common native certificate against the family converts to
the canonical assigned type. A concrete unary theorem discharges the telescope
premise for positive proof-only structures with arbitrary occurrence parameters.
The target is a shared reduct, not a claimed normal form: its parameters may
still compute. No separate argument histories or exact argument coverage occur.

General retained data and function-valued parameters need additional joining
invariants; the canonical telescope does not classify all types. Forward binder
transport at arbitrary noncanonical source types is still open. This proves a
new retained-data case of type-fork joining, not strengthening or a sufficient
strictly smaller front. The original weakN_iff sorry remains; goal active.

Validation: two modules, 244 Lean lines, explicit 751-job build; all 17 public
roots including inductive constructors and recursors audited transitively through
types, opaque bodies, constructors and recursor rules. Maximum closure
11,339; only propext, Classical.choice and Quot.sound, no strengthening,
sorry or configured circular-framework dependency. All 726 local import sources
hash-stable. Artifacts `/dev/shm/caller-canonical-*`; preparation
`/dev/shm/prepare-caller-canonical-audit.py`. Executable unchanged; no PR extraction
or coordination.


## Type beta forks remove native argument demands from conditional application (2026-11-04 23:46:49 UTC)

Verdict: an arbitrary under-binder type computation produces a concrete typed
beta fork after any typed argument is supplied. One branch contracts beta first;
the other computes beneath the lambda and then contracts beta. No primitive
substitution theorem or native argument certificate is used to construct either
path. TypeInstantiationJoin names the remaining joining law explicitly, without
assuming it as a theorem. Type-fork confluence implies it; the existing open
NativeForwardBinder obligation therefore implies it as well.

Given this joining law, common native evidence for a function propagates through
an application with an arbitrary typed argument. Full Pi readout supplies the
original codomain history; the beta fork joins its instantiated output to the
assigned result, and native conversion finishes. The argument needs neither
exact nor common native evidence. The result iterates along arbitrary dependent
literal telescopes. The local theorem requests only the particular codomain's
instantiation law, rather than global type joining.

This removes the exact-argument requirement from the application case under the
already named forward-binder obligation. It does not prove that obligation,
TypeInstantiationJoin, general common-native coverage, or strengthening, and it
is not claimed strictly smaller than PropFront. A further concrete test is
whether exact forward transport of type computations is refuted by using a
fresh converted generic function binder inside a lower-declared neutral caller;
only joining, rather than a forward path, is presently requested here.

Validation: two modules, 196 Lean lines, nine public roots. Combined isolated
five-module 771-job build and complete 22-root audit (including changed imports),
maximum dependency closure 11,493; standard axioms only and no forbidden
dependencies. All 746 closure hashes were stable and matched isolated copies.
Artifacts /tmp/carrier-type-beta-residual-*; preparation
/tmp/prepare-carrier-type-beta-residual.py. No new warnings, executable changes
or coordination. The strengthening goal remains active.


## Variable native coverage is type-conversion joining (2026-11-04 23:47:07 UTC)

Verdict: checked a sharper classification of the common-coverage route. A common
canonical target of a domain's descendants does not directly transport an
arbitrary native body certificate from its original binder to that target:
existing exact image transport needs a reverse domain computation. Substituting
uniform common native coverage for this missing transport has a precise cost.

`NativeVariableCommonCoverage` allows an arbitrary converted assignment at a
variable, not just literal lookup. It is equivalent, under canonical Eq and
sound definitions, to `StaticStructureTypeConversionJoin`: every pair of ordinarily
equal typed types has a common full-union computational target. A retained
variable tests its declared and assigned types; both paths descend through that
fresh test binder. Wrapping arbitrary types as function-to-sort domains retains
the test variable even for propositions, and full Pi component extraction
recovers the original domain join. Conversely, type uniqueness joins a variable's
literal lookup type to its assigned type and supplies common native coverage.

The joining property implies PropositionFront directly: join the lifted
propositions, descend both computations, reflect their common erased syntax,
and compose the lower actual equalities. Consequently variable-only common
coverage already suffices for PropositionFront. No converse from PropositionFront
to this computation-completeness law is asserted. Restricting the source to a
variable is not evidence of a strictly smaller front.

Uniform common native coverage factors exactly into variable common coverage
and bare retained-source native existence. Type equality joins any selected
native type to its assignment. Uniform coverage transports arbitrary native
certificates across actually equal contexts with a forward residual on the
selected output; computed forward-binder transport is a special case. Thus using
coverage to establish that transport leaves type-conversion completeness as an
explicit obligation. None of these open obligations is proved by the reductions.

This changes the next action: separate bare native existence from the equality
conversion case, and do not treat variable coverage as a routine base case or
substitute it silently for forward transport. Canonicalizable caller fragments
remain valid local joining results. General retained-argument joining, full
coverage, strengthening and a sufficient strictly smaller irreducible front are
still open. Original weakN_iff sorry unchanged; goal active.

Validation: two modules, 230 Lean lines, explicit 769-job build; all 14 public
roots (including the four obligation definitions) audited through types, opaque
bodies, constructors and recursor rules. Maximum closure 11,488; only
propext, Classical.choice and Quot.sound, no strengthening, sorry or configured
circular-framework dependency. All 744 local import sources hash-stable. Artifacts
`/dev/shm/variable-coverage-join-*`; preparation
`/dev/shm/prepare-variable-coverage-join-audit.py`. Executable unchanged; no PR
extraction or coordination.


## Nondependent common application without argument recovery (2026-11-04 23:47:08 UTC)

Verdict: proved unconditionally in the full static structure/function-eta union.
A codomain type lifted through an unused binder has a lower computation history
and lower endpoint by certificate descent. Instantiating that endpoint at any
raw argument cancels the lift. Thus the type-instantiation residual is an exact
forward computation in this case, without native images or any confluence law.

Consequently, common native evidence for f:A->B propagates to f x:B for every
typed x:A. A and B may be arbitrary types, and all computed intermediates are
unrestricted. B's well-formedness below the binder follows from the ordinary
application typing, so it is not an additional premise. This closes the entire
nondependent application case of common coverage; the dependent retained case
still requires its explicit beta-instantiation join.

Validation: one 78-line module, three public roots. Combined isolated 771-job
build and full 22-root audit described in the preceding entry; maximum closure
11,493, all 746 source hashes stable and equal to isolated copies. No new warnings,
forbidden dependencies or nonstandard axioms. Artifacts
/tmp/carrier-type-beta-residual-*. Executable unchanged; no coordination.
Strengthening remains open and the goal remains active.


## Exact type computation substitution fails for every descending target (2026-11-04 23:54:05 UTC)

Verdict: refuted the proposed strengthening of TypeInstantiationJoin to an
exact forward computation. The counterexample already has a sort-typed body.
In a canonical-Eq environment with a positive empty unindexed structure S,
declare an old index z:S, K:S->Type, and an old caller H whose function parameter
has domain K z. Add fresh y:S, then a generic function g with converted domain
K y. The type body H g is well typed by unit equality. One native eta expansion
of g computes it to H (fun a:K y => g a).

Substitute the old constant function fun a:K z => Prop for g. The initial type
H (fun a:K z => Prop) is typed below y. The instantiated computed endpoint
beta-reduces to H (fun a:K y => Prop), which retains fresh y in its annotation.
Descent therefore excludes every forward computation between the instantiated
endpoints. The theorem quantifies over every descending primitive relation,
not just the current structure/function-eta union: adding descending rules
cannot repair exact substitution transport. A generic call/lambda annotation
scope lemma supplies the contradiction.

Both instantiated outputs nevertheless compute to the same type by replacing
y and z with S's registered constructor inside the annotations. The witness
therefore preserves the explicitly requested type-instantiation join. It is not
a confluence or strengthening counterexample. This closes the exact-forward
alternative even for type-valued bodies, and directs the next work toward joins
or caller-based repair rather than universal primitive substitution. The already
proved vacuous-codomain case remains valid; this body genuinely uses g.

Validation: one 192-line module, two public roots; isolated explicit 771-job
build and full dependency audit, maximum closure 10,969. Only standard axioms,
no configured forbidden dependencies or new warnings. All 746 closure source
hashes were stable and matched isolated copies. Artifacts
/tmp/carrier-type-inst-boundary-*; preparation
/tmp/prepare-carrier-type-inst-boundary.py. Executable unchanged, no coordination.
The original strengthening sorry remains and the goal remains active.


## Rigid family readout removes the separate native-existence premise (2026-11-05 00:01:03 UTC)

Verdict: proved a conditional reduction, not strengthening. Under canonical Eq
and sound selected definitions that do not unfold registered family heads,
StaticStructureTypeConversionJoin implies StaticStructureNativeExistence and
StaticStructureCommonCoverage. Consequently variable-only common coverage is
equivalent to uniform common coverage. The non-unfolding condition is automatic
for EnvironmentCore.definitions. Thus the previous variable-plus-existence split
has no independent existence obligation once type-conversion joining is given.

The new ingredient is a finite dependent demand observation for a fixed rigid
constant and spine length. Ordinary typed substitution transports demanded
variables; ignored parameters need no native certificates. All stages of the
structure/function-eta union preserve the observation. Rigidness excludes iota,
singleton and computed-Eq heads, while visible control profiles exclude structure
expansion at the observed node. Realizability reads out a beta reduction to the
same constant name with the same arity. Universe instances and arguments may
change. Actual registered families supply their normalized telescope from the
environment; no literal stored declaration shape is assumed.

Join the assigned type with the replayed native type, then use sort, Pi or rigid
family readout. Syntax induction now supplies recovery for every retained term.
For projections, the exposed family's actual typing supplies its constructor
telescope, field index bound and argument count. The proof does not use the
open ScopedSemanticHeadExposure interface or assume coverage to prove existence.

Scope judgment: type-conversion joining remains open and already implies
PropositionFront. This result does not prove a strictly smaller sufficient
obligation, confluence, exact substitution transport, or weakN_iff. Future work
must construct the missing joins rather than treat native existence as an
independent easy premise. Rigid head readout is available unconditionally under
its stated environment assumptions for such joining arguments.

Validation: four new modules, 603 lines, 41 public roots including the observation
constructors and recursors. Explicit 785-job build; full transitive dependency
audit (types, opaque values, constructors and recursor rules), maximum closure
11,860. Only propext, Classical.choice and Quot.sound; no configured
forbidden dependencies or new warnings. All 760 imported-source hashes remained stable.
Artifacts /dev/shm/rigid-native-existence-*. No executable changes or PR extraction.
The original strengthening sorry remains; the goal stays active.

## Generic-variable eta in arbitrary type contexts (2026-11-05)

Verdict: proved conditional contextual function and structure eta without native
certificates for the actual substituted values. TypeInstantiationJoin remains
an explicit open premise. This is progress toward contextual completeness, not
a strengthening proof or a strictly smaller sufficient obligation.

A fresh variable has its exact native declared type. Perform guarded eta on that
variable, propagate the computation through a typed type context using primitive
renaming, then apply TypeInstantiationJoin to substitute the actual value. This
covers function eta, including proposition-valued domains, and every admissible
registered unindexed structure expansion, including retained or erased fields
and arbitrary dependent parameters. Proof values are handled directly by
erasure. Unlike exact substitution transport, refuted in the preceding entry,
this construction requests only a common reduct of the instantiated types.

TypeContextJoin records these observations. Its transitivity follows from fork
joining at typed types: the middle observation C[b] is a type even when b is data.
Existing computational data joins lift through any typed context with no joining
assumption, because only renaming is needed to compute substitution images.
Equal erasures give contextual joins directly. No confluence at data terms or
native certificate for a raw common reduct is assumed by these lemmas.

Remaining boundary: these cases do not establish contextual completeness for
ordinary equality. In particular a pointwise contextual observation of a body
under A does not yet give a join of observations of its enclosing lambda, and
changing a binder domain does not automatically make the same body typable under
a generic replacement domain. Thus the straightforward equality induction still
needs a binder-congruence argument, as well as the remaining primitive cases.
No refutation of that route or claim that type-only fork joining is sufficient
is made. TypeInstantiationJoin itself has not been proved or refuted.

Validation: three modules, 280 lines, ten public roots including the relation
definition. Explicit isolated 773-job build and full transitive audit, maximum
closure 11,056; only propext, Classical.choice and Quot.sound, no configured
forbidden dependencies or new warnings. All 748 closure source hashes remained
stable and matched isolated copies. Artifacts /tmp/carrier-type-context-*;
preparation /tmp/prepare-carrier-type-context.py. Executable unchanged, no
coordination. The original strengthening sorry remains; the goal stays active.


## Repair generic-function eta through the caller's selected domain (2026-11-05 00:09:37 UTC)

Verdict: proved a computational join for the annotation-changing eta/beta peak,
without TypeInstantiationJoin, native coverage of the supplied function, or a
join between the competing annotations. A caller with native type
Pi (Pi A B) C eta-expands any supplied x at A. If its argument has first acquired
an eta wrapper at any other domain L, the same caller expansion followed by
beta contracts the inner wrapper and reaches the identical eta expansion at A.
The proof works both for retained function inputs and erased proof inputs.
The caller's function-argument type must have a nonzero sort; the inner domain
may have sort zero. Matching inner proof-erasure mode is explicit.

The full generic-function eta/beta peak has four checked paths: beta first
produces F x; eta on the bound generic function before beta produces
F (fun y:L => x y); both compute to F (fun y:A => x y). No supplied-argument
native certificate is used. This isolates and closes the annotation discrepancy
in the exact-instantiation counterexample without relying on its unit-structure
assumption or normalizing x. The raw computation theorem is conditional on the
caller's native Pi and the displayed domain-sort witnesses; it is not a claim
that every caller has such a native certificate.

Two typed consequences retain arbitrary lambda bodies, not just constant
functions. The caller can replace the supplied lambda's displayed domain by its
selected domain while preserving its entire erased body. If that body was
originally annotated at the caller's domain, the mismatched eta-expanded branch
returns to the exact original call. Typed proof-erasure stability handles the
proof-input case. These are whole-call computations; no isolated reannotation
path between the function arguments or domains is asserted.

Remaining boundary: arbitrary body computation can alter more than a root eta
wrapper, and arbitrary typed contexts need not expose a caller with the required
native function domain. Full TypeInstantiationJoin, type-conversion joining and
strengthening remain open. This is a solved residual case supporting caller-based
repair, not a strictly smaller sufficient obligation. Next: extend repair across
typed enclosing contexts and changing binders without assuming common coverage.

Validation: one 168-line module, seven public roots. Explicit 743-job build;
full transitive audit through types, opaque values, constructors and recursor
rules, maximum closure 8,358. Only propext, Classical.choice and Quot.sound;
no configured forbidden dependencies or new warnings. All 718 imported-source
hashes remained stable. Artifacts /dev/shm/caller-eta-repair-*.
No executable changes or PR extraction. The original strengthening sorry remains;
the goal stays active.


## Abstract a body to perform function eta below a lambda (2026-11-05 00:20:19 UTC)

Verdict: proved a new binder case for contextual joining, conditional on joining
forks at typed types. For arbitrary dependent A, B, C and f : Pi B C in A::Gamma,
every typed type context joins observations of (fun x:A => f) and
(fun x:A => fun y:B => f y). Neither f nor its enclosing lambda needs a native
certificate. Outer and inner proof domains are both allowed, as are proof
functions. This proves the eta case below one lambda, not general lambda-body
congruence or arbitrary binder-depth completeness.

The construction abstracts over the surrounding binder before substituting.
A fresh generic g : Pi A (Pi B C) has native recovery from its declaration.
Exact native application requires only ordinary typing of the argument, so
under a fresh x:A the term g x recovers Pi B C exactly. Eta first expands g and
then g x, giving a checked computation to the two-lambda generic expansion.
All ordinary typings are retained, and proof-valued sources erase directly.
Substituting the arbitrary original lambda (fun x:A => f) beta-reduces the generic
expansion to (fun x:A => fun y:B => f y); no reduction of f is needed.

A general contextual lemma incorporates that administrative beta cleanup into
the original type-valued beta fork. Generic computation is propagated through
the typed observation using primitive renaming; the actual value is then
substituted on the two fork branches. The computed branch beta-cleans to the
desired observed endpoint. Applying the explicit type-fork joining premise at
the original typed beta-redex yields the join. This avoids assuming exact
substitution of guarded computation or native coverage of the substituted value.

Scope judgment: the previous pointwise TypeContextJoin relation did not by
itself supply lambda congruence. Abstraction gives a concrete way around that
problem for this primitive eta case, rather than postulating congruence. General
body equations, arbitrary binder paths, and the proof of type-fork joining
remain unresolved. No strictly smaller sufficient strengthening obligation or
proof of weakN_iff is claimed. Next: extend the generic abstraction construction
along dependent binder telescopes and test other primitive body equations.

Validation: two new modules, 255 lines, eight public roots. Explicit 775-job
build; full transitive audit through types, opaque values, constructors and
recursor rules, maximum closure 11,073. Only propext, Classical.choice and
Quot.sound; no configured forbidden dependencies or new warnings. All 750
imported-source hashes remained stable. Artifacts /dev/shm/generic-binder-eta-*.
No executable changes, coordination or PR extraction. The original strengthening
sorry remains and the goal stays active.

## Type-only forks align Pi binders and type instantiation (2026-11-05)

Verdict: proved conditional forward binder transport up to joining for type
computations, dependent Pi congruence, lambda reannotation, type-valued lambda
congruence, and instantiation of type joins. All use the explicit open
TypeForkJoin premise. They do not prove confluence, contextual completeness,
strengthening, or a strictly smaller sufficient obligation.

A literal lambda assigned Pi A B can be changed to the annotation A inside any
typed type context: generic eta supplies the chosen domain, beta restores the
entire body, and a type-rooted fork composes the two joins. Ordinary typing of
the original lambda suffices; the reannotated lambda's typing is derived. There
is no native certificate or separate computational domain-join premise. For
type-valued lambda bodies, contextual body comparison yields a direct body join
via the identity type context. This closes contextual congruence for those
lambdas even when their written annotations differ.

The deeper binder step packages a type computation C -> out under A together
with a domain computation A -> B into a fork at Pi A C. The branches have the
same new domain B and respective codomains C and out. TypeForkJoin joins them;
full Pi readout then extracts a codomain join in the B context. Thus forward
transport of type computation is available up to a join, although exact forward
transport of arbitrary native evidence remains open. Realizing a raw middle
endpoint as a typed type allows two such transported joins to compose.

For dependent Pi congruence, realize a common domain reduct E, transport the
codomain join from A to E, then pull the two resulting paths back along A -> E
and A' -> E. Compatible Pi computation reaches the same Pi E sharedB on both
sides. The original codomain join is required only in the A context. Consequently
the ordinary forallEDF case closes from contextual induction premises for its
domain and codomain under TypeForkJoin; no native coverage is assumed.

Type joins also survive arbitrary typed instantiation: apply TypeInstantiationJoin
(which follows from TypeForkJoin) to each branch, realize the common body's raw
output as a type, and join the two computations from its instance. Combining this
with the contextual observation of two data arguments gives simultaneous
substitution of distinct compared arguments into distinct compared type bodies.
The argument needs no native certificate, and only types are fork roots.

Remaining boundary: arbitrary data-valued lambda bodies still need a binder
congruence argument. A contextual comparison of a data body does not directly
supply a computational join under its binder. Dependent application also remains:
a body whose result is a type only at a particular argument is not automatically
a type-valued template at a generic argument. The new instantiation theorem does
not erase that distinction. The remaining primitive cases and TypeForkJoin itself
are still open. These are live proof obligations, not refutations of the route.

Validation: four new modules, 343 lines, eleven public roots including the open
premise definition. Two explicit isolated 776-job builds; full transitive audits
of nine and two roots, maximum closure 11,488. Only propext, Classical.choice and
Quot.sound, no configured forbidden dependencies or new warnings. All 752 sources
in the combined dependency closures remained hash-stable and matched isolated
copies. Artifacts /tmp/carrier-type-fork-binder-* and /tmp/carrier-type-fork-inst-*;
preparation /tmp/prepare-carrier-type-fork-binder.py and
/tmp/prepare-carrier-type-fork-inst.py. Executable unchanged, no coordination.
The original strengthening sorry remains and the goal stays active.


## Generic eta at arbitrary dependent binder depth (2026-11-05 00:28:51 UTC)

Verdict: generalized the preceding one-lambda construction to every finite
dependent lambda telescope. Under the explicit type-only fork-joining premise,
all typed type contexts join observations of wrapLams ds f and
wrapLams ds (fun x:A => f x), whenever f : Pi A B in ds.reverse ++ Gamma.
No native certificate for f or its enclosing abstraction is assumed. The prefix
length is unrestricted; domains may depend on all preceding binders, proof
domains are allowed, and proof-valued functions are included. A companion theorem
joins every ordinary finite dependent eta expansion of an arbitrary typed
function in every typed type context.

The native part is unconditional under canonical Eq and sound definitions:
exact assigned recovery weakens, application retains exact recovery using only
ordinary argument typing, and induction opens the entire displayed telescope.
A fresh generic function therefore supplies all native guards before the actual
function is substituted. The actual terms are typed with the existing ordinary
eta-opening metatheory. There is no recursive assumption of native coverage or
an argument-normalization hypothesis.

The syntax part proves finite administrative beta cleanup independently of
typing. Instantiating the shifted generic telescope restores its original
annotations and eta-opens the supplied function. Opening a supplied lambda
prefix cancels that entire prefix, leaving the arbitrary body untouched. Opening
one additional binder yields eta of that body. Lifting and closing beta paths
then give the required cleanup at arbitrary depth. These lemmas inspect neither
the residual body nor its termination behavior.

The type-valued beta-fork construction from the preceding turn uses this generic
computation and cleanup inside arbitrary typed observations. Thus the proof has
no fixed binder-depth bound and no additional joining premise beyond type forks.
Scope judgment: this solves the function-eta case beneath arbitrary dependent
lambda prefixes, not general congruence for data-valued lambda bodies or arbitrary
dependent term templates. TypeForkJoin itself and the original strengthening
problem remain open. No strictly smaller sufficient obligation is claimed.
Next: use the generic telescope to handle other primitive equations, while
checking that any enclosing template really admits the generic replacement.

Validation: three new modules, 312 lines, 18 public roots. Explicit 778-job
build; full transitive audit through types, opaque values, constructors and
recursor rules, maximum closure 11,089. Only propext, Classical.choice and
Quot.sound; no configured forbidden dependencies or new warnings. All 753
imported-source hashes remained stable. Artifacts /dev/shm/contextual-eta-telescope-*.
No executable changes, coordination or PR extraction. The original strengthening
sorry remains and the goal stays active.


## Structure eta beneath every dependent lambda telescope (2026-11-05 00:35:37 UTC)

Verdict: closed the structure-eta primitive beneath arbitrary finite dependent
lambda prefixes, conditional on the existing TypeForkJoin premise. The public
TypeForkJoin.contextual_structure_eta_under_telescope theorem observes
wrapLams ds m and wrapLams ds (structExpand family info ls ps m) in every typed
type context. The structure parameters may depend on every prefix binder;
proof domains, proof majors, proof-valued abstractions and mixed retained/proof
fields are included. Neither the original major nor its whole abstraction needs
native recovery. Admissibility comes from the actual expansion's ordinary typing,
not a stronger universe assumption or a separate coverage hypothesis.

The native construction first opens the declared function telescope with fresh
variables. Exact assigned recovery weakens and survives each application using
only ordinary argument typing. At the terminal family, exact recovery supplies
the structure-expansion guard. Ordinary telescope eta and structure eta type the
result. This gives a computation of a fresh generic function into its fully
opened and structure-expanded body, before any actual abstraction is substituted.

The syntax layer proves that beta reduction of a major passes through all its
projected fields. Instantiating the generic telescope restores the dependent
domains and parameters exactly. Supplying wrapLams ds m contracts only the
administrative applications introduced by opening that displayed prefix; no
normalization or reduction of m or the parameters is required. The established
generic type-context beta fork then joins observations of the actual two sides.

Scope judgment: this removes another primitive case under unbounded lambda
depth, following the preceding function-eta construction. It does not establish
arbitrary data-valued lambda-body congruence, general dependent term-template
congruence, or TypeForkJoin. It is not a proof of strengthening or a newly proved
strictly smaller sufficient obligation. The original UniqueTyping.weakN_iff sorry
remains. Next: address typed enclosing templates and general body congruence;
reuse this terminal-major construction rather than assume native recovery of
actual substituted values.

Validation: three new modules, 241 lines, eight public roots. Explicit 781-job
build; full transitive dependency audit through types, opaque values, constructor
lists and recursor rules, maximum closure 11,098. Only propext,
Classical.choice and Quot.sound; no configured forbidden dependencies or new
warnings. All 756 local imported-source hashes remained stable. Artifacts
/dev/shm/contextual-structure-telescope-*. Independent untracked work was
preserved. No executable changes, coordination or PR extraction; goal active.

## Contextual application cases and observed data-instantiation forks (2026-11-05)

Verdict: proved more contextual equality cases and removed the generic-type-body
restriction from contextual instantiation of computational joins. TypeForkJoin
remains an open premise wherever joins must compose. No strengthening proof,
confluence proof, or strictly smaller sufficient obligation is claimed.

Composing type observers with a typed template of fixed result type preserves
TypeContextJoin without confluence or native coverage. This proves function-side
congruence for dependent application, argument-side congruence for nondependent
application, and both-sided nondependent congruence under type-only fork joining.
A raw computational argument join also lifts through dependent application:
ordinary equality synchronizes the actual result assignments and proof erasure.
Hence type arguments are covered by extracting their join with the identity
observer, including converted assignments whose domains are not literal sorts.
Proof arguments are covered by their common erasure. Ordinary assigned-type
conversion, proof irrelevance, and arbitrary typed beta paths are also covered.

The generic-type-body restriction really cannot be inferred from an instance:
in the well-formed context f : (X : Type) -> X, the actual application f Prop is
a proposition, while f X under fresh X : Type has no sort typing at any level.
The checked contradiction uses uniqueness, substitutes a Pi type for X, and
applies sort/Pi separation. It holds in every well-formed environment, hence
also with canonical Eq. This refutes only that inference, not application
congruence. In fact the positive type-argument lemma covers this example.

The boundary led to a stronger construction. Every computation of an arbitrary
typed body e under A supplies two paths from (fun z:A => e) x: beta first reaches
e[x], while computing the body first reaches the raw computed output instantiated
at erased x. For proof bodies, source-typed replay proves that the output remains
the proof marker; retained bodies use the explicit compatible lambda/beta paths.
No native argument certificate or substitution transport of guards is required.

Observe that beta redex in an actual typed type context C over E[x]. Its entire
observation is a type, even if e has a genuinely dependent data type E in the
generic context. TypeForkJoin therefore joins the two observed branches. A
common raw body output can be realized as a same-typed actual body, and a second
observed type fork composes the joins. Consequently any computational join of
same-typed data bodies survives arbitrary typed instantiation in every type
observer. This strictly broadens the earlier lemma's body-typing scope; it is
not a claim of a strictly smaller sufficient strengthening obligation.

Remaining boundary: a merely contextual comparison of retained data arguments
still does not supply the raw join used by the general dependent-application
lemma. Arbitrary data-valued lambda-body congruence, the remaining primitive
cases and TypeForkJoin itself remain open. The new instantiation result does
not assume that an arbitrary enclosing generic term template is well typed.

Live next angle: use typed chains of forward and backward computations as the
induction relation for ordinary equality. Generic identity beta wrappers give
native guards and common computational ancestors for eta; compatible steps may
then lift through actual typed terms without genericizing their entire observer.
Dependent application can retag each intermediate result by ordinary conversion.
Only the final type-valued chain would need fork joining. Primitive completeness
and the dependent congruence proofs for this chain relation still need checking;
this paragraph records a live proof strategy, not a proved reduction.

Validation: four new modules, 385 lines, sixteen public roots. Two explicit
isolated 777-job builds and full transitive audits of thirteen and three roots;
maximum closure 11,057. Only propext, Classical.choice and Quot.sound, no
configured forbidden dependencies or new warnings. All 753 sources in the
combined closures remained hash-stable and matched isolated copies. Artifacts
/tmp/carrier-type-context-app-* and /tmp/carrier-contextual-inst-fork-*;
preparation scripts use the corresponding /tmp/prepare-carrier-*.py names.
Executable unchanged, no coordination. The original strengthening sorry remains
and the goal stays active.


## Simultaneous telescope annotations through a typed common ancestor (2026-11-05 00:42:15 UTC)

Verdict: all written domains of a dependent lambda telescope can be replaced
simultaneously by the domains of its assigned Pi telescope, preserving the exact
residual body. Only whole-term typing and equal telescope lengths are required.
The two domain lists need not coincide at any position; no pointwise domain join,
native recovery of the abstraction/body, or separately transported body typing is
assumed. Eta opening followed by administrative beta establishes ordinary typing
and equality of the reannotated target. This works at arbitrary finite depth.

The stronger operational result is an explicit common computational ancestor:
(fun g : wrapForalls ds T => g) (wrapLams written b). Beta first reaches the
original abstraction. Generic telescope eta before instantiation, followed by
administrative beta, reaches wrapLams ds b. Every guard is supplied while g is
fresh; the actual abstraction needs no native certificate. The committed general
data-instantiation peak handles proof-valued functions as well as retained ones.
This fork does not assume TypeForkJoin or any other confluence premise.

Observing that typed common ancestor in a type context creates a type-valued
fork. TypeForkJoin then joins the observations of the original and reannotated
abstractions. Consequently two same-body lambda telescopes with different written
annotations but the same assigned Pi telescope join in every type observer.
The common intermediate uses the assigned domains and its typing is derived.
This removes simultaneous domain alignment from this binder comparison; arbitrary
different data bodies still need a congruence argument. No stronger completeness
or strictly smaller sufficient strengthening obligation is claimed.

Investigated canonical Eq as a classifying observation for contextual data.
The available full-union rigid-head readout returns the family name and arity,
but deliberately allows arbitrary exposed arguments. It therefore does not yet
extract the data computational join needed for arbitrary body congruence. That
argument-readout idea remains unproved, not refuted. A live alternative, recorded
in the newly committed instantiation work, is a typed chain of forward/backward
computations whose primitive eta cases use common ancestors. The concrete fork
proved here supports that approach without presuming its completeness.

Validation: one module, 120 lines, five public roots. Explicit 783-job build;
full transitive audits through types, opaque values, constructors and recursor
rules, maximum closure 11,091. Only propext, Classical.choice and Quot.sound;
no configured forbidden dependencies or new warnings. All 758 local imported
source hashes remained stable. Artifacts /dev/shm/contextual-telescope-annotations-*.
Independent untracked work preserved; no executable changes, coordination or PR
extraction. The original strengthening sorry remains and GOAL.md stays active.

## Typed computation chains close dependent congruence (2026-11-05)

Verdict: the chain strategy from the preceding entry is productive. A new typed
relation generated by erased forward computations, symmetry and transitivity
supports arbitrary typed instantiation, full dependent application congruence,
full lambda and Pi congruence, function eta, structure eta and unit-like equality.
These closure and eta results do not assume TypeForkJoin or native coverage of
actual values. Ordinary-equality completeness for the relation is still open.
This is not a strengthening proof or a strictly smaller sufficient obligation.

Each generating edge requires an actual forward computation and an ordinary
same-typed equation. The latter records soundness and types of intermediate
terms; it is not a rule admitting arbitrary ordinary equations. A checked
source-typed replay lemma reconstructs that equation from two actual same-typed
endpoints and their computation. Thus storing it adds no completeness premise.
Assigned-type conversion retags the whole chain. Beta and equal erasures give
edges directly, including the proof-irrelevance case.

Instantiation replaces each edge under A by the two branches of its typed beta
fork. Traverse beta backward from the original instance to the redex, then take
the computed-body branch to the second instance. This gives another finite typed
chain, without substituting native guards or asking that the two branches join.
It includes arbitrary dependent data bodies, proof bodies and non-native actual
arguments. This is the point at which allowing backward edges removes the earlier
exact-substitution obstruction without asserting a false forward path.

Dependent application is now fully compatible. Symmetry and transitivity in an
argument chain change the displayed codomain instance; ordinary codomain
instantiation equality retags each intermediate result at the original result
type. Function chains lift at a fixed argument. No fixed-result generic template,
data confluence, or argument classification as proof/type is needed. Lambda
body chains run under the original domain; annotation chains use ordinary context
equality to identify the unchanged body's erasure. Retagging intermediate Pi
assignments handles reverse and composite domain steps. The same construction
proves dependent Pi congruence. These results close the congruence difficulty for
this stronger chain relation, not for an arbitrary TypeContextJoin hypothesis.

Function eta is a forward native step on a generic variable followed by chain
instantiation at the actual function. Structure eta uses the committed generic
structure-telescope computation in the same way, including arbitrary dependent
prefixes, open parameters, retained/proof fields and proof majors. Empty-structure
equality composes the two structure-eta chains through the registered constructor.
No native certificate for the actual function or structure major is assumed.

TypeForkJoin has one clearly separated use: it interprets any such data chain as
TypeContextJoin by composing its observed type joins. At sort-typed endpoints the
identity observer yields an actual common reduct. The relation's completeness
for ordinary IsDefEq has not been proved. Next cases to discharge are projection
congruence, universe conversion/declarations, and registered pattern/projection
computation, especially aligning checked pattern arguments via typed chains.
Even a completeness proof would still leave TypeForkJoin itself open; no circular
use of the conditional interpretation is permitted in the closure proofs.

Validation: five new modules, 446 lines, 39 public roots counting generated
constructors and recursors. Eleven explicit isolated targets also include six
newly copied committed imports; 788-job build and full transitive audit of all
70 roots, maximum closure 11,099. Only propext, Classical.choice and Quot.sound;
no configured forbidden dependencies or new warnings. All 763 closure source
hashes stayed stable and matched isolated copies. Artifacts
/tmp/carrier-typed-computation-*; preparation /tmp/prepare-carrier-typed-computation.py
retains all eleven targets and enumerated generated declarations. Executable
unchanged, no coordination. The original strengthening sorry remains and the
goal stays active.


## Telescope congruence and full context conversion for typed chains (2026-11-05 00:51:49 UTC)

Verdict: typed computation equality now closes arbitrary finite dependent lambda
prefixes and is invariant under full ordinary dependent-context conversion. No
TypeForkJoin, native coverage, exact forward binder transport, or strengthening
premise is used for these closure theorems. They apply to retained data bodies
as well as types and proofs. The separate interpretation as contextual joins
continues to require TypeForkJoin.

The telescope reannotation common ancestor from the preceding turn becomes a
typed chain. Lambda congruence can consequently change its domain by ordinary
equality alone, without requiring a domain computation chain. Closing a body
chain under a fixed prefix is an induction on the prefix. Combining closure
with reannotation on both sides compares arbitrary different bodies under
independently written telescopes at the same assigned Pi telescope. The assigned
context's well-formedness follows from whole-term typing, and no separate native
certificate or transported body typing is required. TypeForkJoin then interprets
this chain as a join in every type observer. This does not assume that arbitrary
TypeContextJoin hypotheses themselves have lambda congruence.

Binder transport uses a different operation from forward native transport.
Abstract the body chain under its original domain, convert its function type to
the equal new domain, weaken it into the new context, and apply it to the fresh
variable. Administrative beta on both endpoints returns the unchanged body
syntax at the unchanged assigned type. Exact variable renaming supplies the only
primitive transport. Individual forward paths may become chains with backward
segments; no false forward-context law is asserted.

Opening a chain between literal lambda telescopes similarly applies successive
fresh variables and beta-cleans the displayed prefix. This lets a declaration
change at arbitrary depth: close the intervening prefix, change the declaration,
then reopen. Finally, induction on IsDefEqCtx closes each head binder, transports
the outer function chain along the tail conversion, reopens, and changes the
head declaration. The resulting defeqCtx theorem and its iff retain identical
term and assignment syntax in either definitionally equal context.

Scope judgment: the stronger chain relation now has the dependent binder and
context operations needed by a completeness proof. Ordinary IsDefEq completeness
is still unproved; the remaining registered primitive cases and TypeForkJoin
itself remain live obligations. The original strengthening sorry remains, and
no proof or strictly smaller sufficient strengthening obligation is claimed.
Next: complete the ordinary equality induction using the primitive chains, then
identify exactly what still has to be joined at type roots.

Validation: two new modules, 250 lines, eleven public roots. Explicit 788-job
build; full transitive audits through types, opaque values, constructor lists and
recursor rules, maximum closure 11,102. Only propext, Classical.choice and
Quot.sound; no configured forbidden dependencies or new warnings. All 763 local
imported-source hashes remained stable. Artifacts /dev/shm/typed-binder-transport-*.
Only these modules and the EOF ledger appendices are staged; independent work
is preserved. No executable changes, coordination or PR extraction; goal active.


## Arbitrary paired substitution for typed computation chains (2026-11-05 00:56:37 UTC)

Verdict: typed computation equality now supports arbitrary simultaneous typed
substitution, including two different maps whose corresponding images are related
by typed computation chains. No native recovery, common image reduct, fork joining,
or ordinary-equality completeness assumption is required. The two maps may differ
at every dependent source declaration, including retained data and proof images.
The existing Ctx.SubstEq witness records ordinary typing of the related maps;
lookup-indexed chain witnesses provide their computational content.

The proof inducts on the source context, not on native certificates. At a cons,
close the source chain under its head domain, recursively substitute the two tail
maps into that function chain, and apply the related head images. Dependent
application keeps the common left-hand result assignment. Beta contraction on
both endpoints identifies the results with the original simultaneous substitutions.
The nil case weakens the closed chain into the target context; closedness makes
both arbitrary maps irrelevant. This transports finite chains even where exact
forward substitution of an enriched primitive was previously refuted.

Ordinary one-map substitution follows because every image has a reflexive chain
at its lookup type. An InstN corollary handles replacement at arbitrary binder
depth, with the actual dependent target context provided by its typed witness.
A separate instDF theorem changes both body and argument at once by dependent
application of the abstracted body chain; it needs no extra canonical-Eq or
soundness premises beyond those already embodied by the supplied chains.

The raw-output bridge starts from any actual typed full-union computation.
Source-typed replay supplies a typed representative of its initially raw output,
and general substitution relates all actual instances of the source and that
representative by a chain. It does not claim a forward path to the substituted
raw output or preserve an original guard certificate.

Scope judgment: this supplies the simultaneous substitution interface for the
remaining registered primitive cases of chain completeness. It does not itself
prove that every ordinary IsDefEq has a chain, nor does it establish TypeForkJoin.
No strictly smaller sufficient strengthening obligation is claimed; the original
weakN_iff sorry remains. Next: use related typed capture maps in the remaining
primitive cases, then separate chain completeness from type-rooted joining.

Validation: one new module, 110 lines, five public roots. Explicit 789-job build;
full transitive audits through types, opaque values, constructors and recursor
rules, maximum closure 11,069. Only propext, Classical.choice and Quot.sound;
no configured forbidden dependencies or new warnings. All 764 local imported
source hashes remained stable. Artifacts /dev/shm/typed-substitution-*. Independent
work preserved. No executable changes, coordination or PR extraction; goal active.


### 2026-11-05 — Ordinary constructor coverage for typed computation chains

Verdict: verified progress. Five modules (370 lines) cover projection congruence,
projection selection, sort/constant universe conversion, selected delta, concrete
pattern traces, quotient prefixes, and every stored declaration. Projection
saturation is derived from actual major typing. Proposition-source quotient
applications unfold the repaired prefix, beta-contract, and identify the extracted
inhabitant with the constructor payload by proof irrelevance; lambda-telescope
congruence closes the full stored quotient equation. Nonzero quotient sources use
the registered pattern trace. No fork-joining premise occurs in these constructions.

The conditional ordinary-equality completeness theorem now has one missing
constructor interface, TypedPatternChainClosure. It receives chains for realized
checks, without building ordinary completeness into the chain relation. Together
with the still-open TypeForkJoin, it yields common erased reducts of type equalities.
This is an intermediate interface, not a strictly smaller sufficient strengthening
obligation. Neither the canonical-Eq strengthening theorem nor confluence is proved.

Further inspection sharpens the next task: WF.pats_true shows that the actual
stored recursor patterns have empty checks. WF.pats_guarded separates the enabled
ordinary core from large-target elimination at zero source level. Thus arbitrary
checked-capture alignment is not the immediate raw-pattern residue; the remaining
work is the proposition-source singleton case and the typing equalities needed to
license its erased guarded computation. Next isolate that case, then establish its
chain coverage without assuming type-fork joining.

Validation: isolated builds of seven modules/27 public roots (including three
newly copied committed telescope dependencies), followed by completeness/three
roots; 797 and 798 jobs. Full transitive audits include declaration types, opaque
values, generated constructor/recursor dependencies and recursor RHSs. Maximum
closure 11,538; only propext, Classical.choice, Quot.sound; no configured forbidden
dependencies, sorry sources, or new-module warnings. All 772/773 closure source
hashes stayed stable and matched isolated copies. Artifacts:
/tmp/carrier-typed-primitives-* and /tmp/carrier-typed-completeness-*.
Independent work preserved; executable unchanged; original sorry remains; goal active.


## Closed inhabited proposition forks retain all type forks (2026-11-05 01:05:28 UTC)

Verdict: checked an exact equivalence between TypeForkJoin and fork joining
restricted to closed inhabited propositions. Closed here means an empty term
context; the ambient universe parameters are unchanged. Thus restricting the
source to propositions, requiring an explicit inhabitant, and removing all free
term variables still retains the complete type-fork obligation. This is a
boundary result for the proposed restriction, not confluence or a strictly
smaller sufficient strengthening obligation.

First, a join of two Pis with the same original domain yields a join of their
codomains in the original binder context. Marked full-union Pi origin supplies
one literal Pi endpoint after finite beta cleanup. Exact Pi components on the
other branch recover the second codomain history at that same endpoint. Neither
source annotations nor the exposed common domain must remain unchanged.

Second, proposition fork joining in Gamma implies the same property in A::Gamma.
Realize each raw proposition output, close the fork as forall A P, and close the
supplied proof by lambda abstraction. Impredicativity makes the whole wrapper a
proposition, and the closed proof does not require an inhabitant of A. Apply the
assumed joining in Gamma and read the two codomain histories back out. Induction
on the ambient context therefore derives all inhabited-proposition forks from
closed inhabited-proposition forks.

Finally, any type T embeds as the domain of forall _:T, truth, where truth is the
closed proposition forall P:Prop, P -> P with its literal identity proof. The two
T-computations give a fork of this inhabited proposition. Ordinary context
conversion identifies the unchanged truth body's erasure at changed domains.
Pi readout recovers the original domain join. The construction requires neither
T nor Gamma to be inhabited. Combining the two reductions gives the equivalence
for the full structure/function-eta union, under canonical Eq and sound D.

Joining investigation: deriving coverage from type joins and then using coverage
to obtain joins is still circular. A prospective local binder argument would
need to handle the native application case, where a changed recovered Pi brings
an instantiated codomain computation at an arbitrary, potentially non-native
argument. The present results do not bound that new joining obligation by the
changed domain's syntax. This local argument remains unproved. The closed-root
restriction cannot itself remove it, as the new equivalence demonstrates.

Validation: one module, 177 lines, seven public roots including the two explicit
open-property definitions. Explicit 775-job build; full transitive audits
through types, opaque values, constructors and recursor rules, maximum closure
11,489. Only propext, Classical.choice and Quot.sound; no configured forbidden
dependencies or new warnings. All 750 local imported-source hashes remained
stable. Artifacts /dev/shm/closed-prop-forks-*. Independent work preserved; no
executable changes, coordination or PR extraction. The original strengthening
sorry remains and GOAL.md stays active.


### 2026-11-05 — Singleton residue and concrete prefix-chain coverage

Verdict: verified progress, not a strengthening deliverable. The actual stored
patterns have empty checks. TypedComputationEq.pattern_nonzero covers every
registered pattern outside large-target elimination at zero source level using
its guarded core registration. TypedSingletonPatternChainClosure now names
exactly the exceptional raw-pattern case; it implies the earlier pattern
interface and hence ordinary chain completeness. The condition still needs proof.

Canonical Eq prefixes now accept arbitrary typed computation chains between
their data endpoints. Dependent application first changes the final endpoint to
make the guard reflexive; the stage-one prefix computes; ordinary lambda-domain
alignment restores the original proof annotation at the original assigned type.
Applying this chain to any actual, possibly opaque, proof major and beta-contracting
yields the minor. No raw join, native endpoint recovery, or TypeForkJoin is used.
This verifies the proposed strategy of moving checked arguments by chains before
using a reflexive guard, for canonical Eq rather than for all singleton families.

For unindexed singleton code, transported_family_unindexed proves syntactic
identity of the transported and requested families. Valid.unindexed_guard therefore
supplies a reflexive recovered-carrier guard at every stage. The generated prefix
has a chain from registration, generation and source typing alone; all code/layout
certificates and the actual unfolding check are derived. This stays in the existing
full union and adds no closed equations to the definition collection. Dependent
residual telescopes and proof-valued whole prefixes are included.

Scope judgment: generated-prefix coverage does not yet establish coverage of all
raw singleton pattern equations. The remaining bridge must connect actual literal
constructor instances and their captured fields to the prefix output; the general
indexed case must also supply the family alignment through chains. Investigate the
existing SingletonCoverage extraction/typed-spine alignment proof and use paired
chain substitution for the resulting captures. TypeForkJoin remains independently
open. Neither a canonical-Eq proof/counterexample nor a genuinely smaller sufficient
irreducible strengthening obligation has been obtained; original sorry remains.

Validation: three modules, 246 lines, eleven public roots. Two-module/seven-root
isolated build (800 jobs), then one-module/four-root build (799 jobs). Full transitive
audits through types, opaque values, constructors and recursor rules; maximum
closure 11,583. Only propext, Classical.choice and Quot.sound; no configured
forbidden dependencies, sorry sources, or new-module warnings. All 775/774 closure
source hashes were stable and byte-identical to isolated copies. Artifacts:
/tmp/carrier-typed-singleton-* and /tmp/carrier-typed-unindexed-*.
Independent work preserved; no executable changes or coordination; goal active.


## Native recovery coherence and first-stage expansion overlaps (2026-11-05 01:22:06 UTC)

Verdict: proved coherence of every native recovery over the universe-extended
ordinary core at the same typed source. The earlier result covered variable and
constant application spines. The new theorem covers all syntax, including
lambdas, Pis and dependent projections, without a native premise on arguments.
Mixed guard relations inherit coherence whenever their typed paths have common
level-core reducts. This is a checked critical-pair advance, not strengthening
or a strictly smaller sufficient irreducible obligation.

The projection case follows the complete selected field recipe. Factor the
family path into ordinary computation and structural universe variation, carry
all parameter computations through the recipe, and use the actual target native
projection to justify the final universe conversion. Preceding-field captures
and dependent telescope domains remain present. Native output conversion is
composed only at replayed typed intermediate types. Pi-source outputs are sorts;
ordinary uniqueness supplies equivalent levels rather than assuming literal
universe equality.

Two applications close same-source expansion overlaps. Function eta now joins
for arbitrary short sources, including projections and lambda-headed terms.
Structure eta now joins arbitrary selected parameter vectors: native coherence
joins the families, rigid spine readout recovers the parameter paths, and the
universe/mask theorem joins the expanded constructors. These results permit
mixed proof/data fields and differing universe instances. Concrete theorems for
actual stored environments discharge the core hypotheses for both overlaps at
the first guarded stage, whose guards include ordinary computation, universe
conversion and constant beta expansion.

The proposed stage induction remains open. These theorems handle two eta roots
or two structure roots, not an expansion against an arbitrary contextual path,
beta substitution at non-native arguments, or all higher guarded stages. In
particular, neutral eta paths cannot simply be assumed level-core joinable to
invoke the mixed-guard theorem recursively. No global confluence, native
coverage, or TypeForkJoin premise is used to prove the new overlap cases.

Validation: one module, eight public roots; isolated 770-job build against
committed dependency sources, with full transitive declaration audits through
types, opaque values, constructors and recursor rules (maximum 11,520).
Only propext, Classical.choice and Quot.sound; no configured forbidden
dependencies or new-module warnings. Dependency source hashes checked against
the committed tree before committing. Artifacts /dev/shm/native-level-coherence-*.
Independent work preserved; no executable changes, coordination or PR extraction.
The original strengthening sorry remains and GOAL.md stays active.


### 2026-11-05 — Singleton equation extraction interpreted by typed chains

Verdict: verified progress. NormalEqN (both comparison modes) and NormalEqF now
produce typed computation chains. This includes universe changes, dependent Pi
congruence, projections, proof irrelevance and all eta forms. Lambda annotations
use the generic eta reannotation construction; Pi bodies move through ordinary
context conversion by the already proved binder transport. No type-fork joining
or ordinary-equality completeness premise is used.

Refactored RecursorRegistered.zero_join into zero_join_via_prefix plus its
original full-reduction specialization, preserving the original theorem signature.
The generalized proof exposes exactly its actual operational ingredients: the
selected recursor's own prefix at the fixed universe list, beta, application,
reflexivity/transitivity and closing lambda telescopes. The 450-line extraction
and field-normal-comparison argument is reused once, not copied. Ordinary
FullReduction still supplies an internal subject-reduction fact, independently
of the relation chosen to realize the trace. Existing downstream proofs rebuilt.

TypedComputationTrace interprets those operations at every actual source
assignment. The bridge singleton_equation_of_prefix composes the resulting
trace with the normal comparison at the original stored assignment. Combining
it with generated_unindexed_prefix proves unindexed_singleton_equation: every
registered, well-typed, unindexed proposition-source singleton equation has a
chain, with no remaining prefix-coverage or joining assumption. This is coverage
of the full lambda-wrapped equation, beyond the previous generated-prefix result.

The application interface acts on arbitrary dependent argument spines using
whole-source typing. apply_equation_at_proof_major additionally proves that a
typed right-hand equation instance connects to an actual source application if
the left instance beta-reduces to the same function prefix with another proof
major. Right-instance typing supplies the left instance; common function-domain
typing and proof irrelevance align the majors. Constructor parameter syntax and
constructor universe syntax need not be compared in this bridge.

Remaining scope: actual raw singleton pattern matches still need alignment with
these equation instances. For the unindexed case, establish the syntactic beta
shape with the original recursor argument prefix, then use the proof-major bridge;
WF.singletonPatCoverageJ already obtains right-instance typing from the pattern
reduct. This should avoid the general indexed HasTypeJ/spine-joining detour, but
that syntactic specialization has not yet been proved. For indexed singleton
code, investigate forward computation of transported fields at literal constructor
indices: data slots are literal fields and proof slots erase; recursive cast-type
alignment may follow by typed template computation. General singleton coverage
and TypeForkJoin remain open. No strictly smaller sufficient strengthening
obligation, canonical-Eq proof or counterexample is claimed; original sorry remains.

Validation: two new modules (76 and 156 lines), plus a 46-addition/7-deletion
refactor of SingletonCoverage. Explicit isolated 802-job build; all 48 public
roots audited across four modules, including all 28 roots of the modified legacy
module and six binder-transport roots. Full transitive types, opaque values,
constructors and recursor RHS audit; maximum closure 11,257. Only propext,
Classical.choice, Quot.sound; no configured forbidden dependencies, sorry sources
or audited-module warnings. All 777 closure source hashes remained stable and
byte-identical to isolated copies. Artifacts /tmp/carrier-typed-equation-*.
Independent work preserved; executable unchanged; no coordination; goal active.

### 2026-11-05: actual unindexed singleton pattern coverage — proved

Verdict: the remaining unindexed equation-instance alignment is now discharged.
`singletonInstance_unindexed_beta` derives the rule counts from the registered
compilation and its stored equation, then beta-reduces the left equation at the
actual captures to the original recursor prefix applied to a reconstructed major.
There is no comparison of constructor parameters or constructor universe syntax.
`registered_major_isProof` obtains the original major's proposition typing from
the restored family head and the zero source universe. Combining these with the
full equation chain and right-instance typing proves
`TypedComputationEq.unindexed_singleton_pattern` in the presentation selecting
the actual environment registry. No HasTypeJ, earlier-stage type joins, prefix
coverage assumption, or computational confluence premise is used.

`TypedIndexedSingletonPatternChainClosure` records the remaining raw pattern
case with a nonempty index telescope. Its `singleton_closure` discharges every
unindexed branch using the new proof; ordinary chain completeness therefore now
needs only indexed singleton coverage. This is an intermediate narrowing of one
component, not a strictly smaller sufficient strengthening obligation. Indexed
singleton coverage and TypeForkJoin remain open, and the original sorry remains.

Next live route: specialize transported-field computation to literal constructor
indices, using typed computation of Eq casts and proof irrelevance for extracted
proof fields. A direct appeal to ordinary conversion for arbitrary indexed
families would be circular; the proposed argument must build the field chains.

Validation: two new modules, six public roots, isolated 806-job build and full
transitive declaration audit (types, opaque values, constructors and recursor
RHS included). Maximum closure 11,762; only propext, Classical.choice, Quot.sound;
no configured forbidden dependencies, sorry sources or new module warnings.
All 781 closure source hashes stayed stable and matched isolated copies byte for
byte. Artifacts: /tmp/carrier-unindexed-pattern-*. Independent work preserved;
executable unchanged; no coordination. Goal active, not complete or blocked.


## Identity beta/eta peaks force eta-aware residuals (2026-11-05 01:41:30 UTC)

Verdict: generalized the existing identity beta/eta obstruction to arbitrary
ordinary type conversion, and strengthened its separation from the level core
to the entire non-eta expansion union at arbitrary guard depth. One typed
identity beta step and one native function-eta expansion with a stage-zero
guard have no common reduct in that non-eta union. The very same two branches explicitly join at the
first static structure/function-eta stage. Thus this is not a counterexample
to full-union confluence or canonical-Eq strengthening.

The general construction accepts any ordinary equality A = B : Sort u. Let
f be fun _:A => Prop, assign it the converted function type forall _:B, Type,
and apply the identity function at that assigned type to f. The identity redex
recovers the assigned Pi exactly using only lookup/lambda/application recovery;
no native evidence for f is used. Beta exposes the literal A annotation. Native
eta selects B, and finite beta cleanup restores exactly the constant Prop body.
Level-core lambda inversion proves an exact equivalence: the two branches have
a level-core join if and only if the erasures of A and B do.

Consequently BetaEtaCoreForkJoin, explicitly documented as a false proposed
invariant, would imply level-core completeness for arbitrary type conversion.
The concrete counterexample instantiates the domains with the existing neutral
eta pair F f and F (fun x => f x). Its pure-erasure beta/universe separation
excludes every non-eta expansion-union join, for every definition collection.
Pure compatible expansion would give a beta/universe join of the two lambda
branches; beta cleanup and lambda inversion would then give the impossible
beta/universe join of the two domains. The available
native eta step on f instead computes the first domain to the second at stage
one. Compatible lambda computation on the beta branch and beta cleanup on the
eta branch give the explicit stage-one common reduct. All context and source
typings are supplied, so the example persists in canonical-Eq environments.

The concrete core counterexample and its eta repair were already established
in ProofErasureEtaBetaPiBoundary.lean. This entry does not claim that example
as new: the additional results are the arbitrary-conversion construction and
exact level-core equivalence, plus nonjoinability in the full non-eta union.

This identifies the exact excluded case of the earlier BetaLambdaReadout
result: beta creates a lambda by substituting it for a variable carrying a
converted function assignment. The previous literal-lambda-wrapper theorem
tracks a syntactically present lambda through substitutions and remains valid.
The new result rules out core-only residuals even at the first guarded layer;
it does not refute a stage induction using eta-aware residuals or an induction
that also tracks the source's typing conversions. Next work must preserve that
information, rather than treating lower native guard depth as a sufficient
core-joining invariant. General type-fork joining and strengthening remain open.

Validation: one module, five public roots; isolated 784-job build against
committed dependency sources and full transitive declaration audits through
types, opaque values, constructors and recursor rules (maximum 8,595).
Only propext, Classical.choice and Quot.sound; no configured forbidden
dependencies or new-module warnings. Dependency source hashes checked against
the committed tree before committing. Artifacts /dev/shm/identity-eta-peak-*.
Independent work preserved; executable unchanged; no coordination or PR extraction.
GOAL.md remains active; this is evidence changing the confluence strategy, not
one of the goal's completed deliverables.

### 2026-11-05: proof-telescope witness independence — exact erasure equality

Verdict: proved a stronger property than the planned computation chain. Every
retained variable below a dependent telescope of propositions belongs to the
original context. The two witness substitutions agree there, so typed erasure
commutes with substitution to give literally equal erased bodies, even for data
bodies in an arbitrary surrounding context. This requires neither canonical Eq
nor soundness of a chosen definition system. Ordinary telescope proof irrelevance
then supplies a typed chain whose raw computation is reflexive.

Specializing to singleton cast telescopes proves identical erasures (and typed
chains) for each reconstructed field under any two typed witness lists. Fields
may contain dependent data and indices may be arbitrary. Canonical Eq is used
only by existing cast-telescope typing in this specialization. The earlier
simultaneous-chain-substitution proof was superseded by this simpler retained
support argument; no fork joining or native recovery premise was introduced.

Remaining scope: witness replacement does not remove the data-slot casts.
The aligned occurrence theorem uses ordinary type uniqueness to equate an
index domain with its field domain; computational alignment must still be
constructed rather than inferred from that ordinary equality. A live next
fragment is all-propositional index telescopes: fixed parameters and erased
proof indices should make the entire transported/requested family guard
reflexive. General indexed singleton coverage and TypeForkJoin remain open;
no requested final deliverable is claimed and the original sorry remains.

Validation: one new 105-line module, five public roots, isolated 779-job build
and full transitive declaration audit including opaque values, declaration
types and generated dependencies. Maximum closure 8,479; only propext,
Classical.choice, Quot.sound; no forbidden dependencies, sorry sources or new
module warnings. All 754 closure sources remained hash-stable and identical
to isolated copies. Artifacts /tmp/carrier-proof-telescope-*.
Independent work preserved; executable unchanged; no coordination; goal active.

### 2026-11-05: proof-indexed singleton prefixes and stored equations — proved

Verdict: the all-propositional index fragment has an unconditional raw family
guard. A dependent proof suffix can be changed beneath fixed parameters without
changing the erasure of any typed closed template: retained variables refer only
to the common parameter prefix. Apply this to the singleton family template at
the requested index list and the transported constructor's index list. Both lists
are typed, so `proof_indices_family_erasure` makes the two family erasures
literally identical. This is stronger than ordinary family conversion and needs
neither type-fork joining nor a native recovery certificate.

`SingletonPrefixCode.Valid.proof_indices_guard` proves the actual raw guard
beneath every generated residual telescope. `proof_indices_prefix` and
`generated_proof_indices_prefix` realize it as a typed computation chain for
all typed prefix sources. `proof_indices_singleton_equation` then interprets the
full extraction trace and proves the entire lambda-wrapped stored equation.
The proof-index telescope may depend on parameters and earlier proofs; it is
not required to be empty or syntactically constant. No missing prefix/guard
coverage assumption remains in this fragment.

Remaining scope: actual raw proof-indexed pattern instances still require
alignment with their generic equation instances. Next specialize the existing
beta-shape argument to return the common parameter/motive/minor prefix followed
by the reconstructed indices. `ProofIndexedSingleton.type_shape` and
`GuardedSingleton.full_major_args` expose the index and major typings of both
actual full spines; proposition indices and majors erase identically. The
ordinary equality needed alongside this erased equality can be composed from
the actual pat rule, the proved equation chain, and beta. This should bypass
HasTypeJ for the fragment, but is not yet proved. Data-indexed singleton coverage
and TypeForkJoin remain open; no strictly smaller sufficient strengthening
obligation, canonical-Eq proof or counterexample is claimed. Original sorry remains.

Validation: two new modules (121 and 63 lines), six public roots, isolated
805-job build and full transitive declaration audit. Maximum closure 11,269;
only propext, Classical.choice, Quot.sound; no configured forbidden dependencies,
sorry sources or audited-module warnings. All 780 closure source hashes stayed
stable and were byte-identical to isolated copies. Artifacts:
/tmp/carrier-proof-index-equation-*. Independent work preserved; executable
unchanged; no coordination; goal active, not complete or blocked.


## Native cut provenance gives head-beta/expansion residuals (2026-11-05 01:51:58 UTC)

Verdict: proved exact native recovery preservation through finite certified
head-beta computations, then used it to construct commuting residuals with
function eta, masked structure eta and native identity expansion. This is a
positive case of the beta/eta joining problem identified by the preceding
identity-peak obstruction. It uses the full static structure/function-eta
union, without assuming TypeForkJoin or core-joinability of its guard paths.

NativeHeadBeta retains actual domain, body and argument typings at each beta
cut. A retained argument must natively recover the cut's written domain; proof
arguments need no recovery. The relation includes function-position computation
and composition, so beta may create later redexes or expose a lambda by
substituting into a variable. beta_path forgets the certificates. recovery
preserves every selected native output exactly across the whole head path,
using the existing root-beta recovery theorem at cuts and application inversion
in function positions. It does not normalize bodies or substituted arguments.

Every actual native identity expansion reconstructs a typed wrapper with a
NativeHeadBeta contraction, at the source's original assigned type. Its own
generated guard supplies the cut certificate, so no new coverage assumption is
needed for that construction. This is the relevant difference from a wrapper
whose annotation was selected by arbitrary ordinary type conversion.

eta_residual, identity_residual and structure_residual retain the originally
selected native type at the computed source. They rebuild the same expansion
there, and a beta-only residual from the old expansion reaches it. Structure
parameters, universe instance and static proof-field mask stay fixed. If the
head path exposes a literal lambda, lambda_domain additionally constructs a
forward computation from its written annotation to the old selected Pi domain;
eta_square joins by changing just that annotation on the short branch and using
only beta on the long branch, retaining the original body exactly.

Scope: this is not arbitrary beta stability or a native coverage theorem.
Changing an application argument can change the initially recovered codomain;
joining that changed type with a later conversion is still a type fork.
Preservation of cut certificates through arbitrary compatible computations and
unrestricted head-beta coverage remain open. The earlier core obstruction is
not contradicted: cut certificates here may themselves require eta at later
stages. Next track generated-wrapper provenance through those compatible paths,
with explicit residuals on selected types instead of assuming exact recovery.
No strictly smaller sufficient strengthening obligation, canonical-Eq proof or
counterexample is claimed. The original weakN_iff sorry remains; goal active.

Validation: one new module; 17 audit roots including every constructor and the
recursor interfaces; isolated 772-job build; full transitive audit of types,
opaque values, constructors and recursor RHS (maximum 11,365). Only
propext, Classical.choice and Quot.sound; no configured forbidden dependencies,
sorry sources or new-module warnings. All 747 local dependency source hashes
stayed stable and are checked against committed sources before committing.
Artifacts /dev/shm/native-head-beta-*. Independent work preserved; executable
unchanged; no coordination or PR extraction.

### 2026-11-05: actual proof-indexed singleton pattern coverage — proved

Verdict: the full dependent proof-index fragment now has raw pattern coverage.
`singletonInstance_beta_prefix` generalizes the previous unindexed syntax proof:
the actual equation captures preserve the recursor's parameter/motive/minor
prefix, reconstruct an index list of the registered length, and reconstruct the
major. It also identifies the rule prefix count with `data.indexOffset`. The
existing unindexed theorem retains its signature as a specialization.

`proof_telescope_suffix_arguments` proves that every actual argument of a
propositional suffix erases to a proof, with arbitrary data parameters before
it. The registered recursor type and `GuardedSingleton.full_major_args` expose
both actual index/major suffixes. `proof_indices_spine` therefore supplies a
reflexive erased computation between typed full spines sharing their original
parameter/motive/minor prefix. The ordinary equality accompanying this raw
computation comes from the original pat rule composed with the proved generic
equation and beta, not from an assumed computation chain for the original pat.
Thus `proof_indices_singleton_pattern` avoids HasTypeJ, earlier-stage type joins,
constructor-parameter matching, and constructor-universe matching.

`TypedDataIndexedSingletonPatternChainClosure` records the remaining raw case:
the registered layout's index telescope is not propositional. Its
`singleton_closure` covers all other layouts, including empty index telescopes;
ordinary chain completeness now follows from this remaining data-indexed
coverage. This is not a strictly smaller sufficient strengthening condition:
TypeForkJoin remains separate and open. The original sorry remains.

Next full-scope work must address data-index alignment or the type-fork join,
not simply claim success from fragment coverage. Literal-constructor casts
still need computational alignment of index and field domains; ordinary type
uniqueness alone does not provide it. Selective development/standardisation of
typed joins remains a live alternative, without a claimed finite round bound or
exact native recovery invariant (both already concretely obstructed).

Validation: two new modules (122 and 128 lines), and 63 additions/29 deletions
to the beta-shape module. Isolated 811-job build; all nine public roots audited,
including both roots of the modified module. Full transitive declaration audit,
maximum closure 11,797; only propext, Classical.choice, Quot.sound; no configured
forbidden dependencies, sorry sources or audited-module warnings. All 786
closure source hashes were stable and byte-identical to isolated copies.
Artifacts /tmp/carrier-proof-index-pattern-*. Executable unchanged; independent
work preserved; no coordination; goal active, not complete or blocked.


## Native substitution preserves old cuts, not all created cuts (2026-11-05 02:05:26 UTC)

Verdict: certified head developments are closed under exact native substitution,
but that closure cannot certify every new beta redex exposed by substitution.
Both the positive substitution theorem and a concrete created-cut boundary are
checked in the full structure/function-eta union, without TypeForkJoin.

NativeImageTransport.Images.finite_stage collects a uniform finite image bound
from any monotone stage family and a finite source context. The full-union
recovery transport therefore needs only pointwise union recovery, not a bound
chosen by the caller. NativeHeadBeta.subst transports each original root cut's
typings and its retained-argument certificate through a simultaneous typed map.
NativeHeadBeta.inst specializes this to a single retained native argument, with
proof arguments admitted vacuously. body_beta_square supplies the certified
residual after contracting a cut before developing its body's original head
path. Source and image guard depths may be independently unbounded but finite.
These are residuals of existing certificates, not coverage of newly created cuts.

The new boundary instantiates the existing fresh-unit exact-recovery failure.
There is an actually assigned domain A whose erasure contains a fresh retained
unit variable; x cannot recover A in any descending native language. Nevertheless
A computes to C and x recovers C. The identity function written with domain A
is typed and natively recovers the computed Pi C -> C. Its original annotation
is unchanged: lambda recovery converts both the Pi domain and lifted codomain
along the actual A-to-C computation. Substitution of this function for a fresh
function variable is an actual Ctx.SubstEq with native images. It changes the
neutral application f x into (fun y:A => y) x. Both function and argument have
exact native certificates at the selected interface C -> C and C.

That newly exposed identity cut has no NativeHeadBeta certificate, even via
multiple steps: it recovers A before beta, and the proved exact recovery
preservation would force impossible recovery of A from x afterward. The theorem
includes the typed substitution, its native image condition, and the literal
instantiation equation. It is conditional on the same closed positive empty
structure as the existing boundary, and compatible with canonical Eq. It is
not a canonical-Eq strengthening counterexample or a refutation of confluence.

Judgment: carrying exact native cut certificates is valid for residuals of
already certified reductions and generated identity wrappers, but is insufficient
as a complete invariant for all newly created redexes. Do not infer global cut
coverage from native-image substitution closure. A general developments proof
must permit selected types to move toward common reducts or retain stronger
origin information for guard choices. The existing NativeForwardBinder/common
instantiation obligations already contain type-fork content; they cannot be
installed as an automatic local repair. The next task is the residual type fork,
not another exact-cut coverage assertion. General TypeForkJoin, indexed data
singleton coverage and the original strengthening theorem remain open; no
strictly smaller sufficient obligation is claimed.

Validation: two modules (121 and 110 lines), seven public roots, isolated
792-job build and full transitive declaration audits through types, opaque
values, constructors and recursor RHS (maximum 11,384). Only propext,
Classical.choice and Quot.sound; no configured forbidden dependencies, sorry
sources or new-module warnings. All 767 local source hashes stayed stable and
are checked against committed dependency sources before committing. Artifacts
/dev/shm/native-head-subst-*. Independent work preserved; executable unchanged;
no coordination or PR extraction. GOAL.md remains active.


## Dependent singleton data reconstruction from explicit domain chains (2026-11-05)

Verdict: dependent field reconstruction is now computationally checked once
literal data-slot domain comparisons are supplied as typed computation chains.
This is progress inside the data-index case, not a proof of strengthening or a
strictly smaller sufficient obligation.

TypedComputationTrace.mkApps_congr replays a pointwise-related entire argument
spine. TypedComputationEq.instOuter_from_wrapper closes a typed telescope,
applies the two spines, and contracts beta on both ends. Open and closed body
versions need only the source telescope instance; whole-application replay
supplies target typing. Argument chains may carry different actual assignments.
No native recovery, canonical Eq, or type-fork joining is needed here.

TypedComputationEq.typeCast removes a canonical type cast from a chain between
its endpoint types, at any actual assignment of the cast. The equality witness
may be opaque. It uses the already checked canonical Eq prefix computation,
not ordinary type uniqueness as a surrogate for computation.

transportedFields_chain_of_data_alignment handles the full dependent field
list. At each step, the preceding field chains compare the instantiated field
domains; a supplied index-domain/original-field-domain chain then compares the
actual cast endpoints. The cast computes, and a supplied index/field value
chain reaches the original field. Proof fields use proof irrelevance. Original
and transported telescope typings determine every intermediate assignment.

At literal constructor indices the value chains are reflexive. The named
SingletonLiteralDataDomainChains premise isolates only the comparisons of
specialized declared index domains with original field domains, before any
reconstructed fields occur. transportedFields_chain_at_literal derives all
field chains from it, for any major proof at those indices. Applying the typed
branch-family template gives transportedFamily_chain_at_literal. The final
transportedFamily_join_at_literal additionally assumes TypeForkJoin to provide
the actual shared erased reduct required by the singleton family guard.

Remaining scope: ordinary uniqueness supplies ordinary domain equations, not
the named domain chains. Literal-family comparison does not cover arbitrary
prefixes; the stored-equation trace currently requests prefix computation at
all occurrences. General data-indexed singleton pattern coverage, computational
domain agreement, full-union TypeForkJoin and the original strengthening sorry
remain open. No inference of a common reduct from a bare computation chain, no
ordinary-equality completeness assumption hidden in a proof, and no claim that
the new local domain premise is sufficient for the whole goal.

Validation: four new modules, 331 lines, twelve public roots; isolated 807-job
build and full transitive declaration audits through types, opaque bodies,
constructors and recursor RHS. Maximum closure 11,170; only propext,
Classical.choice and Quot.sound, no configured forbidden dependencies or sorry
sources, and no new-module warnings. All 782 closure source hashes were stable
and byte-identical to isolated copies. Artifacts /tmp/carrier-data-domain-chain-*.
Executable unchanged; independent work preserved; no coordination; GOAL.md active.


## Generic declaration-domain comparisons suffice at all literal occurrences (2026-11-05)

Verdict: the new data-domain premise can be supplied once per data slot in the
closed declaration's generic field context, instead of separately at every
actual parameter/field instance. This is a finite collection for a fixed layout
and universe instance; the generic computational comparisons remain open.

SingletonGenericDataDomainChains names those comparisons. Their left sides are
the declared index domains instantiated at generic parameters and constructor
indices; their right sides are the field domains at the preceding literal field
variables. singleton_generic_data_domains_defeq proves the corresponding
ordinary equalities without assuming any computation chains. The generic index
and field declarations type the same literal field variable, so ordinary type
uniqueness gives the equality at the specified field universe.

SingletonGenericDataDomainChains.specialize uses typed simultaneous substitution
to supply SingletonLiteralDataDomainChains at any actual typed field instance.
Closed-template composition, generic parameter specialization and finite variable
range specialization give the exact endpoints. The ordinary substitution needs
no native image recovery or type-fork joining. family_chain combines this with
the preceding dependent reconstruction theorem for any major proof at the
literal constructor indices.

Remaining scope: constructing these generic domain chains is still an open
computational completeness problem. Proving ordinary domain equality, as done
here, does not solve it. The general singleton stored-equation trace also needs
prefix coverage beyond literal occurrences. Full-union TypeForkJoin and the
original strengthening theorem remain open. No strict-smaller/sufficient-goal
claim is made. Inspection of the existing lambda-origin observer also confirms
that an unrestricted native-output readout cannot simply be inserted: control
frames do not retain generated-wrapper guard provenance, and the already checked
caller-domain boundary rules out the straightforward forward-origin assertion.
The provenance/common-reduct route remains live and unproved.

Validation: one new 120-line module with four public roots, plus three roots of
the committed beta-recovery dependency restored in the isolated checkout. The
shared working-tree version of that dependency is being independently edited;
it was neither reused nor staged. Isolated 809-job build; exact seven-root full
transitive audit, maximum closure 11,344; only propext, Classical.choice and
Quot.sound, no configured forbidden dependencies, sorry sources or audited-module
warnings. All 784 closure hashes match isolated copies and committed dependencies
at db693ba1 (with the one new source checked against its working copy). Artifacts
/tmp/carrier-generic-data-domains-*. Executable unchanged; independent edits
preserved; no coordination; GOAL.md active, not complete or blocked.


## Native wrapper histories and unused head cuts (2026-11-05 02:25:12 UTC)

Verdict: checked progress on the development route, with no general type-fork
joining premise. Native recovery of an arbitrary typed identity wrapper is
exactly forward computation from its stored annotation, provided its argument
is retained. This gives a real source for the residual type fork; it does not
join that fork. A typed constant wrapper preserves the complete set of native
outputs in both directions, even without recovery for its discarded argument.

The root-beta factorization is extracted from the existing recovery proof:
recover the original body, instantiate that selected type, then retain the final
conversion tail. It needs only ordinary argument typing. Unused-binder
certificate descent removes this intermediate binder for identity and constant
bodies. Full static structure/function-eta union guards and arbitrary native
conversion tails are covered.

The existing NativeHeadBeta relation now includes constant cuts with the body
typed in the lower context. Its recovery, expansion residuals, lambda readout,
eta square and native-substitution theorem still hold. The prior created-identity
cut counterexample also still holds for this enlarged relation. Thus this is
an actual extension of the certified developments, not arbitrary cut coverage.
The lower typing premise for a constant body is explicit; no strengthening is
used to infer it from typing under the unused binder.

Validation: 793-job isolated build; 34 public roots including the enlarged
inductive's constructors and recursors, every public theorem in all four edited
modules, and the two existing created-cut boundary roots. Full transitive audit
through types, opaque values and recursor RHS: maximum closure 11,387,
only propext, Classical.choice and Quot.sound, no configured forbidden dependency
or sorry. All 768 local import sources remained unchanged during validation;
dependencies were copied from committed HEAD and checked again before commit.
Artifacts: /dev/shm/wrapper-native-*. Executable unchanged. Independent edits
preserved. No PR extraction. GOAL.md remains open: no strengthening proof,
canonical-Eq counterexample, or strictly smaller sufficient obligation claimed.


## Literal-prefix traces close stored data-indexed singleton equations (2026-11-05)

Verdict: removed the all-prefix coverage premise from stored singleton equation
computation. For arbitrary dependent data indices, generic data-domain chains
and TypeForkJoin now suffice for the entire lambda-wrapped stored equation.
Neither open premise is discharged; actual pattern alignment remains separate.

RecursorData.LiteralSingletonPrefix records the actual opened parameters, a typed
constructor field instance, and literal equality of the opened indices with the
constructor indices specialized at those fields. Its fresh proof major need not
be the constructor itself. RecursorRegistered.zero_join_via_literal_prefix retains
this evidence at the only prefix step of the original coverage construction.
The construction's existing typed fields beneath the fresh major, and its exact
opened argument equations, supply the certificate. The original zero_join_via_prefix
signature and zero_join remain wrappers, so existing callers are preserved.
No second copy of the large coverage construction was introduced.

SingletonPrefixCode.Valid.literal_guard uses the registered opened telescope to
obtain actual major typing, specializes the generic declaration-domain chains,
and forms the transported-family computation chain. TypeForkJoin joins its two
erasures. Finite-stage extraction from the resulting raw comparison gives a
concrete finite guard depth; no uniform stage bound or native argument recovery
is assumed. TypedComputationEq.literal_prefix rebuilds the generated check and
performs its recovered singleton step at the next stage, retaining the original
source assignment. generated_literal_prefix derives the fixed code certificates
from registration and generation.

TypedComputationEq.singleton_equation_of_literal_prefix interprets the revised
coverage construction as typed computation chains. data_singleton_equation
supplies its prefix callback using the finite generic domain comparisons and
TypeForkJoin. It covers every registered large-eliminating singleton equation at
a proposition-source specialization, including arbitrary dependent data-index
telescopes, at the stored equation type. This closes the interface mismatch
between the previous literal-family theorem and the older all-prefix callback.

Remaining scope: generic domain chains are known only as ordinary domain
equalities in general, and TypeForkJoin is open. An actual matched pattern may
supply recursor indices different from the literal indices of the stored-equation
instance; ordinary family/type uniqueness gives their ordinary alignment but
not computation chains. The proof-indexed pattern case remains unconditionally
covered by exact erasure, while the data-indexed pattern case still needs that
computational alignment. Strengthening is not proved, and no strictly smaller
sufficient irreducible obligation is claimed.

Validation: three new modules (23, 110 and 70 lines), and 60 additions/5 deletions
in SingletonCoverage. Isolated 812-job build, with all 39 public roots audited
across five modules (including the committed beta-recovery dependency updated
by independent work). Full transitive traversal includes declaration types,
opaque bodies, constructors and recursor RHS; maximum closure 11,345. Only
propext, Classical.choice and Quot.sound; no configured forbidden dependencies,
sorry sources or audited-module warnings. All 787 closure source hashes stayed
stable and matched isolated copies byte-for-byte. Artifacts
/tmp/carrier-literal-prefix-*. Executable unchanged; independent work preserved;
no coordination; GOAL.md active, not complete or blocked.


## Generated lambda frames retain historical native origins (2026-11-05 02:40:56 UTC)

Verdict: the provenance route now has a checked invariant that survives a real
loss of exact cut recovery. This advances lambda-domain observation, without
claiming closure under arbitrary compatible computation or joining type forks.

NativePiHistory stores an actual typed Pi predecessor, a forward domain path
from the original anchor, and the complete computation to a selected native
output. Pi component extraction reads every later literal Pi domain from that
anchor. LambdaWrapperHistory distinguishes an inner lambda payload from an
identity frame's historical annotation. Constant and identity frames can nest.
Every native output of such a frame has the stored Pi origin, without requiring
the current wrapped argument to recover the old annotation. Generated native
identity expansion supplies its history from the actual original guard.

The invariant survives literal root beta contraction, replacement by an argument
with the same anchored payload history and ordinary type, and arbitrary full-
union computation of an identity annotation. Root native eta reconstructs a
literal lambda payload with a forward domain history. A finite beta readout
exposes a lambda and its domain path. No body-origin claim is made: the history
is deliberately about lambda domains, with no arbitrary equality-to-computation
or fork-joining premise hidden in it.

The boundary module verifies that this history is useful beyond exact native
cuts. Starting with the existing positive empty-structure example x:A that
cannot natively recover its assigned A, put the exactly recoverable identity
wrapper w=(fun y:A => y) x inside a constant function f=(fun _:Type => w).
Native recovery of f at Q=(Type -> A) really licenses a generated outer identity
frame. Beta inside f produces g=(fun _:Type => x). Exact recovery of g at Q would
recover x at A by applying g to Prop and contracting the constant wrapper,
contradicting the existing boundary. Nevertheless the evolved outer frame has
LambdaWrapperHistory, and root contraction retains that history. Its contraction
is provably outside NativeHeadBeta, including the recently added constant cuts.
This is an actually generated frame followed by an actual beta path, not an
arbitrarily assigned wrapper presented as generated provenance.

Remaining gap: computation in the bodies of control functions can destroy the
literal identity/constant-frame syntax. The grammar does not cover those
higher-order control programs, and no closure of the grammar under all
ScopedCompute paths is asserted. The next observer must retain these separate
payload and annotation histories across its control-variable demands. General
full-union lambda readout, TypeForkJoin and the original strengthening sorry
remain open. No new strictly smaller sufficient obligation is claimed.

Validation: two new modules, 351 lines; 794-job isolated build and 20 public
roots including constructors and recursor RHS, with complete transitive type
and opaque-value traversal. Maximum closure 11,387; only propext,
Classical.choice and Quot.sound, no configured forbidden dependencies or sorry,
and no new-module warnings. All 769 local source hashes remained stable during
validation and were checked against committed dependencies before staging.
Artifacts /dev/shm/lambda-wrapper-*. Executable unchanged, independent work
preserved, no coordination or PR extraction. GOAL.md remains active.

### Strong-derivation computational typing — checked progress, open

Retain structural constant/application certificates together with term chains
in the IsDefEqStrong induction. Conversion subderivations supply actual chains;
the pattern obligation receives the resulting certificates for source and
reduct. This avoids asking arbitrary ordinary typings to expose computational
conversions. Five modules now check: raw join realization, Pi chain injectivity
under TypeForkJoin, HasTypeC inversion, simultaneous strong induction, and
computational telescope/major inversion. Remaining: rigid family argument
readout, earlier-environment chains for declaration normalization and generic
data domains, and TypeForkJoin. No strictly smaller sufficient obligation is
claimed; the original strengthening sorry is unchanged.

### Structural variable certificates for generic data domains — checked progress

Extend HasTypeC with exact variable lookups. Two certificates for one variable
compare its assigned types computationally, without TypeForkJoin. Identity
computational telescope typing and the literal data-slot identity now turn
computational constructor-index typing into SingletonGenericDataDomainChains.
Remaining: obtain the index certificates from earlier declaration history;
ordinary typing alone does not supply them. Actual rigid argument readout and
TypeForkJoin remain open. No strict reduction or complete strengthening result.

### Rigid arguments carry scoped value chains — checked foundation, readout open

Forward retained-argument origins are already refuted by caller eta. Replace
them with existentially typed ScopedValueChain histories. Representative replay,
context realization, composition, arbitrary typed substitution, endpoint
computation and application-spine congruence now check without TypeForkJoin.
The known caller-eta forward-origin counterexample has these histories, even
after arbitrary interpreted substitution. A literal-endpoint RigidSpineValueHistory
premise plus TypeForkJoin now yields exact computational rigid-spine injectivity.
Remaining: prove that history premise with a finite observer for opaque and
higher-order data arguments; obtain declaration-history certificates and prove
TypeForkJoin. No strict reduction or full strengthening result is asserted.

## 2026-11-05 03:13:25 UTC — Recursive native-type observations close full lambda-domain readout

Verdict: checked progress. Replace the literal wrapper grammar by a finite
control observer with separate recursive histories for written annotations.
An indexed Pi observer allows arbitrary dependent codomains while fixing only
the lower domain. NativeTypeDemand interprets finite term demands in native
types; ordinary interpreted substitution preserves these demands without exact
native recovery of argument images. This supplies the previously missing
application case, including arbitrary computation in control-function bodies.

The resulting lambda-domain observer survives every compatible full static
structure/function-eta union computation. A finite beta readout exposes a lambda
whose domain has a forward computation from the original written domain.
Consequently, a common computed endpoint for two retained lambdas gives a common
computed endpoint for their domains, and every later native Pi selection retains
a forward history of its domain. No TypeForkJoin premise or body-origin claim.

Remaining: this does not join arbitrary forks or preserve the lambda body's
history. Applying the endpoint to a fresh variable does not itself close that
gap: comparing with the original body requires a beta residual across the
function computation. Do not silently infer this from ordinary typed
substitution or domain readout. The strengthening sorry remains open; no new
strictly smaller sufficient obligation is claimed.

Validation: nine modules, 776-job build, 79 public/constructor/recursor roots;
full type/opaque-value/recursor-RHS audit, maximum closure 11,435, only the
three allowed axioms, no forbidden dependencies or new-module warnings. All 751
local dependency sources stayed stable and were checked against committed
sources before staging. Artifacts /dev/shm/lambda-domain-*. No PR extraction.

## 2026-11-05 03:24:52 UTC — Computed application cuts and root peaks along lambda histories

Verdict: checked progress. Use the full domain observer before asking for an
original-body history. If an unchanged argument recovers the original written
domain A, conversion along the computed function's domain history supplies its
exact certificate at every exposed lambda domain. Arbitrary computed endpoints
have a finite beta readout ending in an actual typed lambda and a certified final
application cut. This does not certify the preceding control beta steps. Once
that cut is selected, subsequent body computation instantiates exactly.

More directly useful for confluence: native eta at any computed descendant of
a lambda can be joined with arbitrary further function computation using only
fork joining at the original A. The full domain observer supplies both paths
from A; the existing eta residual makes the final bodies identical. Every
primitive root along the same history is either a beta-reversible wrapper or
native function eta. Consequently the local A-fork premise handles all primitive
root/computation peaks along that history, without a body-history premise.

Remaining: arbitrary beta-root peaks, compatible surrounding contexts, and a
valid global induction supplying local domain forks. If the argument itself
computes, its old native certificate cannot silently be reused; independently
computed domain paths need not already have a join. No new strictly smaller
sufficient obligation or completed strengthening proof is claimed.

Validation: two modules, eight roots, 793-job build; full transitive audit
maximum closure 11,522, only allowed axioms, no forbidden dependencies or
new-module warnings. All 768 closure source hashes stable and committed
outside these modules. Artifacts /dev/shm/lambda-history-peaks-*.

## 2026-11-05 03:36:04 UTC — Complete local square at an initially certified beta cut

Verdict: checked progress plus a checked boundary on iteration. The full static
structure/function-eta body/argument square uses native recovery only before
argument computation. Instantiate the body path first, then compute the argument
through the realized body. Backward context transport covers bodies computed
after the original domain changes. No new native output for the computed
argument is required; loss of exact recovery does not invalidate this square.

ScopedStep specifies one primitive or beta contraction at one compatible
occurrence. Its reflexive-transitive closure is proved exactly equivalent to
ScopedCompute; simultaneous binder computation decomposes body first, domain
second. native_root_beta_step_square now joins every such one-step competitor
of a retained beta redex whose original argument has its written native type.
Whole-redex primitives commute by native recovery, function-root primitives
beta-return the same applied body, and child steps use the body/argument square.

The next naive step is refuted: an outer cut initially certified by a native
identity-wrapper argument loses its certificate after one beta step inside that
argument, using the existing positive empty-structure boundary. The two branches
happen to coincide, so this is not a confluence counterexample. It rules out
iterating the local result by assuming every marked residual remains
NativeHeadBeta. A development invariant must instead retain historical body and
argument paths, or otherwise join without exact certification of each residual.

Remaining: compose these local squares through arbitrary paths, including newly
created cuts and full body-history/readout. No unrestricted local confluence,
TypeForkJoin, strengthening proof, or strict reduction of PropFront is claimed.
Validation: five modules, 28 public/constructor/recursor roots, 818-job build;
full dependency audit maximum closure 11,629, allowed axioms only, no
forbidden dependencies or new-module warnings, 793 stable local source hashes.
Artifacts /dev/shm/native-beta-local-*; no PR extraction.

### Finite rigid observer with opaque value keys — proved for typed telescopes

The scoped-chain invariant now has a finite dependent observer, full-union
preservation and operational readout. Proof versus data profiles follow ordinary
domain sorts; data requires only a universe not definitionally zero. Function
demands are interpreted at actually typed applications. This yields argument
histories for rigid heads assigned universe-ending dependent telescopes, with
arbitrary data/function arguments and proof slots, without native recovery or
TypeForkJoin. Under TypeForkJoin, TypedComputationEq.rigid_spine_inv now derives
exact argument chains without a separate history premise. Remaining: consume
this theorem in actual singleton alignment, obtain declaration-history
normalization/index certificates, and prove TypeForkJoin. The broader arbitrary
rigid-kind history predicate is not claimed. Original strengthening remains open;
no strictly smaller sufficient obligation is asserted.

## 2026-11-05 03:47:15 UTC — Historical cuts and a native pivot before argument computation

Verdict: checked progress. Replace renewed exact native certificates at residual
cuts by actual domain/body/argument computation histories from one originally
certified cut. Body history stays under the original binder. Backward native
context transport appends computations performed under later annotations.
The histories survive arbitrarily many interleaved component rounds and supply
an exact contraction residual from the original contractum, even when the final
argument lacks native recovery at the written domain.

The stronger step is native_pivot: every native type selected by the evolved
redex is recovered at a typed intermediate reachable from the original
contractum, which then computes to the current raw contractum. Recover the
computed body under the old binder and instantiate the original native argument;
argument computation then propagates through the selected type and its final
conversion tail. Native eta and structure guards can fire at this pivot before
argument computation runs through their outputs. Thus all primitive competitors
of the historical cut join without certifying its current beta contraction.
Every one-occurrence competitor is covered as well.

The previous exact-certificate-loss example now has the required history; its
current identity cut remains provably outside NativeHeadBeta. This verifies that
the new invariant actually crosses that boundary. Remaining: root expansions
followed by arbitrary continuation, nested marked contexts and created cuts.
The proved composition is finite component rounds followed by one arbitrary
step, not a strip theorem for all paths. No TypeForkJoin, strengthening proof,
canonical-Eq counterexample or strict reduction of PropFront is claimed.

Validation: five modules, 824-job build, 19 public roots; full transitive
audit maximum closure 11,634, only allowed axioms, no forbidden dependencies
or new-module warnings; all 799 local source hashes stable and equal own sources
or committed dependencies at staging. Artifacts /dev/shm/cut-history-*.

### 2026-11-05 — Computational singleton instance alignment from value histories

**Verdict: proved conditional alignment, replacing the arbitrary-index alignment gap.**
`TypedComputationEqU.rigid_spine_inv` supplies argument chains from the proved
value observer for sort-headed rigid families. `singletonInstance_alignC` uses
structural application typings (`HasTypeC`), computational telescope peeling and
earlier declaration chains to align every actual singleton recursor instance
with its generic equation, including arbitrary dependent data indices. No
ordinary uniqueness equation is promoted to a computation chain.

Type-fork joining and earlier declaration chains remain assumptions; generic
data-domain certificates are still needed for the stored equation. This does
not complete strengthening or establish a strictly smaller sufficient obligation.
Validation: four modules, 836-job isolated build, 58 public/generated roots,
maximum closure 11,976; 811 stable source hashes and committed dependencies;
only allowed axioms, no forbidden dependencies or task-module warnings.

### 2026-11-05 — Actual singleton chains close the strong pattern case

**Verdict: conditional chain completeness now integrated.**
`TypedComputationEq.computational_singleton_pattern` composes actual index
alignment with the stored singleton equation for arbitrary dependent data
indices. `computational_pattern_closure_of_declarations` covers every stored
pattern; `computational_typing_of_declarations` supplies chains and both endpoint
`HasTypeC` certificates for ordinary equality. The assumptions are TypeForkJoin,
SingletonDeclarationChains and RegisteredSingletonDomainChains, plus the
concrete presentation. Declaration certificates and fork joining remain open.
No strict-reduction or completed-strengthening claim. Two modules / 150 lines,
848-job build, five audited roots (maximum closure 12,617), 823 stable source
hashes; only allowed axioms and no forbidden dependencies or task warnings.

### 2026-11-05 03:58:23 UTC — Uniform historical pivots under application spines

**Verdict: proved the contextual one-step square for every pending application
spine.** Strengthen native_pivot to choose one typed pivot before selecting any
native output. Exact transfer of all outputs lifts through applications because
native application recovery uses only the function certificate. The same pivot
therefore works for every raw pending spine, with no native certificates for its
arguments. Primitive guards at any enclosing application can fire at that pivot;
the remaining argument computation runs inside the expanded output.

The resulting native_cut_spine_development_step_square covers arbitrarily many
component-history rounds, computation of all pending arguments, and any final
one-occurrence step anywhere in the spine. The competing primitive branch joins
by beta alone; the original-contractum branch uses full-union computation.
This extends the previous root-cut square to cuts buried in function position.

Still open: histories after root expansion followed by unrestricted continuation,
other surrounding contexts, and created cuts. Exact output transfer alone does
not supply those cases: dependent annotations and projection result types can
retain the changed subterm itself. This is a limitation of the present argument,
not a checked refutation of contextual developments. No strengthening proof,
canonical-Eq counterexample, or strictly smaller sufficient obligation is claimed.
Validation: four modules, 814-job isolated build, 11 public roots; full
transitive audit maximum closure 11,650; only allowed axioms, no forbidden
dependencies or task-module warnings; 789 stable local source hashes, checked
against own sources and committed dependencies at staging. Artifacts
/dev/shm/cut-spine-*.

### 2026-11-05 — Discharge declaration chains by actual stage induction

**Verdict: earlier declaration-chain assumption removed from integrated completeness.**
`computational_typing_of_strong_earlier` interprets an earlier environment's
strong derivations directly in ambient chains and computational typings, with
coverage only for its pattern registry. The type-former extension preserves
that registry. `computational_pattern_closure_of_history` uses the chosen
installation history and strict stage rank to supply the declaration chains
needed by the stage-specific actual singleton theorem.

`computational_typing_of_history` now assumes TypeForkJoin and
RegisteredSingletonDomainChains, not SingletonDeclarationChains. Those two
assumptions and the original strengthening problem remain open; no strict
reduction claim. Next: generic index typing can be extracted from formation
of the recursor type before its rules are installed, then interpreted using
the same earlier-registry induction.

Validation: five-module integration build (851 jobs), 18 public/generated
roots, maximum closure 12,633, 826 stable source hashes, only allowed axioms,
no forbidden dependencies or task-module warnings.
