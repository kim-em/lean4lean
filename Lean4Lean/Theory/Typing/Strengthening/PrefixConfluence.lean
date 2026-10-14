import Lean4Lean.Theory.Typing.Strengthening.AugmentedComputationalConfluence

/-! # Exact confluence for the compatible actual-prefix relation

The finite mixed presentation and PrefixCompute have the same typed endpoints.
Constructor saturation is recovered from projection source typing, so the
parallel projection rule embeds in the syntactic saturated projection relation.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A well-typed projection of its registered constructor supplies exactly all
constructor parameters and fields. No field typing or arity check is assumed. -/
theorem projection_constructor_saturated (hΓ : OnCtx Γ (env.IsType univs))
    (hinfo : env.projections S info)
    (H : env.HasType univs Γ (.proj S index (mkApps (.const info.ctorName ls) args)) F) :
    args.length = info.nparams + info.numFields := by
  obtain ⟨info', _, _, _, _, _, _, hi', _, _, _, _, _, _, hm, _, _⟩ := H.proj_inv henv hΓ
  cases henv.ordered.projections_unique hi' hinfo
  obtain ⟨decl, type, ctor, _, _, hname, _, huvars, hnparams, _, _, _, hctorType,
    _, _, _, Hraw, _⟩ := henv.ordered.projectionShape hinfo
  obtain ⟨doms, result, hshape, hle, _, hhead, harity⟩ := Hraw.forallArity
  subst hname
  have hresult : result = mkApps (.const type.name (VLevel.params decl.uvars)) result.getAppFnArgs.2 := by
    rw [← hhead]; exact (mkApps_getAppFnArgs_eq result).symm
  have hctor := henv.ordered.projectionConstructor hinfo
  rw [hctorType] at hshape harity
  have ⟨ci, hci, hls, hlen⟩ :=
    (VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, hm.hasType.2⟩).elim fun _ h =>
      HasType.const_inv henv.orderedStrong hΓ h
  rw [hctor] at hci
  cases Option.some.inj hci
  have hc : env.HasType univs Γ (.const info.ctorName ls) (info.ctorType.instL ls) :=
    HasType.const hctor hls hlen
  rw [hshape, hresult, instL_wrapForalls, instL_mkApps] at hc
  have hn := HasType.mkApps_rigid_arity henv hΓ (henv.projectionRigid hinfo) hc hm.hasType.2
  simp only [List.length_map] at hn
  rw [hn, VProjectionInfo.numFields, harity]
  omega

end Lean4Lean.VEnv.Strengthening.PureObservation

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]

private theorem augmented_map (f : VExpr → VExpr)
    (hf : ∀ {a b}, AugmentedComputeStep Γ a b → AugmentedComputeStep Δ (f a) (f b))
    (H : AugmentedCompute Γ a b) : AugmentedCompute Δ (f a) (f b) := by
  induction H with
  | rfl => exact .rfl
  | tail _ H ih => exact ih.tail (hf H)

/-- Finite mixed computation has the compatible-congruence interface. Binder
paths run before domain paths, keeping each nontrivial body step in its source
context and requiring no typed context conversion for this syntactic result. -/
theorem augmentedCompute_congrRel : CongrRel AugmentedCompute where
  rfl := .rfl
  app {Γ f f' a a'} HF HA := by
    exact (augmented_map (fun f => .app f a) (fun H => H.elim
      (fun H => .inl (.app H .refl)) (fun H => .inr (.app H .rfl))) HF).trans
      (augmented_map (fun a => .app f' a) (fun H => H.elim
        (fun H => .inl (.app .refl H)) (fun H => .inr (.app .rfl H))) HA)
  proj H := augmented_map _ (fun H => H.elim (fun H => .inl (.proj H)) (fun H => .inr (.proj H))) H
  lam {Γ A A' b b'} HA HB := by
    exact (augmented_map (fun b => .lam A b) (fun H => H.elim
      (fun H => .inl (.lam .refl H)) (fun H => .inr (.lam .rfl H))) HB).trans
      (augmented_map (fun A => .lam A b') (fun H => H.elim
        (fun H => .inl (.lam H .refl)) (fun H => .inr (.lam H .rfl))) HA)
  forallE {Γ A A' b b'} HA HB := by
    exact (augmented_map (fun b => .forallE A b) (fun H => H.elim
      (fun H => .inl (.forallE .refl H)) (fun H => .inr (.forallE .rfl H))) HB).trans
      (augmented_map (fun A => .forallE A b') (fun H => H.elim
        (fun H => .inl (.forallE H .refl)) (fun H => .inr (.forallE H .rfl))) HA)
  weakN W H := augmented_map _ (fun H => H.elim
    (fun H => .inl (by
      simp only [← lift'_consN_skipN, InductiveSignature.RecursorData.lift'_eq_subst]
      exact H.subst))
    (fun H => .inr (H.weakN W))) H

/-- Every compatible actual-prefix computation embeds in the finite mixed
presentation, with no source-typing premise. -/
theorem PureObservation.PrefixCompute.toAugmented
    (H : PrefixCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) Γ a b) :
    AugmentedCompute Γ a b := by
  induction H with
  | base H => exact .tail .rfl (.inl H)
  | singleton H => exact .tail .rfl (.inr (.delta rfl (fun _ _ _ => .rfl) H))
  | quotient H => exact .tail .rfl (.inr (.quotDelta rfl (fun _ _ _ => .rfl) H))
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | app _ _ ih1 ih2 => exact augmentedCompute_congrRel.app ih1 ih2
  | lam _ _ ih1 ih2 => exact augmentedCompute_congrRel.lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact augmentedCompute_congrRel.forallE ih1 ih2
  | proj _ ih => exact augmentedCompute_congrRel.proj ih

/-- A source-typed DeltaPar step serializes into compatible actual-prefix
computation. Projection saturation follows from its checked source. -/
theorem PureObservation.PrefixCompute.of_deltaPar
    (H : DeltaPar Γ a b) (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) :
    PrefixCompute D Γ a b := by
  induction H generalizing A with
  | bvar | sort | const => exact .refl
  | app _ _ ihf iha =>
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    exact .app (ihf hΓ hf) (iha hΓ hx)
  | lam _ _ ihA ihb =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ha.lam_inv henv hΓ
    exact .lam (ihA hΓ hA) (ihb ⟨hΓ, _, hA⟩ hb)
  | forallE _ _ ihA ihB =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ha.forallE_inv henv
    exact .forallE (ihA hΓ hA) (ihB ⟨hΓ, _, hA⟩ hB)
  | proj _ ihm =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2)
  | delta hlen _ hr ih =>
    have HA := List.forall₂_of_getElem hlen (fun i hi hi' => ih i hi hi' hΓ
      (HasType.mkApps_args_typed hΓ ha _ (List.getElem_mem hi)).choose_spec)
    exact (prefixCompute_congrRel.mkApps .refl HA).trans (.singleton hr)
  | quotDelta hlen _ hr ih =>
    have HA := List.forall₂_of_getElem hlen (fun i hi hi' => ih i hi hi' hΓ
      (HasType.mkApps_args_typed hΓ ha _ (List.getElem_mem hi)).choose_spec)
    exact (prefixCompute_congrRel.mkApps .refl HA).trans (.quotient hr)
  | projIota hlen _ hl hs hi ht ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    have HA := List.forall₂_of_getElem hlen (fun i hi hi' => ih i hi hi' hΓ
      (HasType.mkApps_args_typed hΓ hm.hasType.2 _ (List.getElem_mem hi)).choose_spec)
    exact (PrefixCompute.proj (prefixCompute_congrRel.mkApps .refl HA)).trans
      (.base (.base (.projIota hl (projection_constructor_saturated hΓ hl hs) hi)))

/-- Every finite mixed path from a typed source is a compatible actual-prefix
path with the same literal endpoints. -/
theorem AugmentedCompute.toPrefix (H : AugmentedCompute Γ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) :
    PrefixCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) Γ a b := by
  induction H with
  | rfl => exact .refl
  | tail H R ih =>
    rcases R with R | R
    · exact ih.trans (.base R)
    · exact ih.trans (.of_deltaPar R hΓ (AugmentedCompute.hasType hΓ H ha))

/-- The compatible actual-prefix relation over all stored and selected structure
equations is exactly confluent from typed sources. This includes indexed
prefixes and requires no canonical Eq, normalization or strengthening front. -/
theorem PureObservation.PrefixCompute.confluent
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
    (H1 : PrefixCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) Γ a b)
    (H2 : PrefixCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) Γ a c) :
    ∃ d, PrefixCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) Γ b d ∧
      PrefixCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) Γ c d := by
  obtain ⟨d, HB, HC⟩ := H1.toAugmented.confluent hcon hΓ ha H2.toAugmented
  have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  exact ⟨d, HB.toPrefix hΓ (H1.simAt hs hΓ _ ha).hasType.2,
    HC.toPrefix hΓ (H2.simAt hs hΓ _ ha).hasType.2⟩

end Lean4Lean.VEnv.Strengthening
