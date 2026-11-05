import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePolyAliasCompute
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasCoreExtension

/-! # Polymorphic aliases through full enriched computation -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]
/-- A matched pattern at an actual stored-definition head must be the bare
constant definition pattern. Iota patterns are separated by registry ownership. -/
theorem erased_pattern_stored_head_bare
    (hp : Pat p r) (hm : Matches p a ls captures)
    (HD : (Definitions.ofEnv env univs henv).unfolds name levels rhs)
    (hh : a.constHead = some name) : ∃ ls', a = .const name ls' := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  cases sp with
  | defn c =>
    cases hm
    cases Option.some.inj hh
    exact ⟨_, rfl⟩
  | iota rc mr cc kc =>
    have HH : some rc = some name := by
      simpa only [Pattern.constHead_eq, SimplePattern.iota_headConst] using hm.constHead.symm.trans hh
    have hn : rc = name := Option.some.inj HH
    exact (iota_no_stored_definition hp (hn ▸ HD)).elim

/-- An ordinary primitive at a stored head can only occur at the bare alias,
not at an applied alias spine. This holds for any selected delta collection. -/
theorem erased_iota_stored_head_bare
    (HD : (Definitions.ofEnv env univs henv).unfolds name levels rhs)
    (R : ErasedIotaPrimitive D a b) (hh : a.constHead = some name) :
    ∃ ls', a = .const name ls' := by
  rcases R with (R | R) | R
  · cases R with
    | delta => cases Option.some.inj hh; exact ⟨_, rfl⟩
    | projIota => cases hh
  · cases R with
    | select hp _ hm => exact erased_pattern_stored_head_bare hp hm HD hh
    | apply hp _ hm => exact erased_pattern_stored_head_bare hp hm HD hh
  · cases R with
    | intro hp _ _ hm => exact erased_pattern_stored_head_bare hp hm HD hh

namespace PolyAliasDemandProfile
open DemandProfile
variable {c : Name} {arity : Nat}

/-- An extended delta rule at an observed alias selects its certified body.
The concrete pattern alternatives already belong to the actual stored core. -/
theorem Obs.alias_root_of_agreement
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hag : StoredAgreement D)
    (HT : Typing Δ (.const name levels) t)
    (HD : (Definitions.ofEnv env univs henv).unfolds name levels rhs)
    (HB : Obs c arity Δ S (proofErase [] rhs) t o)
    (R : ErasedIotaPrimitive D (.const name levels) out) : Obs c arity Δ S out t o := by
  rcases R with (R | R) | R
  · cases R with
    | delta HD' => cases hag HD HD'; exact HB
  · obtain ⟨Γ, e, T, hΓ, _, ht, _, EE⟩ := HT
    obtain rfl := erase_const_inv EE
    obtain ⟨rhs', HD', rfl⟩ := erased_stored_constant_root hcon hΓ ht (.inl (.inr R))
    cases Definitions.ofEnv_unique henv HD HD'
    exact HB
  · obtain ⟨Γ, e, T, hΓ, _, ht, _, EE⟩ := HT
    obtain rfl := erase_const_inv EE
    obtain ⟨rhs', HD', rfl⟩ := erased_stored_constant_root hcon hΓ ht (.inr R)
    cases Definitions.ofEnv_unique henv HD HD'
    exact HB

/-- Extended ordinary roots preserve alias observations when stored bodies
agree and the designated rigid head remains non-unfolding. -/
theorem Obs.iota_of_agreement
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hag : StoredAgreement D)
    (hc : env.Rigid c) (hD : ∀ ls rhs, ¬ D.unfolds c ls rhs)
    (R : ErasedIotaPrimitive D a b) (H : Obs c arity Δ S a t o) : Obs c arity Δ S b t o := by
  classical
  by_cases HA : ∃ name levels, a = .const name levels
  · obtain ⟨name, levels, rfl⟩ := HA
    cases H with
    | const HT => exact (erased_iota_primitive_no_rigid hc hD R rfl).elim
    | delta HT HD HB => exact Obs.alias_root_of_agreement hcon hag HT HD (HB (VLevel.forall₂_equiv_refl _) HD) R
  · rcases H.primitive_heads (erased_iota_primitive_head R) with HH | ⟨name, levels, rhs, HD, HH⟩
    · exact (erased_iota_primitive_no_rigid hc hD R HH).elim
    · obtain ⟨ls, E⟩ := erased_iota_stored_head_bare HD R HH
      exact (HA ⟨name, ls, E⟩).elim

/-- Full enriched stages preserve universe-indexed alias observations. Singleton heads
are separated from stored definitions by their registered iota equations. -/
theorem coherent_stage_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hag : StoredAgreement D)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid c) (hD : ∀ ls rhs, ¬ D.unfolds c ls rhs) :
    ∀ stage {Δ a b S t o},
      ErasedStaticStructureEtaExpansionStage D stage Δ a b →
      Obs c arity Δ S a t o → Obs c arity Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b S t o R H
    rcases R with (R | R) | R
    · exact H.iota_of_agreement hcon hag hc hD R
    · cases R with
      | sort => exact H.not_sort.elim
      | const HL hw =>
        cases H with
        | const HT => exact .const (HT.compute
            (erased_static_structure_eta_expansion_stage_descent heq hs 0)
            (.base (.inl (.inr (.const HL hw)))))
        | delta HT HD HB =>
          obtain ⟨rhs', HD', _⟩ := Definitions.ofEnv_levelCompatible henv HD hw HL
          apply Obs.delta (HT.compute
            (erased_static_structure_eta_expansion_stage_descent heq hs 0)
            (.base (.inl (.inr (.const HL hw))))) HD'
          intro levels'' rhs'' HL' HD''
          exact HB (HL.trans (fun _ _ _ H K => H.trans K) HL') HD''
    · cases R; exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b S t o R H
    rcases R with R | R | R | R | R | R
    · exact ih R H
    · have HH := H.primitive_heads R.2.head
      cases R.2 with
      | intro V _ _ _ =>
        rcases HH with HH | ⟨name, levels, rhs, HD, HH⟩
        · have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans HH)
          exact (V.not_rigid (hn ▸ hc)).elim
        · have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans HH)
          obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq V.equation_eq
          exact (PureObservation.Definitions.ofEnv_no_registered henv V.registered ⟨index, howner⟩
            (by simpa only [hn] using HD)).elim
    · have HH := H.primitive_heads R.head
      cases R with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        rcases HH with HH | ⟨name, levels, rhs, HD, HH⟩
        · exact (hc.pats _ _ hp (by
            simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj HH)).elim
        · have hn : ``Eq.rec = name := Option.some.inj HH
          obtain ⟨value, hreg, hname, _⟩ := PureObservation.Definitions.ofEnv_origin henv HD
          exact (henv.defeq_head_not_pat (definitionRegistry_registered hreg).1.2
            (show value.toDefEq.lhs.stripLams.getAppFnArgs.1 =
              .const value.name (VLevel.params value.uvars) from rfl) hp
            (by simp only [canonicalEqRecPattern, SimplePattern.iota_headConst, hn, hname])).elim
    · exact H.native_identity (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact (H.typing.no_masked_structure
        (erased_static_structure_eta_expansion_stage_descent heq hs stage) H.demand.visible R).elim

/-- Full compatible enriched computation preserves the same universe-indexed alias
observer under a coherent sound collection extension. -/
theorem Obs.coherent_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hag : StoredAgreement D)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid c) (hD : ∀ ls rhs, ¬ D.unfolds c ls rhs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out)
    (HS : S.Typed Δ) (H : Obs c arity Δ S source t o) : Obs c arity Δ S out t o :=
  H.compute (erased_static_structure_eta_expansion_union_descent heq hs)
    (fun ⟨stage, R⟩ H => coherent_stage_observation heq hs hag hcon hc hD stage R H) R HS

/-- The full actual environment discharges soundness, alias agreement and
rigid-head exclusion, including when quotient primitives are registered. -/
theorem Obs.environment_union
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.Rigid c)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion EnvironmentCore.definitions) Δ source out)
    (HS : S.Typed Δ) (H : Obs c arity Δ S source t o) : Obs c arity Δ S out t o :=
  H.coherent_union heq EnvironmentCore.sound EnvironmentCore.storedAgreement hcon hc
    (EnvironmentCore.no_rigid hc) R HS

end PolyAliasDemandProfile
end Lean4Lean.VEnv.Strengthening
