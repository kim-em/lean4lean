import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasDemandTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Alias preservation under coherent extensions of stored definitions

The independent observer always records actual stored equations. A larger
computation collection is admitted when its equations at those instances have
exactly the stored body. No confluence of the enriched relation is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A computation collection cannot select a different body at an actual
stored constant instance. Other heads may have arbitrary additional equations. -/
def StoredAgreement (D : Definitions) : Prop :=
  ∀ {name levels rhs rhs'}, (Definitions.ofEnv env univs henv).unfolds name levels rhs →
    D.unfolds name levels rhs' → rhs = rhs'

/-- Deterministic inclusion of the stored collection supplies exact agreement. -/
theorem storedAgreement_of_deterministic
    (H : ∀ {name levels rhs}, (Definitions.ofEnv env univs henv).unfolds name levels rhs →
      D.unfolds name levels rhs) (HD : D.Deterministic) : StoredAgreement D :=
  fun HS HT => HD (H HS) HT

namespace EnvironmentCore

/-- Optional quotient registration and selected structure equations preserve
exact determinism at every name and universe instance. -/
theorem deterministic : definitions.Deterministic := by
  classical
  by_cases hq : QuotRegistered env
  · rw [definitions_of_quot hq]
    exact ErasedQuotCore.deterministic hq
  · rw [definitions_of_no_quot hq]
    exact fun HA HB => RegisteredStructure.definitions_ofEnv_unique HA HB

/-- The full actual environment collection agrees with all stored aliases. -/
theorem storedAgreement : StoredAgreement definitions :=
  storedAgreement_of_deterministic (fun H => includes_core (.inl H)) deterministic

/-- The actual stored erased core embeds root-for-root into EnvironmentCore. -/
theorem stored_primitive
    (R : ErasedIotaPrimitive (Definitions.ofEnv env univs henv) a b) :
    ErasedIotaPrimitive definitions a b := by
  rcases R with (R | R) | R
  · cases R with
    | delta HD => exact .inl (.inl (.delta (includes_core (.inl HD))))
    | projIota hi hl hg => exact .inl (.inl (.projIota hi hl hg))
  · exact .inl (.inr R)
  · exact .inr R

end EnvironmentCore
namespace AliasDemandProfile
open DemandProfile
variable {c : Name} {arity : Nat}

/-- An extended delta rule at an observed alias selects its certified body.
The concrete pattern alternatives already belong to the actual stored core. -/
theorem Obs.alias_root_of_agreement
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hag : StoredAgreement D)
    (HT : Typing Δ (.const name []) .sort)
    (HD : (Definitions.ofEnv env univs henv).unfolds name [] rhs)
    (HB : Obs c arity Δ S (proofErase [] rhs) .sort .pi)
    (R : ErasedIotaPrimitive D (.const name []) out) : Obs c arity Δ S out .sort .pi := by
  rcases R with (R | R) | R
  · cases R with
    | delta HD' => cases hag HD HD'; exact HB
  · exact Obs.alias_root hcon HT HD HB (.inl (.inr R))
  · exact Obs.alias_root hcon HT HD HB (.inr R)

/-- Extended ordinary roots preserve alias observations when stored bodies
agree and the designated rigid head remains non-unfolding. -/
theorem Obs.iota_of_agreement
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hag : StoredAgreement D)
    (hc : env.Rigid c) (hD : ∀ ls rhs, ¬ D.unfolds c ls rhs)
    (R : ErasedIotaPrimitive D a b) (H : Obs c arity Δ S a t o) : Obs c arity Δ S b t o := by
  classical
  by_cases HA : ∃ name, a = .const name []
  · obtain ⟨name, rfl⟩ := HA
    cases H with
    | const HT => exact (erased_iota_primitive_no_rigid hc hD R rfl).elim
    | delta HT HD HB => exact Obs.alias_root_of_agreement hcon hag HT HD HB R
  · exact (erased_iota_primitive_no_rigid hc hD R
      (H.primitive_head (erased_iota_primitive_head R) (fun name E => HA ⟨name, E⟩))).elim

/-- Full enriched stages preserve finite alias observations. Singleton heads
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
          cases HL
          exact .delta HT HD HB
    · cases R; exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b S t o R H
    rcases R with R | R | R | R | R | R
    · exact ih R H
    · have HH := H.primitive_heads R.2.head
      cases R.2 with
      | intro V _ _ _ =>
        rcases HH with HH | ⟨name, rhs, HD, HH⟩
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
        rcases HH with HH | ⟨name, rhs, HD, HH⟩
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

/-- Full compatible enriched computation preserves the same finite alias
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

end AliasDemandProfile
end Lean4Lean.VEnv.Strengthening
