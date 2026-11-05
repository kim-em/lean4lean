import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFixedTailReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAliasDemandRoots
import Lean4Lean.Theory.Typing.Strengthening.DeclarationHeadExamples
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedControlJoinBoundary

/-! # Recursive types need not admit fixed native references

The admitted recursive declaration D := D -> (Prop -> Prop) retains D down
the domains of every finite Pi unfolding. Each such result still has a strict
ordinary step. Native coherence and fixed-reference return would turn a fixed
stage-zero native output of a variable of type D into a fixed core reduct of D,
which is impossible. The environment extension preserves canonical Eq.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- A finite chain of Pi domains ending at one nullary recursive constant.
Codomains are unrestricted and do not contribute to the persistent marker. -/
inductive RecursiveDomainChain (c : Name) : ProofShape → Prop where
  | const : RecursiveDomainChain c (.const c [])
  | pi : RecursiveDomainChain c A → RecursiveDomainChain c (.forallE A B)

/-- Number of consecutive Pi domains before the leftmost non-Pi node. -/
def recursiveDomainDepth : ProofShape → Nat
  | .forallE A _ => recursiveDomainDepth A + 1
  | _ => 0

/-- Beta contraction cannot remove the left-domain marker. -/
theorem RecursiveDomainChain.beta (H : RecursiveDomainChain c a) (R : ProofShape.BetaRed a b) :
    RecursiveDomainChain c b := by
  induction R with
  | refl => exact H
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | forallE _ _ ih _ => cases H with | pi H => exact .pi (ih H)
  | app | proj | lam | beta => cases H

/-- A core whose constant rule retains the marker and whose roots do not
rewrite Pis preserves the marker under every finite compatible computation. -/
theorem RecursiveDomainChain.compute
    (hconst : ∀ {out}, Step (.const c []) out → RecursiveDomainChain c out)
    (hpi : ∀ {A B out}, ¬ Step (.forallE A B) out)
    (H : RecursiveDomainChain c a) (R : Compute Step a b) : RecursiveDomainChain c b := by
  induction R with
  | base R => cases H with
    | const => exact hconst R
    | pi => exact (hpi R).elim
  | beta R => exact H.beta R
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | forallE _ _ ih _ => cases H with | pi H => exact .pi (ih H)
  | app | proj | lam => cases H

/-- Unfolding the remaining marker is always a strict step, including after
arbitrarily many earlier Pi unfoldings. Hence no marked expression is fixed. -/
theorem RecursiveDomainChain.not_fixed
    (H : RecursiveDomainChain c a)
    (R : ProofShape.Compute Step (.const c []) (.forallE (.const c []) body)) : ¬ ComputeFixed Step a := by
  induction H with
  | const => intro HF; have E := HF R; cases E
  | pi H ih =>
    intro HF
    apply ih
    intro out RO
    exact (ProofShape.forallE.inj (HF (.forallE RO .refl))).1

private theorem RecursiveDomainChain.beta_depth (H : RecursiveDomainChain c a)
    (R : ProofShape.BetaRed a b) : recursiveDomainDepth b = recursiveDomainDepth a := by
  induction R with
  | refl => rfl
  | trans R S ih₁ ih₂ => exact (ih₂ (H.beta R)).trans (ih₁ H)
  | forallE _ _ ih _ => cases H with
    | pi H => exact congrArg (· + 1) (ih H)
  | app | proj | lam | beta => cases H

/-- Compatible computation cannot shorten the marked Pi-domain chain. This
uses only marker preservation at the recursive constant and no Pi root rules. -/
theorem RecursiveDomainChain.depth_mono
    (hconst : ∀ {out}, Step (.const c []) out → RecursiveDomainChain c out)
    (hpi : ∀ {A B out}, ¬ Step (.forallE A B) out)
    (H : RecursiveDomainChain c a) (R : Compute Step a b) :
    recursiveDomainDepth a ≤ recursiveDomainDepth b := by
  induction R with
  | base R => cases H with
    | const => exact Nat.zero_le _
    | pi => exact (hpi R).elim
  | beta R => exact Nat.le_of_eq (H.beta_depth R).symm
  | trans R S ih₁ ih₂ => exact Nat.le_trans (ih₁ H) (ih₂ (H.compute hconst hpi R))
  | forallE _ _ ih _ => cases H with
    | pi H => exact Nat.add_le_add_right (ih H) 1
  | app | proj | lam => cases H

/-- One unfolding at the remaining recursive constant strictly increases
left-domain depth, however many Pi frames already surround it. -/
theorem RecursiveDomainChain.grows
    (H : RecursiveDomainChain c a)
    (R : ProofShape.Compute Step (.const c []) (.forallE (.const c []) body)) :
    ∃ b, Compute Step a b ∧ recursiveDomainDepth a < recursiveDomainDepth b := by
  induction H with
  | const => exact ⟨_, R, by simp [recursiveDomainDepth]⟩
  | pi H ih =>
    obtain ⟨b, Rb, hb⟩ := ih
    exact ⟨_, .forallE Rb .refl, Nat.add_lt_add_right hb 1⟩

variable [Params]
namespace RecursiveFixedReferenceBoundary
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private constant_sort_caller_erase
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedControlJoinBoundary

private theorem definitions_deterministic : EnvironmentCore.definitions.Deterministic := by
  classical
  by_cases hq : QuotRegistered env
  · rw [EnvironmentCore.definitions_of_quot hq]
    exact ErasedQuotCore.deterministic hq
  · rw [EnvironmentCore.definitions_of_no_quot hq]
    exact fun H₁ H₂ => RegisteredStructure.definitions_ofEnv_unique H₁ H₂

private theorem value_erase (hc : env.constants c = some (GuardedEta.declaration c).toVConstant) :
    proofErase [] (GuardedEta.domainValue c) =
      .forallE (.const c []) (.forallE (.sort .zero) (.sort .zero)) := by
  have hD := GuardedEta.domain_typed hc univs ([] : List VExpr)
  have hΓD : OnCtx [GuardedEta.domain c] (env.IsType univs) := ⟨trivial, _, hD⟩
  have hB := GuardedEta.result_typed env univs [GuardedEta.domain c]
  have hΓP : OnCtx (.sort .zero :: [GuardedEta.domain c]) (env.IsType univs) :=
    ⟨hΓD, _, HasType.sort (by trivial)⟩
  rw [show proofErase [] (GuardedEta.domainValue c) = .forallE _ _ from
    if_neg (not_isProof_of_sort (by trivial) (HasType.forallE hD hB)),
    show proofErase [] (GuardedEta.domain c) = .const c [] from
      if_neg (not_isProof_of_sort (by trivial) hD),
    show proofErase [GuardedEta.domain c] GuardedEta.resultType = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓD hB)]
  simp only [GuardedEta.prop]
  rw [show proofErase [GuardedEta.domain c] (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓD (HasType.sort (by trivial))),
    show proofErase (.sort .zero :: [GuardedEta.domain c]) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓP (HasType.sort (by trivial)))]

private theorem constant_root
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c))
    (R : ErasedIotaPrimitive EnvironmentCore.definitions (.const c []) out) :
    out = .forallE (.const c []) (.forallE (.sort .zero) (.sort .zero)) := by
  have hroot (R : ErasedIotaPrimitive (Definitions.ofEnv env univs henv) (.const c []) out) :
      out = proofErase [] (GuardedEta.domainValue c) := by
    obtain ⟨rhs, HR, rfl⟩ := erased_stored_constant_root hcon (Γ := []) (by trivial)
      (GuardedEta.domain_typed hc univs []) R
    cases Definitions.ofEnv_unique henv HD HR
    rfl
  have E : out = proofErase [] (GuardedEta.domainValue c) := by
    rcases R with (R | R) | R
    · cases R with
      | delta HR =>
        cases definitions_deterministic (EnvironmentCore.includes_core (.inl HD)) HR
        rfl
    · exact hroot (.inl (.inr R))
    · exact hroot (.inr R)
  exact E.trans (value_erase hc)

/-- Every finite level-core reduct of the recursive type still admits a
strict ordinary-core step. Universe conversion and arbitrary Pi-codomain
computation cannot produce a fixed reference. -/
theorem recursive_core_reduct_not_fixed
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c))
    (R : Compute (ErasedLevelCore EnvironmentCore.definitions) (.const c []) out) :
    ¬ ComputeFixed (ErasedIotaPrimitive EnvironmentCore.definitions) out := by
  have Hchain : RecursiveDomainChain c out := RecursiveDomainChain.compute
    (Step := ErasedLevelCore EnvironmentCore.definitions) (fun H => by
      rcases H with H | H
      · rw [constant_root hcon hc HD H]; exact .pi .const
      · cases H with | const HL _ => cases HL; exact .const)
    (fun H => erased_level_core_no_pi H) .const R
  have RU : Compute (ErasedIotaPrimitive EnvironmentCore.definitions) (.const c [])
      (.forallE (.const c []) (.forallE (.sort .zero) (.sort .zero))) := by
    rw [← value_erase hc]
    exact .base (.inl (.inl (.delta (EnvironmentCore.includes_core (.inl HD)))))
  exact Hchain.not_fixed RU

/-- The weaker return condition also fails: every core reduct of the recursive
type has an ordinary reduct that cannot compute back in the level core. The
strictly increasing Pi-domain depth excludes cycles as well as fixed points. -/
theorem recursive_core_reduct_no_return
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c))
    (R : Compute (ErasedLevelCore EnvironmentCore.definitions) (.const c []) out) :
    ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) out mid →
      Compute (ErasedLevelCore EnvironmentCore.definitions) mid out) := by
  have hconst {b} (H : ErasedLevelCore EnvironmentCore.definitions (.const c []) b) :
      RecursiveDomainChain c b := by
    rcases H with H | H
    · rw [constant_root hcon hc HD H]; exact .pi .const
    · cases H with | const HL _ => cases HL; exact .const
  have hpi {A B b} : ¬ ErasedLevelCore EnvironmentCore.definitions (.forallE A B) b :=
    erased_level_core_no_pi
  have HC := RecursiveDomainChain.compute hconst hpi .const R
  have RU : Compute (ErasedIotaPrimitive EnvironmentCore.definitions) (.const c [])
      (.forallE (.const c []) (.forallE (.sort .zero) (.sort .zero))) := by
    rw [← value_erase hc]
    exact .base (.inl (.inl (.delta (EnvironmentCore.includes_core (.inl HD)))))
  obtain ⟨mid, RM, HM⟩ := HC.grows RU
  have RM' : Compute (ErasedLevelCore EnvironmentCore.definitions) out mid := RM.mono (fun H => .inl H)
  intro Hreturn
  have Hdepth := (HC.compute hconst hpi RM').depth_mono hconst hpi (Hreturn RM)
  exact (Nat.not_lt_of_ge Hdepth) HM

/-- No native output can serve even as a returning reference when one native
output is the recursive constant. This rules out universal coverage by the
weaker ordinary-reduct return premise, not just by fixed normal references. -/
theorem recursive_native_output_no_return
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e A)
    (Rref : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ e) (.const c []))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) out mid →
      Compute (ErasedLevelCore EnvironmentCore.definitions) mid out) := by
  intro Hreturn
  obtain ⟨P, heP, EP⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_stage_descent heq EnvironmentCore.sound 0) hΓ he RN
  obtain ⟨_, hP⟩ := heP.isType henv hΓ
  have HJ := stage_zero_native_outputs_join heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible hcon) hcon EnvironmentCore.no_rigid
    (EnvironmentCore.typed_core_confluence hcon) hΓ he Rref RN
  have RC : Compute (ErasedLevelCore EnvironmentCore.definitions) (.const c []) out := by
    simpa only [EP] using proofErase_returning_core_join_return EnvironmentCore.sound
      (EnvironmentCore.levelCompatible hcon) hcon hΓ hP (EP ▸ Hreturn) (EP ▸ HJ)
  exact recursive_core_reduct_no_return hcon hc HD RC Hreturn

/-- Recovering the recursive constant once rules out fixed outputs for every
other stage-zero recovery of the same typed source. Internal selections and
final conversion tails may differ freely. -/
theorem recursive_native_output_not_fixed
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c))
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e A)
    (Rref : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ e) (.const c []))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ¬ ComputeFixed (ErasedIotaPrimitive EnvironmentCore.definitions) out := by
  intro HF
  obtain ⟨P, heP, EP⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_stage_descent heq EnvironmentCore.sound 0) hΓ he RN
  obtain ⟨_, hP⟩ := heP.isType henv hΓ
  have HJ := stage_zero_native_outputs_join heq EnvironmentCore.sound
    (EnvironmentCore.levelCompatible hcon) hcon EnvironmentCore.no_rigid
    (EnvironmentCore.typed_core_confluence hcon) hΓ he Rref RN
  have RC : Compute (ErasedLevelCore EnvironmentCore.definitions) (.const c []) out := by
    simpa only [EP] using proofErase_fixed_core_join_return EnvironmentCore.sound
      (EnvironmentCore.levelCompatible hcon) hcon hΓ hP (EP ▸ HF) (EP ▸ HJ)
  exact recursive_core_reduct_not_fixed hcon hc HD RC HF

/-- A typed variable at the recursive type has native recovery, but none of
its complete stage-zero native outputs is fixed by ordinary computation.
This refutes universal fixed-native-reference coverage, not strengthening or
comparison of the variable with itself. -/
theorem recursive_variable_has_no_fixed_native_reference
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c)) :
    ∃ Γ e A, OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ e A ∧
      (∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ e) out) ∧
      ∀ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ e) out →
        ¬ ComputeFixed (ErasedIotaPrimitive EnvironmentCore.definitions) out := by
  let A := GuardedEta.domain c
  let Γ := [A]
  have hA : env.HasType univs [] A (.sort (.succ .zero)) := GuardedEta.domain_typed hc univs []
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨trivial, _, hA⟩
  have hAΓ : env.HasType univs Γ A (.sort (.succ .zero)) := GuardedEta.domain_typed hc univs Γ
  have hv : env.HasType univs Γ (.bvar 0) A := .bvar .zero
  have EA : proofErase [] A = .const c [] := if_neg (not_isProof_of_sort (by trivial) hA)
  have EV : proofErase Γ (.bvar 0) = .bvar 0 := if_neg (not_proof_at_positive_type hΓ hAΓ hv)
  have EO : contextOracle (proofEraseCtx Γ) 0 = .const c [] := by
    simp only [Γ, proofEraseCtx, EA, contextOracle, TypeOracle.cons, ProofShape.liftN]
  have Rref : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ (.bvar 0)) (.const c []) := by
    rw [EV, ← EO]; exact .bvar
  refine ⟨Γ, .bvar 0, A, hΓ, hv, ⟨_, Rref⟩, ?_⟩
  exact fun _ RN => recursive_native_output_not_fixed heq hcon hc HD hΓ hv Rref RN

/-- Fixed-reference coverage fails in the literal universe-control setting
itself. A constant caller accepts Sort 0 at domain Sort 1, but no selected native
Pi has a fixed or returning codomain after that argument is substituted. The
caller does have a native Pi, so initial recovery is not missing. -/
theorem recursive_control_has_no_fixed_result_reference
    (heq : env.HasCanonicalEq) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : env.constants c = some (GuardedEta.declaration c).toVConstant)
    (HD : (Definitions.ofEnv env univs henv).unfolds c [] (GuardedEta.domainValue c)) :
    ∃ Γ f T, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ f (.forallE (.sort (.succ .zero)) T) ∧
      (∃ X Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y)) ∧
      ∀ X Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y) →
        (¬ ComputeFixed (ErasedIotaPrimitive EnvironmentCore.definitions) (Y.inst (.sort .zero))) ∧
        ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) (Y.inst (.sort .zero)) mid →
          Compute (ErasedLevelCore EnvironmentCore.definitions) mid (Y.inst (.sort .zero))) := by
  let A := GuardedEta.domain c
  let Γ := [A]
  have hA : env.HasType univs [] A (.sort (.succ .zero)) := GuardedEta.domain_typed hc univs []
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨trivial, _, hA⟩
  have hAΓ : env.HasType univs Γ A (.sort (.succ .zero)) := GuardedEta.domain_typed hc univs Γ
  have hv : env.HasType univs Γ (.bvar 0) A := .bvar .zero
  have hn := not_proof_at_positive_type hΓ hAΓ hv
  have EA : proofErase [] A = .const c [] := if_neg (not_isProof_of_sort (by trivial) hA)
  have EV : proofErase Γ (.bvar 0) = .bvar 0 := if_neg hn
  obtain ⟨EF, EFp⟩ := constant_sort_caller_erase hΓ hv hn
  rw [EV] at EF EFp
  let f := VExpr.lam (.sort (.succ .zero)) (VExpr.bvar 0).lift
  have hf : env.HasType univs Γ f (.forallE (.sort (.succ .zero)) A.lift) :=
    .lam (.sort (by trivial)) (hv.weakN henv Ctx.LiftN.one)
  have hfp := HasType.app hf (HasType.sort (by trivial))
  have EO : contextOracle (.sort (.succ .zero) :: proofEraseCtx Γ) 1 = .const c [] := by
    simp only [Γ, proofEraseCtx, EA, contextOracle, TypeOracle.cons, ProofShape.liftN]
  have RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ f) (.forallE (.sort (.succ .zero)) (.const c [])) := by
    rw [EF]
    apply ScopedTypeRecovery.lam
    rw [← EO]
    exact .bvar
  have app_native {X Y}
      (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y)) :
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
        (proofEraseCtx Γ) (proofErase Γ (.app f (.sort .zero))) (Y.inst (.sort .zero)) := by
    rw [EFp, ← EF]
    exact .app RN
  have Rbase : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
      (proofEraseCtx Γ) (proofErase Γ (.app f (.sort .zero))) (.const c []) := app_native RF
  exact ⟨Γ, f, A.lift, hΓ, hf, ⟨_, _, RF⟩, fun _ _ RN =>
    ⟨recursive_native_output_not_fixed heq hcon hc HD hΓ hfp Rbase (app_native RN),
      recursive_native_output_no_return heq hcon hc HD hΓ hfp Rbase (app_native RN)⟩⟩

omit [Params] in
/-- Installing the actual recursive declaration over any canonical-Eq base
produces a well-formed canonical-Eq environment with a typed universe-control
function admitting native Pis but no fixed or returning result reference at Sort 0. No
abstract rule or definition-compatibility assumptions remain in this witness.
Thus fixed-reference coverage cannot discharge the general control theorem. -/
theorem canonical_recursive_fixed_reference_failure
    (hbase : base.WF) (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) (U : Nat) :
    ∃ hE : (GuardedEta.extended base c).WF,
      (GuardedEta.extended base c).HasCanonicalEq ∧
      (letI := hE.params U
       ∃ Γ f T, OnCtx Γ ((GuardedEta.extended base c).IsType U) ∧
         (GuardedEta.extended base c).HasType U Γ f (.forallE (.sort (.succ .zero)) T) ∧
         (∃ X Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
           (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y)) ∧
         ∀ X Y, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage EnvironmentCore.definitions 0)
           (proofEraseCtx Γ) (proofErase Γ f) (.forallE X Y) →
           (¬ ComputeFixed (ErasedIotaPrimitive EnvironmentCore.definitions) (Y.inst (.sort .zero))) ∧
           ¬ (∀ {mid}, Compute (ErasedIotaPrimitive EnvironmentCore.definitions) (Y.inst (.sort .zero)) mid →
             Compute (ErasedLevelCore EnvironmentCore.definitions) mid (Y.inst (.sort .zero)))) := by
  let hE := GuardedEta.extended_wf hbase hfresh
  have hEq := GuardedEta.extended_canonicalEq heq hfresh
  refine ⟨hE, hEq, ?_⟩
  letI := hE.params U
  apply recursive_control_has_no_fixed_result_reference (c := c) hEq (fun H => H)
  · change (GuardedEta.extended base c).constants c = some (GuardedEta.declaration c).toVConstant
    simp [GuardedEta.extended, GuardedEta.stub, VEnv.addDefEq]
  · exact guarded_definition hE U

end RecursiveFixedReferenceBoundary
end Lean4Lean.VEnv.Strengthening
