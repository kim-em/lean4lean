import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-! # Reindexing function carriers with neutral terminal results

A telescope terminating in a variable-headed result supplies only ordinary
comparison at that result. Its carrier guard can therefore replace the terminal
result while retaining every displayed domain. This remains valid through
arbitrary compatible computation of those domains and neutral arguments.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private variableHead variableHead_mkApps bvar_spine_not_primitive
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-- Any finite Pi telescope whose final result is a variable-headed application.
Domains and arguments may contain computations or diverging terms. -/
inductive NeutralResult : ProofShape → Prop where
  | neutral : NeutralResult (mkApps (.bvar i) args)
  | forallE : NeutralResult B → NeutralResult (.forallE A B)

/-- Keep a displayed Pi telescope and replace its terminal result. The new
result is raw syntax in the scope of all the retained binders. -/
def replaceResult : ProofShape → ProofShape → ProofShape
  | .forallE A B, result => .forallE A (replaceResult B result)
  | _, result => result

private theorem replaceResult_neutral (i args result) :
    replaceResult (mkApps (.bvar i) args) result = result := by
  induction args using List.snoc_induction with
  | nil => rfl
  | snoc args a ih => rw [mkApps_snoc]; rfl

private theorem NeutralResult.constHead (H : NeutralResult A) : A.constHead = none := by
  cases H with
  | neutral => simp only [constHead_mkApps, ProofShape.constHead]
  | forallE => rfl

private theorem NeutralResult.forall_body (H : NeutralResult (.forallE A B)) : NeutralResult B := by
  generalize E : ProofShape.forallE A B = source at H
  cases H with
  | neutral =>
    have HE := congrArg variableHead E
    simp only [variableHead, variableHead_mkApps] at HE
    cases HE
  | forallE H => cases E; exact H

private theorem NeutralResult.not_subsingleton [Params]
    (H : NeutralResult A) (HS : SubsingletonCarrier A) : False := by
  induction HS with
  | unit => have HE := H.constHead; simp only [constHead_mkApps, ProofShape.constHead] at HE; cases HE
  | forallE HS ih => exact ih H.forall_body

private theorem NeutralResult.beta (N : NeutralResult A) (R : BetaRed A A') :
    NeutralResult A' ∧ BetaRed (replaceResult A result) (replaceResult A' result) := by
  induction N generalizing A' with
  | neutral =>
    obtain ⟨args', rfl, _⟩ := R.bvar_spine
    exact ⟨.neutral, by simp only [replaceResult_neutral]; exact .refl⟩
  | forallE N ih =>
    obtain ⟨D', B', rfl, RD, RB⟩ := beta_forallE_parts R
    obtain ⟨NB, RR⟩ := ih RB
    exact ⟨.forallE NB, .forallE RD RR⟩

private theorem neutral_compute_result
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (mkApps (.bvar i) args) out) :
    NeutralResult out ∧ ScopedCompute Step Δ
      (replaceResult (mkApps (.bvar i) args) result) (replaceResult out result) := by
  obtain ⟨args', rfl, _⟩ := R.bvar_spine hhead
  exact ⟨.neutral, by simp only [replaceResult_neutral]; exact .refl⟩

/-- Computation preserves neutral-result telescopes. Replacing their terminal
result mirrors the same domain computations while discarding only computation
inside the old neutral result's arguments. No confluence is needed. -/
theorem ScopedCompute.replace_neutral_result
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ A A') (N : NeutralResult A) :
    NeutralResult A' ∧ ScopedCompute Step Δ (replaceResult A result) (replaceResult A' result) := by
  induction R with
  | base H =>
    cases N with
    | neutral => exact (bvar_spine_not_primitive _ (hhead H)).elim
    | forallE => exact (hhead H).elim
  | beta H =>
    obtain ⟨N', HR⟩ := N.beta H
    exact ⟨N', .beta HR⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨N₁, HR₁⟩ := ih₁ N
    obtain ⟨N₂, HR₂⟩ := ih₂ N₁
    exact ⟨N₂, HR₁.trans HR₂⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨N', RR⟩ := ihB N.forall_body
    exact ⟨.forallE N', .forallE RA RR⟩
  | app RA RB =>
    generalize E : ProofShape.app _ _ = source at N
    cases N with
    | neutral => exact neutral_compute_result hhead (E ▸ ScopedCompute.app RA RB)
    | forallE => cases E
  | proj =>
    generalize E : ProofShape.proj _ _ _ = source at N
    cases N with
    | neutral =>
      have HE := congrArg variableHead E
      simp only [variableHead, variableHead_mkApps] at HE
      cases HE
    | forallE => cases E
  | lam =>
    generalize E : ProofShape.lam _ _ = source at N
    cases N with
    | neutral =>
      have HE := congrArg variableHead E
      simp only [variableHead, variableHead_mkApps] at HE
      cases HE
    | forallE => cases E

variable [Params]
/-- A joint guard at a neutral-result function telescope transfers to any new
terminal result with all binder domains retained. This includes nested function
guards, endpoint reduction, and arbitrary intermediate carrier computation.
Sound use still requires endpoint typings at the chosen target carrier. -/
theorem JointCarrierGuard.replace_neutral_result
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (N : NeutralResult A) (H : JointCarrierGuard Step Δ A a b) :
    JointCarrierGuard Step Δ (replaceResult A result) a b := by
  change JointCheck Step Δ (.carrier A) a b at H
  generalize E : JointCheckKind.carrier A = kind at H
  induction H generalizing A result with
  | carrierChecked H => exact .carrierChecked H
  | carrierSubsingleton HS => cases E; exact (N.not_subsingleton HS).elim
  | carrierFunction S H ih =>
    cases E
    exact .carrierFunction S (ih N.forall_body rfl)
  | carrierSymm H ih => exact .carrierSymm (ih N E)
  | carrierCompute R H ih =>
    cases E
    obtain ⟨N', RR⟩ := R.replace_neutral_result hhead N
    exact .carrierCompute RR (ih N' rfl)
  | carrierReduce RA RB H ih => exact .carrierReduce RA RB (ih N E)
  | carrierIntro | carrierNested =>
    cases E
    have HE := N.constHead
    simp only [constHead_mkApps, ProofShape.constHead] at HE
    cases HE
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

end Lean4Lean.VEnv.Strengthening.ProofShape
