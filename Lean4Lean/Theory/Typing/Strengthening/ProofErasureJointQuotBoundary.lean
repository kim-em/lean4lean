import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointSortExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKCore
import Lean4Lean.Theory.Typing.Strengthening.StructurePrefixDisjoint

/-! # The missing proposition-source quotient rule in joint stages

Ordinary quotient iota needs a visible constructor major. General singleton
prefixes cannot apply to Quot.lift, which is not in the recursor registry.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private spineCount match_varN_count from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKCore
open private scoped_normal_fixed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

private theorem quot_match_excluded (hq : QuotRegistered env)
    (hp : Pat p r) (hm : ProofShape.Matches p e levels captures)
    (hh : e.constHead = some ``Quot.lift)
    (he : spineCount e ≤ 5 ∨ ∃ f, e = .app f .proof) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  have hn := hm.constHead.symm.trans hh
  cases sp with
  | defn c =>
    have hc : c = ``Quot.lift := Option.some.inj hn
    subst c
    exact (pat_const_not_unfolding hp).2 hq rfl
  | iota c major ctor fields =>
    have hc : c = ``Quot.lift := by
      rw [Pattern.constHead_eq, SimplePattern.iota_headConst] at hn
      exact Option.some.inj hn
    subst c
    have hmajor : major = 5 := by
      rcases pat_recursor hp with ⟨data, _, _, _, hl, _⟩ | ⟨_, _, hm, _⟩
      · rw [recursorData_quot hq] at hl; cases hl
      · exact hm
    subst major
    cases hm with
    | app hfn harg =>
      rcases he with he | ⟨f, E⟩
      · have H := match_varN_count hfn
        change spineCount _ + 1 ≤ 5 at he
        omega
      · cases E
        exact harg.ne_proof rfl

private theorem quot_core_no_root (hq : QuotRegistered env)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Quot.lift levels rhs)
    (hh : e.constHead = some ``Quot.lift)
    (he : spineCount e ≤ 5 ∨ ∃ f, e = .app f .proof) :
    ¬ ErasedIotaPrimitive D e out := by
  intro H
  rcases H with (H | H) | H
  · cases H with
    | delta H => cases Option.some.inj hh; exact hD _ _ H
    | projIota => cases hh
  · cases H with
    | select hp _ hm | apply hp _ hm => exact quot_match_excluded hq hp hm hh he
  · cases H with
    | intro hp _ _ hm => exact quot_match_excluded hq hp hm hh he

/-- Joint stages add no quotient prefix: no registered singleton has that name,
and the specialized prefix has Eq.rec as its head. Thus the ordinary stuck
quotient root stays stuck at every stage, independently of its guards. -/
theorem erased_joint_quot_no_root (hq : QuotRegistered env)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Quot.lift levels rhs)
    (hh : e.constHead = some ``Quot.lift)
    (he : (∃ args levels, e = ProofShape.mkApps (.const ``Quot.lift levels) args ∧ args.length ≤ 5) ∨
      ∃ f, e = .app f .proof) :
    ∀ stage Δ out, ¬ ErasedJointStage D stage Δ e out := by
  have he' : spineCount e ≤ 5 ∨ ∃ f, e = .app f .proof := by
    rcases he with ⟨args, levels, rfl, hlen⟩ | H
    · left
      have count : ∀ args, spineCount (ProofShape.mkApps (.const ``Quot.lift levels) args) = args.length := by
        intro args
        induction args using List.snoc_induction with
        | nil => rfl
        | snoc args a ih => simp only [ProofShape.mkApps_snoc, spineCount, ih,
            List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      simpa only [count] using hlen
    · exact .inr H
  intro stage
  induction stage with
  | zero => exact fun _ _ => quot_core_no_root hq hD hh he'
  | succ stage ih =>
    intro Δ out H
    rcases H with H | H | H
    · exact ih _ _ H
    · cases H.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans hh)
        have hl := V.lookup
        rw [hn, recursorData_quot hq] at hl
        cases hl
    · cases H with
      | intro _ => exact (by decide : (``Eq.rec : Name) ≠ ``Quot.lift) (Option.some.inj hh)

private theorem core_no_quot (hq : QuotRegistered env) :
    ¬ ErasedCore.definitions.unfolds ``Quot.lift levels rhs := by
  rintro (H | H)
  · obtain ⟨df, ls, hd, _, _, he, _⟩ := H
    have hh := henv.quotLift_not_definition hq.equation hd
    generalize heq : df.lhs = lhs at he
    cases lhs with
    | const c us =>
      have hc := (VExpr.const.inj he).1
      subst c
      exact hh us heq
    | _ => simp only [VExpr.instL] at he; cases he
  · exact H.not_quotient hq rfl

namespace JointQuotBoundary
/-- The normal retained fragment needed for quotient captures. -/
inductive Simple : ProofShape → Prop where
  | proof : Simple .proof
  | bvar : Simple (.bvar i)
  | sort : Simple (.sort u)
  | lam : Simple A → Simple b → Simple (.lam A b)
  | forallE : Simple A → Simple B → Simple (.forallE A B)

omit [Params] in
/-- This fragment is stable under insertion, including beneath annotations. -/
theorem Simple.liftN (H : Simple e) : Simple (e.liftN n k) := by
  induction H generalizing k with
  | proof => exact .proof
  | bvar => exact .bvar
  | sort => exact .sort
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB

private theorem Simple.normal (H : Simple e) :
    ProofShape.NormalSyntax (ErasedJointStage D stage Δ) e := by
  induction H with
  | proof | bvar | sort => exact ⟨fun _ R => erased_joint_stage_head stage R, trivial⟩
  | lam _ _ ihA ihb | forallE _ _ ihA ihb =>
    exact ⟨fun _ R => erased_joint_stage_head stage R, ihA, ihb⟩

/-- A proof-major Quot.lift with five simple captures is fixed by every finite
joint-stage computation, at every raw context. This excludes all alternate
paths through arguments and annotations, not just its outermost reduction. -/
theorem fixed (hq : QuotRegistered env)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Quot.lift levels rhs)
    (hlen : args.length = 5) (hargs : ∀ a ∈ args, Simple a)
    (R : ProofShape.ScopedCompute (ErasedJointStage D stage) Δ
      (.app (ProofShape.mkApps (.const ``Quot.lift levels) args) .proof) out) :
    out = .app (ProofShape.mkApps (.const ``Quot.lift levels) args) .proof := by
  apply scoped_normal_fixed R
  intro Δ
  refine ⟨fun out => erased_joint_quot_no_root hq hD
    (by simp only [ProofShape.constHead, ProofShape.constHead_mkApps]) (.inr ⟨_, rfl⟩) stage Δ out,
    ?_, ?_, (Simple.normal Simple.proof)⟩
  · intro A b E
    have H := congrArg ProofShape.constHead E
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at H
    cases H
  · apply ProofShape.NormalSyntax.mkApps
    · intro args' out hl
      exact erased_joint_quot_no_root hq hD (ProofShape.constHead_mkApps _ _)
        (.inl ⟨args', _, rfl, hlen ▸ hl⟩) stage Δ out
    · intro a ha; exact (hargs a ha).normal

private def relationType : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))
private def compatibility : VExpr :=
  .forallE (.bvar 1) (.forallE (.bvar 2)
    (.forallE (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
      (eqApp (.succ (.succ .zero)) (.sort (.succ .zero))
        (.app (.lam (.bvar 4) (.sort .zero)) (.bvar 2))
        (.app (.lam (.bvar 4) (.sort .zero)) (.bvar 1)))))
private def quotientType : VExpr := mkApps (.const ``Quot [.zero]) [.bvar 2, .bvar 1]
private def context : List VExpr := [quotientType, compatibility, relationType, .sort .zero]
private def source : VExpr := mkApps (.const ``Quot.lift [.zero, .succ (.succ .zero)])
  [.bvar 3, .bvar 2, .sort (.succ .zero), .lam (.bvar 3) (.sort .zero), .bvar 1, .bvar 0]

local syntax "quot_type_tac" : tactic
macro_rules | `(tactic| quot_type_tac) => `(tactic|
  first
  | refine HasType.forallE (u := ?_) (v := ?_) ?_ ?_ <;> [skip; skip; quot_type_tac; quot_type_tac]
  | exact HasType.sort (by trivial)
  | refine HasType.bvar ?_; lookup_tac
  | refine HasType.app' (A := ?_) (B := ?_) ?_ ?_ ?_ <;> [skip; skip; quot_type_tac; quot_type_tac; exact rfl]
  | refine HasType.const' (ci := ?_) ?_ ?_ ?_ ?_ <;> [skip; assumption; simp <;> trivial; exact rfl; exact rfl]
  | refine HasType.lam (u := ?_) ?_ ?_ <;> [skip; quot_type_tac; quot_type_tac])

private theorem context_wf (heq : env.HasCanonicalEq) (hq : QuotRegistered env) :
    OnCtx context (env.IsType univs) := by
  have he := heq.1
  have hq := hq.quotient
  refine ⟨⟨⟨⟨trivial, .succ .zero, HasType.sort (by trivial)⟩, .imax .zero (.imax .zero (.succ .zero)), ?_⟩, .imax .zero (.imax .zero (.imax .zero .zero)), ?_⟩, .zero, ?_⟩
  · exact HasType.forallE (HasType.bvar .zero)
      (HasType.forallE (HasType.bvar (.succ .zero)) (HasType.sort (by trivial)))
  · dsimp [context, relationType, compatibility, quotientType, eqApp, mkApps]
    apply HasType.forallE
    · quot_type_tac
    apply HasType.forallE
    · quot_type_tac
    apply HasType.forallE
    · quot_type_tac
    apply HasType.eqApp heq (by trivial)
    · exact .sort (by trivial)
    · exact HasType.app (HasType.lam (HasType.bvar (by lookup_tac))
        (HasType.sort (l := .zero) (by trivial))) (HasType.bvar (by lookup_tac))
    · exact HasType.app (HasType.lam (HasType.bvar (by lookup_tac))
        (HasType.sort (l := .zero) (by trivial))) (HasType.bvar (by lookup_tac))
  · dsimp [context, relationType, compatibility, quotientType, eqApp, mkApps]
    quot_type_tac

private theorem source_typed (hq : QuotRegistered env) :
    env.HasType univs context source (.sort (.succ .zero)) := by
  have hl := hq.lift
  dsimp [context, source, relationType, compatibility, quotientType, eqApp, mkApps]
  refine HasType.app' (HasType.app' (HasType.app' (HasType.app' (HasType.app' (HasType.app'
    (HasType.const hl (by simp; trivial) rfl) ?_ rfl) ?_ rfl) ?_ rfl) ?_ rfl) ?_ rfl) ?_ rfl
  all_goals quot_type_tac

private theorem source_eq_sort (heq : env.HasCanonicalEq) (hq : QuotRegistered env) :
    env.IsDefEq univs context source (.sort .zero) (.sort (.succ .zero)) := by
  have hΓ := context_wf heq hq
  have ht := source_typed hq
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  have HP := QuotPrefixUnfold.atFive henv hΓ hq (by trivial) (by trivial) (by rfl) ⟨_, hf⟩
  have HE := IsDefEq.appDF ((HP.defeq henv hΓ).of_l henv hΓ hf) hx
  have HB : VExpr.BetaRed
      (.app (.lam (mkApps (.const ``Quot [.zero]) [.bvar 3, .bvar 2])
        (.app (VExpr.lam (.bvar 3) (.sort .zero)).lift
          (mkApps (QuotPrefixUnfolding.propInhabitant .zero) [(VExpr.bvar 3).lift, (VExpr.bvar 2).lift, .bvar 0])))
        (.bvar 0)) (.sort .zero) := by
    apply VExpr.BetaRed.trans .beta
    simp only [VExpr.inst, VExpr.lift, VExpr.liftN, instVar]
    exact .beta
  exact IsDefEq.trans_l henv hΓ ht (HE.trans (HB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ HE.hasType.2))

private theorem simple_variable (Γ : List VExpr) (i : Nat) : Simple (proofErase Γ (.bvar i)) := by
  unfold proofErase
  split
  · exact .proof
  · exact .bvar

private theorem simple_sort (Γ : List VExpr) (u : VLevel) : Simple (proofErase Γ (.sort u)) := by
  unfold proofErase
  split
  · exact .proof
  · exact .sort

private theorem erased_source (heq : env.HasCanonicalEq) (hq : QuotRegistered env) :
    ∃ args, args.length = 5 ∧ (∀ a ∈ args, Simple a) ∧
      proofErase context source = .app
        (ProofShape.mkApps (.const ``Quot.lift [.zero, .succ (.succ .zero)]) args) .proof := by
  have hΓ := context_wf heq hq
  have ht := source_typed hq
  have hquot := hq.quotient
  have hQ : env.HasType univs [compatibility, relationType, .sort .zero] quotientType (.sort .zero) := by
    dsimp [compatibility, relationType, quotientType, eqApp, mkApps]
    quot_type_tac
  have hp : IsProof context (.bvar 0) := ⟨quotientType.lift, .bvar .zero, hQ.weak henv⟩
  have E := proofErase_const_spine hΓ ht (not_isProof_of_sort hΓ ht)
  change proofErase context source = ProofShape.mkApps _
    ((([.bvar 3, .bvar 2, .sort (.succ .zero), .lam (.bvar 3) (.sort .zero), .bvar 1] : List VExpr) ++ [VExpr.bvar 0]).map
      (proofErase context)) at E
  rw [List.map_append, List.map_singleton, ProofShape.mkApps_snoc, proofErase_eq_proof.2 hp] at E
  refine ⟨_, by simp, ?_, E⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact simple_variable _ _
  · exact simple_variable _ _
  · exact simple_sort _ _
  · unfold proofErase
    split
    · exact .proof
    · exact .lam (simple_variable _ _) (simple_sort _ _)
  · exact simple_variable _ _

/-- An actual well-typed type equals Prop, but no joint stage exposes any sort
from its erasure, even after arbitrary front lifts and at any raw context.
All stored equations are present. The missing rule is the proposition-source
quotient prefix, not a comparison guard or a finite-stage bound. -/
theorem sort_exposure_failure (heq : env.HasCanonicalEq) (hq : QuotRegistered env) :
    ∃ Γ T, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ T (.sort (.succ .zero)) ∧
      env.IsDefEq univs Γ T (.sort .zero) (.sort (.succ .zero)) ∧
      ∀ n Δ w, ¬ ProofShape.ScopedCompute (ErasedJointUnion ErasedCore.definitions) Δ
        ((proofErase Γ T).liftN n) (.sort w) := by
  refine ⟨context, source, context_wf heq hq, source_typed hq, source_eq_sort heq hq, ?_⟩
  intro n Δ w R
  obtain ⟨args, hlen, hs, E⟩ := erased_source heq hq
  rw [E] at R
  simp only [ProofShape.liftN, ProofShape.liftN_mkApps] at R
  obtain ⟨stage, R⟩ := R.finite_stage erased_joint_stage_mono
  have H := fixed hq (fun _ _ => core_no_quot hq)
    (by simpa only [List.length_map] using hlen)
    (by intro a ha; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha; exact (hs b hb).liftN) R
  cases H

/-- The current concrete joint union does not satisfy re-synthesis in a
canonical-Eq environment with the primitive quotient. Comparison recursion
cannot repair an omitted quotient-prefix computation rule. This refutes this
candidate semantic premise, not canonical-Eq strengthening itself. -/
theorem not_resynthesis (heq : env.HasCanonicalEq) (hq : QuotRegistered env)
    (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    ¬ JointCarrierDomainResynthesis (ErasedJointUnion ErasedCore.definitions) Step := by
  intro H
  obtain ⟨Γ, T, hΓ, hT, HT, HN⟩ := sort_exposure_failure heq hq
  obtain ⟨w, R⟩ := H.sort_exposure_above hΓ hT ⟨_, HT⟩
  simp only [ProofShape.liftN_add] at R
  exact HN 2 _ w R

end JointQuotBoundary
end Lean4Lean.VEnv.Strengthening
