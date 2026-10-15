import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKNormal
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots
import Lean4Lean.Theory.Typing.Strengthening.IndexedPrefixBoundary

/-! # Core normality of neutral-endpoint Eq recursors

Visible iota requires the major's constructor; prefixes of fewer than six
arguments cannot match any registered canonical Eq rule.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape

private def spineCount : ProofShape → Nat
  | .app f _ => spineCount f + 1
  | _ => 0

private theorem match_varN_count (H : Matches ((Pattern.const c).varN n) e ls captures) :
    spineCount e = n := by
  induction n generalizing e with
  | zero => cases H; rfl
  | succ n ih => cases H with | var H => exact congrArg (· + 1) (ih H)

variable [Params]

private theorem eqRec_match_excluded
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hp : Pat p r) (hm : Matches p e levels captures)
    (hh : e.constHead = some ``Eq.rec)
    (he : spineCount e ≤ 5 ∨ ∃ f, e = .app f .proof) : False := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  have hn := hm.constHead.symm.trans hh
  cases sp with
  | defn c =>
    have hc : c = ``Eq.rec := Option.some.inj hn
    subst c
    rw [(pat_const_not_unfolding hp).1] at hreg
    cases hreg
  | iota c major ctor fields =>
    have hc : c = ``Eq.rec := by
      rw [Pattern.constHead_eq, SimplePattern.iota_headConst] at hn
      exact Option.some.inj hn
    subst c
    have hmj := ConstructorObservation.recursor_major_offset hreg hp
    rw [hoff] at hmj
    cases hm with
    | app hfn harg =>
      rcases he with he | ⟨f, E⟩
      · have H := match_varN_count hfn
        change spineCount _ + 1 ≤ 5 at he
        omega
      · cases E
        exact harg.ne_proof rfl

/-- No ordinary primitive contracts an unsaturated canonical Eq prefix, or an
Eq application whose final argument has erased to a proof marker. -/
theorem erased_iota_eqRec_no_root
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hh : e.constHead = some ``Eq.rec)
    (he : (∃ args levels, e = mkApps (.const ``Eq.rec levels) args ∧ args.length ≤ 5) ∨
      ∃ f, e = .app f .proof) : ¬ ErasedIotaPrimitive D e out := by
  have he' : spineCount e ≤ 5 ∨ ∃ f, e = .app f .proof := by
    rcases he with ⟨args, levels, rfl, hlen⟩ | H
    · left
      have count : ∀ args, spineCount (mkApps (.const ``Eq.rec levels) args) = args.length := by
        intro args
        induction args using List.snoc_induction with
        | nil => rfl
        | snoc args a ih => simp only [mkApps_snoc, spineCount, ih, List.length_append,
            List.length_cons, List.length_nil, Nat.zero_add]
      simpa only [count] using hlen
    · exact .inr H
  intro H
  rcases H with (H | H) | H
  · cases H with
    | delta H => cases Option.some.inj hh; exact hD _ _ H
    | projIota => cases hh
  · cases H with
    | select hp _ hm | apply hp _ hm => exact eqRec_match_excluded hreg hoff hp hm hh he'
  · cases H with
    | intro hp _ _ hm => exact eqRec_match_excluded hreg hoff hp hm hh he'

omit [Params] in
/-- Normal arguments give a normal constant spine when primitives are excluded
at every prefix. This checks all prefixes, not only the saturated root. -/
theorem ProofShape.NormalSyntax.mkApps
    (hroot : ∀ args' out, args'.length ≤ args.length →
      ¬ Step (mkApps (.const c levels) args') out)
    (hargs : ∀ a ∈ args, NormalSyntax Step a) :
    NormalSyntax Step (mkApps (.const c levels) args) := by
  induction args using List.snoc_induction with
  | nil => exact ⟨fun out => hroot [] out (by simp), trivial⟩
  | snoc args a ih =>
    rw [mkApps_snoc]
    refine ⟨fun out => by rw [← mkApps_snoc]; exact hroot _ out (Nat.le_refl _), ?_, ?_,
      hargs a (by simp)⟩
    · intro A b E
      have H := congrArg constHead E
      simp only [constHead_mkApps, constHead] at H
      cases H
    · apply ih
      · intro args' out hlen
        apply hroot args' out
        simp only [List.length_append, List.length_cons, List.length_nil] at *
        omega
      · intro a ha
        exact hargs a (List.mem_append_left _ ha)

/-- A full proof-major Eq recursor is core-normal when its five earlier
arguments are normal and canonical registration excludes shorter matches. -/
theorem eqRec_proof_core_normal
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hargs : ∀ t ∈ [α, a, M, m, b], NormalSyntax (ErasedIotaPrimitive D) t) :
    NormalSyntax (ErasedIotaPrimitive D) (eqRec v w α a M m b .proof) := by
  have hf : NormalSyntax (ErasedIotaPrimitive D)
      (mkApps (.const ``Eq.rec [v, w]) [α, a, M, m, b]) := by
    apply NormalSyntax.mkApps _ hargs
    intro args out hlen
    exact erased_iota_eqRec_no_root hreg hoff hD (constHead_mkApps _ _)
      (.inl ⟨args, _, rfl, hlen⟩)
  refine ⟨fun out => erased_iota_eqRec_no_root hreg hoff hD rfl (.inr ⟨_, rfl⟩), ?_, hf,
    ?_⟩
  · intro A b E; cases E
  · exact ⟨fun out H => erased_iota_primitive_head H, trivial⟩

omit [Params] in
/-- Distinct variable endpoints supply the whole-term K guard invariant when
all remaining captures already satisfy it. -/
theorem ProofShape.NeutralKGuards.eqRec_bvars
    (hα : NeutralKGuards α) (hM : NeutralKGuards M) (hm : NeutralKGuards m)
    (hne : i ≠ j) : NeutralKGuards (eqRec v w α (.bvar i) M m (.bvar j) .proof) := by
  simp only [NeutralKGuards, eqRec] at ⊢
  simp only [ProofShape.app.injEq, ProofShape.const.injEq, List.cons.injEq] at ⊢
  simp only [reduceCtorEq, false_and, false_implies, implies_true, true_and,
    and_true, hα, hM, hm]
  intro v' w' α' a' M' m' b' p' H
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, Ea⟩, _⟩, _⟩, Eb⟩, _⟩ := H
  exact ⟨i, j, Ea.symm, Eb.symm, hne⟩

/-- Every old compared-K computation from this entire recursor is the identity.
The hypotheses explicitly check all captures and all core prefix computations. -/
theorem eqRec_distinct_variables_fixed
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hα : NormalSyntax (ErasedIotaPrimitive D) α) (hM : NormalSyntax (ErasedIotaPrimitive D) M)
    (hm : NormalSyntax (ErasedIotaPrimitive D) m)
    (gα : NeutralKGuards α) (gM : NeutralKGuards M) (gm : NeutralKGuards m) (hne : i ≠ j)
    (R : Compute (ErasedComparedKStage D stage)
      (eqRec v w α (.bvar i) M m (.bvar j) .proof) out) :
    out = eqRec v w α (.bvar i) M m (.bvar j) .proof := by
  apply (NeutralKGuards.eqRec_bvars gα gM gm hne).fixed_comparedK _ R
  apply eqRec_proof_core_normal hreg hoff hD
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact hα
  · exact ⟨fun _ H => erased_iota_primitive_head H, trivial⟩
  · exact hM
  · exact hm
  · exact ⟨fun _ H => erased_iota_primitive_head H, trivial⟩

end Lean4Lean.VEnv.Strengthening
