import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputation

/-! # Declaration and projection rules on annotated proof erasures

Closed definition bodies have context-independent erasures. An erased saturated
constructor spine retains its original arguments, with proof fields marked.
Consequently both primitives replay without inventing an inhabitant for a marker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions PatternCompute)
open private erase_app_inv erase_proj_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

namespace ProofShape
/-- Application spines in the erased syntax. -/
def mkApps (f : ProofShape) : List ProofShape → ProofShape
  | [] => f
  | a :: args => mkApps (.app f a) args

/-- Snoc exposes the final application. -/
theorem mkApps_snoc : mkApps f (args ++ [a]) = .app (mkApps f args) a := by
  induction args generalizing f with
  | nil => rfl
  | cons x xs ih => exact ih
end ProofShape

variable [Params]

/-- Erasure cannot introduce a variable absent from the original term. -/
theorem proofErase_closed_liftN (hc : e.ClosedN k) :
    (proofErase Γ e).liftN n k = proofErase Γ e := by
  induction e generalizing Γ k with
  | bvar i =>
    simp only [VExpr.ClosedN] at hc
    simp only [proofErase]
    split <;> simp [ProofShape.liftN, liftVar, hc]
  | sort | const => simp only [proofErase]; split <;> rfl
  | app f a ihf iha =>
    simp only [proofErase]; split
    · rfl
    · simp only [ProofShape.liftN, ihf hc.1, iha hc.2]
  | proj s i m ih =>
    simp only [proofErase]; split
    · rfl
    · simp only [ProofShape.liftN, ih hc]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [proofErase]; split
    · rfl
    · simp only [ProofShape.liftN, ihA hc.1, ihb hc.2]

/-- A closed term typed in the empty context has the same erasure in every
well-formed context, even though proof detection uses the ambient context. -/
theorem proofErase_closed_context (hc : e.Closed)
    (ht : env.HasType univs [] e T) (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ e = proofErase [] e := by
  have W : Ctx.LiftN Γ.length 0 [] Γ := by
    simpa only [List.append_nil] using (Ctx.LiftN.zero (Γ := []) Γ)
  have H := proofErase_liftN (by trivial) hΓ W ht
  simpa only [hc.liftN_eq (Nat.zero_le _), proofErase_closed_liftN hc] using H

private theorem erase_const_inv (H : proofErase Γ e = .const c ls) : e = .const c ls := by
  cases e <;> simp only [proofErase] at H <;> split at H <;> simp_all

/-- Erasure of a visible constructor spine retains a corresponding original
argument at every position, including positions occupied by proof markers. -/
theorem proofErase_const_spine_inv
    (H : proofErase Γ e = ProofShape.mkApps (.const c ls) args) :
    ∃ original, e = mkApps (.const c ls) original ∧ args = original.map (proofErase Γ) := by
  induction args using List.snoc_induction generalizing e with
  | nil => exact ⟨[], erase_const_inv H, rfl⟩
  | snoc args a ih =>
    rw [ProofShape.mkApps_snoc] at H
    obtain ⟨f, a₀, rfl, _, Hf, Ha⟩ := erase_app_inv H
    obtain ⟨args₀, rfl, rfl⟩ := ih Hf
    exact ⟨args₀ ++ [a₀], (mkApps_snoc ..).symm, by simp [Ha]⟩

/-- A typed non-proof constant spine erases structurally, retaining all of its
argument positions even when individual arguments erase to proof markers. -/
theorem proofErase_const_spine (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (mkApps (.const c ls) args) T)
    (hn : ¬ IsProof Γ (mkApps (.const c ls) args)) :
    proofErase Γ (mkApps (.const c ls) args) =
      ProofShape.mkApps (.const c ls) (args.map (proofErase Γ)) := by
  induction args using List.snoc_induction generalizing T with
  | nil => exact if_neg hn
  | snoc args a ih =>
    rw [mkApps_snoc] at ht hn ⊢
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    simp only [proofErase, if_neg hn, ih hf (not_isProof_fn hΓ hf ha hn),
      List.map_append, List.map_cons, List.map_nil, ProofShape.mkApps_snoc]

namespace ProofShape
/-- Concrete erased primitives, independent of the context of their occurrence. -/
inductive Primitive (D : Definitions) : ProofShape → ProofShape → Prop where
  | delta : D.unfolds c ls rhs → Primitive D (.const c ls) (proofErase [] rhs)
  | projIota : env.projections s info → args.length = info.nparams + info.numFields →
      args[info.nparams + i]? = some field →
      Primitive D (.proj s i (mkApps (.const info.ctorName ls) args)) field
end ProofShape

private theorem isProof_congr (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.IsDefEq univs Γ e out T) : IsProof Γ e ↔ IsProof Γ out := by
  constructor
  · rintro ⟨P, hp, hP⟩
    exact ⟨P, ((show env.IsDefEqU univs Γ e out from ⟨_, H⟩).of_l henv hΓ hp).hasType.2, hP⟩
  · rintro ⟨P, hp, hP⟩
    exact ⟨P, ((show env.IsDefEqU univs Γ out e from ⟨_, H.symm⟩).of_l henv hΓ hp).hasType.2, hP⟩

/-- Every typed original declaration step is visible as an erased delta step,
or becomes the empty path when its source and target are proofs. -/
theorem proofErase_delta (hs : D.Sound env univs) (hd : D.unfolds c ls rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (.const c ls) T) :
    ProofShape.Compute (ProofShape.Primitive D) (proofErase Γ (.const c ls)) (proofErase Γ rhs) := by
  have HE := (hs Γ c ls rhs hd).of_l henv hΓ ht
  by_cases hp : IsProof Γ (.const c ls)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
    exact .refl
  · obtain ⟨_, H0⟩ := hs [] c ls rhs hd
    rw [proofErase_closed_context (D.closed hd) H0.hasType.2 hΓ]
    simpa only [proofErase, if_neg hp] using ProofShape.Compute.base (ProofShape.Primitive.delta hd)

/-- Every saturated original projection step erases to field selection, or to
an empty path when the selected result is a proof. -/
theorem proofErase_projIota (hs : D.Sound env univs)
    (hi : env.projections s info) (hl : args.length = info.nparams + info.numFields)
    (hg : args[info.nparams + i]? = some field)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i (mkApps (.const info.ctorName ls) args)) T) :
    ProofShape.Compute (ProofShape.Primitive D)
      (proofErase Γ (.proj s i (mkApps (.const info.ctorName ls) args))) (proofErase Γ field) := by
  have R : PatternCompute D (.proj s i (mkApps (.const info.ctorName ls) args)) field :=
    .base (.projIota hi hl hg)
  have HE := R.simAt hs hΓ T ht
  by_cases hp : IsProof Γ (.proj s i (mkApps (.const info.ctorName ls) args))
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
    exact .refl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    simp only [proofErase, if_neg hp, proofErase_const_spine hΓ hm.hasType.2
      (not_isProof_major hΓ ht hp)]
    exact .base (.projIota hi (by simpa only [List.length_map] using hl)
      (by simp only [List.getElem?_map, hg, Option.map_some]))

/-- Closed declaration unfolding and saturated projection selection replay
from every typed representative of their erased source. -/
theorem erased_primitives_replay (hs : D.Sound env univs) :
    ErasedPrimitiveReplay D (ProofShape.Primitive D) := by
  intro Γ e T out hΓ ht R
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | delta hd =>
    obtain rfl := erase_const_inv hsrc
    obtain ⟨_, HE⟩ := hs [] _ _ _ hd
    exact ⟨_, .base (.base (.delta hd)), proofErase_closed_context (D.closed hd) HE.hasType.2 hΓ⟩
  | projIota hi hl hg =>
    obtain ⟨m, rfl, _, Hm⟩ := erase_proj_inv hsrc
    obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv Hm
    simp only [List.length_map] at hl
    rw [List.getElem?_map] at hg
    obtain ⟨field, hget, hfield⟩ := Option.map_eq_some_iff.mp hg
    exact ⟨field, .base (.projIota hi hl hget), hfield⟩

/-- Every compatible erased beta/declaration/projection path has a typed
original replay. Recursive declaration bodies require no normalization premise. -/
theorem proofErase_primitive_compute_replay (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.Compute (ProofShape.Primitive D) (proofErase Γ e) out) :
    ∃ e', PatternCompute D e e' ∧ proofErase Γ e' = out :=
  proofErase_compute_replay hs (erased_primitives_replay hs) hΓ ht R

/-- A common erased beta/declaration/projection result above inserted binders
proves the original equality below. Intermediate annotations need no lower typing. -/
theorem proofErase_primitive_join_descend (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (Ra : ProofShape.Compute (ProofShape.Primitive D) (proofErase Γ' (a.liftN n k)) out)
    (Rb : ProofShape.Compute (ProofShape.Primitive D) (proofErase Γ' (b.liftN n k)) out) :
    env.IsDefEq univs Γ a b T :=
  proofErase_compute_join_descend hs (erased_primitives_replay hs) hΓ hΓ' W ha hb Ra Rb

end Lean4Lean.VEnv.Strengthening
