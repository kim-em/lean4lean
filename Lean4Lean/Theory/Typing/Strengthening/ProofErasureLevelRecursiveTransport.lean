import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFixedTailReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreEtaTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreNeutralSpines

/-! # Comparisons whose references may continue computing

Typed join leaves may reduce indefinitely. Typed eta and fixed comparison leaves
preserve eta differences without requiring a common reduct. Pi and lambda frames combine
these two behaviors, with independent computation in every component. Coverage
of arbitrary checking certificates, especially reducible applications, remains
open; no forward-transport oracle is a constructor of this fragment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A recursive level-core comparison fragment. Typed eta and join leaves need
no fixedness. An additional fixed-leaf constructor admits arbitrary raw checks.
Leaf typings are actual witnesses used for confluence and universe-return arguments; the raw
comparison conclusion can subsequently be embedded at any checking context. -/
inductive LevelRecursiveGuard (D : Definitions) : Bool → ProofShape → ProofShape → Prop where
  | join (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (HJ : ComputeJoin (ErasedLevelCore D) (proofErase Γ a) (proofErase Γ b)) :
      LevelRecursiveGuard D mode (proofErase Γ a) (proofErase Γ b)
  | fixed (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (HA : ComputeFixed (ErasedIotaPrimitive D) (proofErase Γ a))
      (HB : ComputeFixed (ErasedIotaPrimitive D) (proofErase Γ b))
      (H : RawCheckedCompare (ErasedLevelCore D) mode (proofErase Γ a) (proofErase Γ b)) :
      LevelRecursiveGuard D mode (proofErase Γ a) (proofErase Γ b)
  | eta (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a T)
      (hb : env.HasType univs Γ b T)
      (H : EtaHead (proofErase Γ a) (proofErase Γ b)) :
      LevelRecursiveGuard D true (proofErase Γ a) (proofErase Γ b)
  | neutral (hlen : args.length = args'.length)
      (H : ∀ i (hi : i < args.length),
        LevelRecursiveGuard D true args[i] (args'[i]'(hlen ▸ hi))) :
      LevelRecursiveGuard D mode (ProofShape.mkApps (.bvar index) args)
        (ProofShape.mkApps (.bvar index) args')
  | lam : LevelRecursiveGuard D false A A' → LevelRecursiveGuard D mode b b' →
      LevelRecursiveGuard D mode (.lam A b) (.lam A' b')
  | lamCommon : LevelRecursiveGuard D true b b' →
      LevelRecursiveGuard D true (.lam A b) (.lam A' b')
  | forallE : LevelRecursiveGuard D false A A' → LevelRecursiveGuard D false B B' →
      LevelRecursiveGuard D mode (.forallE A B) (.forallE A' B')
  | compute (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (HA : Compute (ErasedLevelCore D) (proofErase Γ a) a')
      (HB : Compute (ErasedLevelCore D) (proofErase Γ b) b')
      (H : LevelRecursiveGuard D mode a' b') :
      LevelRecursiveGuard D mode (proofErase Γ a) (proofErase Γ b)
  | symm : LevelRecursiveGuard D mode a b → LevelRecursiveGuard D mode b a

omit [Params] in
private theorem pointwise_list {R : α → β → Prop} {as : List α} {bs : List β}
    (hlen : as.length = bs.length)
    (H : ∀ i (hi : i < as.length) (hj : i < bs.length), R as[i] bs[i]) :
    List.Forall₂ R as bs := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => exact .nil
    | cons b bs => cases hlen
  | cons a as ih => cases bs with
    | nil => cases hlen
    | cons b bs =>
      exact .cons (H 0 (by simp) (by simp))
        (ih (Nat.succ.inj hlen) (fun i hi hj => H (i+1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj)))

private theorem compare_spine (H : List.Forall₂ (RawCheckedCompare Step true) args args')
    (HF : RawCheckedCompare Step false f f') :
    RawCheckedCompare Step mode (ProofShape.mkApps f args) (ProofShape.mkApps f' args') := by
  induction H generalizing f f' with
  | nil => cases mode <;> first | exact HF | exact HF.common
  | cons H _ ih => exact ih (.app HF H)

/-- Independent level-core paths preserve comparison for the recursive
fragment. Typed confluence handles evolving join leaves; fixed leaves return
locally. Typed eta reflects fresh-argument computation; neutral spines recurse
through their arguments. Neither entire endpoint must normalize, return, or join
the other. -/
theorem LevelRecursiveGuard.forward
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode a b)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    RawCheckedCompare (ErasedLevelCore D) mode a' b' := by
  induction H generalizing a' b' with
  | join hΓ ha hb HJ =>
    have H := (ComputeJoin.of_compute RA).symm.trans_typed hc hΓ ha HJ
    obtain ⟨shared, RL, RR⟩ := H.trans_typed hc hΓ hb (.of_compute RB)
    exact .compute RL RR (.base .refl)
  | fixed hΓ ha hb HA HB H =>
    have RL := proofErase_fixed_core_join_return hs hl hcon hΓ ha HA
      (ComputeJoin.of_compute RA).symm
    have RR := proofErase_fixed_core_join_return hs hl hcon hΓ hb HB
      (ComputeJoin.of_compute RB).symm
    exact .compute RL RR H
  | eta hΓ ha hb H => exact proofErase_level_core_eta_head_forward hs hl hcon hc hΓ ha hb H RA RB
  | neutral hlen H ih =>
    obtain ⟨as, rfl, HA⟩ := RA.level_core_bvar_spine
    obtain ⟨bs, rfl, HB⟩ := RB.level_core_bvar_spine
    apply compare_spine (HF := .base .refl)
    apply pointwise_list (HA.length_eq.symm.trans (hlen.trans HB.length_eq))
    intro i hi hi'
    have hia := HA.length_eq.symm ▸ hi
    have hib := HB.length_eq.symm ▸ hi'
    exact ih i hia (HA.getElem_of i hia hi) (HB.getElem_of i hib hi')
  | lam _ _ ihA ihb =>
    obtain ⟨_, _, rfl, RA, Ra⟩ := RA.level_core_lam_inv
    obtain ⟨_, _, rfl, RB, Rb⟩ := RB.level_core_lam_inv
    exact .lam (ihA RA RB) (ihb Ra Rb)
  | lamCommon _ ih =>
    obtain ⟨_, _, rfl, _, Ra⟩ := RA.level_core_lam_inv
    obtain ⟨_, _, rfl, _, Rb⟩ := RB.level_core_lam_inv
    exact .lamCommon (ih Ra Rb)
  | forallE _ _ ihA ihB =>
    obtain ⟨_, _, rfl, RA, Ra⟩ := RA.pi_parts (fun H => erased_level_core_no_pi H)
    obtain ⟨_, _, rfl, RB, Rb⟩ := RB.pi_parts (fun H => erased_level_core_no_pi H)
    exact .forallE (ihA RA RB) (ihB Ra Rb)
  | compute hΓ ha hb HA HB _ ih =>
    obtain ⟨left, RL, HL⟩ := hc hΓ ha RA HA
    obtain ⟨right, RR, HR⟩ := hc hΓ hb RB HB
    exact .compute RL RR (ih HL HR)
  | symm _ ih => exact (ih RB RA).symm

/-- Reference joins suffice to transport a recursive comparison even when
neither join can return to its original reference. Both references evolve to
their respective joining points before the recursive forward theorem applies. -/
theorem LevelRecursiveGuard.of_joins
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D mode a b)
    (HA : ComputeJoin (ErasedLevelCore D) outA a)
    (HB : ComputeJoin (ErasedLevelCore D) outB b) :
    RawCheckedCompare (ErasedLevelCore D) mode outA outB := by
  obtain ⟨left, RL, RA⟩ := HA
  obtain ⟨right, RR, RB⟩ := HB
  exact .compute RL RR (H.forward hs hl hcon hc RA RB)

end Lean4Lean.VEnv.Strengthening
