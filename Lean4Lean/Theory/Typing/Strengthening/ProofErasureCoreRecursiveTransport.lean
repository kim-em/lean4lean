import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRawEtaTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRigidRoots

/-! # Recursive certificates stable under ordinary computation

Typed joins and typed eta leaves can occur beneath rigid application spines and
lambda binders. The fragment has a checked two-sided residual theorem; it does
not assert coverage of arbitrary comparisons or reducible function positions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]
namespace ErasedCore
open ProofShape

/-- A concrete recursive fragment of comparison, with typed computational and
eta leaves. Rigid spines prevent computation from creating a beta overlap at
function position. Lambda checking permits independent annotation computation.
No forward-stability premise is included among the constructors. -/
inductive RecursiveGuard : Bool → ProofShape → ProofShape → Prop where
  | join (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (HA : Compute Step (proofErase Γ a) shared)
      (HB : Compute Step (proofErase Γ b) shared) :
      RecursiveGuard mode (proofErase Γ a) (proofErase Γ b)
  | eta (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a T)
      (hb : env.HasType univs Γ b T)
      (HA : Compute Step (proofErase Γ a) a')
      (HB : Compute Step (proofErase Γ b) b') (H : EtaHead a' b') :
      RecursiveGuard true (proofErase Γ a) (proofErase Γ b)
  | spine (hc : env.Rigid c) (hD : ∀ ls rhs, ¬ definitions.unfolds c ls rhs)
      (hlen : args.length = args'.length)
      (H : ∀ i (hi : i < args.length),
        RecursiveGuard true args[i] (args'[i]'(hlen ▸ hi))) :
      RecursiveGuard mode (ProofShape.mkApps (.const c ls) args)
        (ProofShape.mkApps (.const c ls) args')
  | lam : RecursiveGuard false A A' → RecursiveGuard mode b b' →
      RecursiveGuard mode (.lam A b) (.lam A' b')
  | lamCommon : RecursiveGuard true b b' →
      RecursiveGuard true (.lam A b) (.lam A' b')
  | compute (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (HA : Compute Step (proofErase Γ a) a')
      (HB : Compute Step (proofErase Γ b) b') (H : RecursiveGuard mode a' b') :
      RecursiveGuard mode (proofErase Γ a) (proofErase Γ b)
  | symm : RecursiveGuard mode a b → RecursiveGuard mode b a

private theorem forget_scope (H : ScopedCompute (fun _ => Step) Δ a b) :
    Compute Step a b := by
  induction H with
  | base H => exact .base H
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

private theorem rigid_spine (hc : env.Rigid c)
    (hD : ∀ ls rhs, ¬ definitions.unfolds c ls rhs)
    (R : Compute Step (ProofShape.mkApps (.const c ls) args) out) :
    ∃ args', out = ProofShape.mkApps (.const c ls) args' ∧
      List.Forall₂ (Compute Step) args args' := by
  have R' : ScopedCompute (fun _ => Step) [] _ _ := R.scoped (fun H => .base H)
  obtain ⟨args', E, H⟩ := R'.const_spine (fun H =>
    erased_iota_primitive_no_rigid hc hD H (ProofShape.constHead_mkApps _ _))
  exact ⟨args', E, H.imp (fun _ _ H => forget_scope H)⟩

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

/-- Arbitrary independent core computations preserve a recursive guard as a
raw checking certificate. In particular, eta leaves may occur at any depth
inside rigid indices and lambda bodies. No normalization is assumed. -/
theorem RecursiveGuard.forward
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : RecursiveGuard mode a b)
    (RA : Compute Step a a') (RB : Compute Step b b') :
    RawCheckedCompare Step mode a' b' := by
  induction H generalizing a' b' with
  | join hΓ ha hb HA HB => exact join_guard_forward hcon hΓ ha hb HA HB RA RB
  | eta hΓ ha hb HA HB H => exact head_eta_join_raw_forward hcon hΓ ha hb HA HB H RA RB
  | spine hc hD hlen H ih =>
    obtain ⟨as, rfl, HA⟩ := rigid_spine hc hD RA
    obtain ⟨bs, rfl, HB⟩ := rigid_spine hc hD RB
    apply compare_spine (HF := .base .refl)
    apply pointwise_list (HA.length_eq.symm.trans (hlen.trans HB.length_eq))
    intro i hi hi'
    have hia := HA.length_eq.symm ▸ hi
    have hib := HB.length_eq.symm ▸ hi'
    exact ih i hia (HA.getElem_of i hia hi) (HB.getElem_of i hib hi')
  | lam _ _ ihA ihb =>
    obtain ⟨_, _, rfl, RA, Ra⟩ := RA.lam_inv (fun H => root H)
    obtain ⟨_, _, rfl, RB, Rb⟩ := RB.lam_inv (fun H => root H)
    exact .lam (ihA RA RB) (ihb Ra Rb)
  | lamCommon _ ih =>
    obtain ⟨_, _, rfl, _, Ra⟩ := RA.lam_inv (fun H => root H)
    obtain ⟨_, _, rfl, _, Rb⟩ := RB.lam_inv (fun H => root H)
    exact .lamCommon (ih Ra Rb)
  | compute hΓ ha hb HA HB _ ih =>
    obtain ⟨left, RL, HL⟩ := confluent hcon hΓ ha RA HA
    obtain ⟨right, RR, HR⟩ := confluent hcon hΓ hb RB HB
    exact .compute RL RR (ih HL HR)
  | symm _ ih => exact (ih RB RA).symm

end ErasedCore
end Lean4Lean.VEnv.Strengthening
