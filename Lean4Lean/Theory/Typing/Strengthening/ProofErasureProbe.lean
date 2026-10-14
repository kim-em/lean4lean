import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedK

/-! # Domain extraction from constant-body erased lambda probes

Core and guarded K primitives have constant, application or projection sources.
They preserve a lambda with a constant sort body through compatible computation.
Comparing two such probes therefore supplies an inferred comparison of their
domains, even when the probe comparison was requested only in common mode.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape

/-- Primitive computational roots exclude binders, sorts and variables. -/
def ComputationalRoot : ProofShape → Prop
  | .const .. | .app .. | .proj .. => True
  | _ => False

private theorem BetaRed.sort_inv (R : BetaRed e out) (E : e = .sort u) : out = .sort u := by
  induction R with
  | refl => exact E
  | trans _ _ ih1 ih2 => exact ih2 (ih1 E)
  | app | proj | lam | forallE | beta => cases E

private theorem BetaRed.probe_inv (R : BetaRed (.lam A (.sort u)) out) :
    ∃ B, out = .lam B (.sort u) ∧ BetaRed A B := by
  generalize E : ProofShape.lam A (.sort u) = e at R
  induction R generalizing A with
  | refl => exact ⟨_, E.symm, .refl⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨B, rfl, H1⟩ := ih1 E
    obtain ⟨C, EC, H2⟩ := ih2 rfl
    exact ⟨C, EC, H1.trans H2⟩
  | lam RA Rb =>
    cases E
    obtain rfl := Rb.sort_inv rfl
    exact ⟨_, rfl, RA⟩
  | app | proj | forallE | beta => cases E

/-- Computational primitives cannot change a standalone sort. -/
theorem Compute.sort_inv (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (R : Compute Step e out) (E : e = .sort u) : out = .sort u := by
  induction R with
  | base H => exact (E ▸ hroot H).elim
  | beta H => exact H.sort_inv E
  | trans _ _ ih1 ih2 => exact ih2 (ih1 E)
  | app | proj | lam | forallE => cases E

/-- A constant-sort lambda body persists through arbitrary finite computation;
only its displayed domain computes. -/
theorem Compute.probe_inv (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (R : Compute Step (.lam A (.sort u)) out) :
    ∃ B, out = .lam B (.sort u) ∧ Compute Step A B := by
  generalize E : ProofShape.lam A (.sort u) = e at R
  induction R generalizing A with
  | base H => exact (E ▸ hroot H).elim
  | beta H =>
    cases E
    obtain ⟨B, EB, HB⟩ := H.probe_inv
    exact ⟨B, EB, .beta HB⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨B, rfl, H1⟩ := ih1 E
    obtain ⟨C, EC, H2⟩ := ih2 rfl
    exact ⟨C, EC, H1.trans H2⟩
  | lam RA Rb =>
    cases E
    obtain rfl := Rb.sort_inv hroot rfl
    exact ⟨_, rfl, RA⟩
  | app | proj | forallE => cases E

private theorem mkApps_const_ne_lam : mkApps (.const c ls) args ≠ .lam A b := by
  induction args using List.snoc_induction with
  | nil => simp [mkApps]
  | snoc args a ih => simp [mkApps_snoc]

variable [Params]

private theorem StructureEtaHead.not_lam (H : StructureEtaHead (.lam A b) m) : False := by
  generalize E : ProofShape.lam A b = e at H
  cases H with
  | intro => exact mkApps_const_ne_lam E.symm

private theorem EtaHead.not_probe (H : EtaHead (.lam A (.sort u)) m) : False := by
  obtain ⟨_, _, HE, _⟩ := H.shape
  cases HE

/-- Extract the domain certificate from comparison of constant-body probes.
Head eta is impossible for these bodies, so this conclusion is inferred-mode
even if the enclosing comparison was common-mode. -/
theorem Compare.probe_inv (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : Compare Step mode (.lam A (.sort u)) (.lam B (.sort v))) :
    Compare Step false A B := by
  generalize Ea : ProofShape.lam A (.sort u) = a at H
  generalize Eb : ProofShape.lam B (.sort v) = b at H
  induction H generalizing A B with
  | refl => cases Ea.trans Eb.symm; exact .refl
  | lam HA HB => cases Ea; cases Eb; exact HA
  | etaL H => cases Ea; exact H.not_probe.elim
  | etaR H => cases Eb; exact H.not_probe.elim
  | structL H => cases Ea; exact H.not_lam.elim
  | structR H => cases Eb; exact H.not_lam.elim
  | etaLams HD H => cases Ea; cases Eb; exact HD
  | compute Ra Rb HC ih =>
    cases Ea; cases Eb
    obtain ⟨A', EA, HA⟩ := Ra.probe_inv hroot
    obtain ⟨B', EB, HB⟩ := Rb.probe_inv hroot
    exact .compute HA HB (ih EA.symm EB.symm)
  | sort | const | app | proj | forallE => cases Ea

private theorem Matches.computationalRoot (H : Matches p e ls captures) : ComputationalRoot e := by
  cases H <;> trivial

end ProofShape
variable [Params]

/-- Every core or recursively guarded K primitive has a computational root.
The result is independent of declaration soundness and of guard completeness. -/
theorem erased_compared_K_stage_root : ∀ stage {a b}, ErasedComparedKStage D stage a b →
    ProofShape.ComputationalRoot a := by
  intro stage
  induction stage with
  | zero =>
    intro a b H
    rcases H with (H | H) | H
    · cases H <;> trivial
    · cases H with
      | select _ _ hm => exact hm.computationalRoot
      | apply _ _ hm => exact hm.computationalRoot
    · cases H with
      | intro _ _ _ hm => exact hm.computationalRoot
  | succ stage ih =>
    intro a b H
    rcases H with H | H
    · exact ih H
    · cases H; trivial

end Lean4Lean.VEnv.Strengthening
