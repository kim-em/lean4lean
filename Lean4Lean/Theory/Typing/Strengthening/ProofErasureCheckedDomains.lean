import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCheckedTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredLambdaDomains

/-! # Inferred lambda domains remain visible under checking

Checking a lambda at a common type can omit a domain certificate. Inferring an
equality between two lambdas still exposes that certificate: a switch from
checking to inference must compare their recovered Pi types first.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

private theorem mkApps_const_ne_forallE : mkApps (.const c ls) args ≠ .forallE A B := by
  induction args using List.snoc_induction with
  | nil => simp [mkApps]
  | snoc args a ih => simp [mkApps_snoc]

variable [Params]
private theorem StructureEtaHead.not_forallE (H : StructureEtaHead (.forallE A B) m) : False := by
  generalize E : ProofShape.forallE A B = e at H
  cases H with
  | intro => exact mkApps_const_ne_forallE E.symm

/-- Pi comparison always compares its displayed domains, in either mode. -/
theorem Compare.forallE_domains (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : Compare Step mode (.forallE A C) (.forallE B D)) : Compare Step false A B := by
  generalize Ea : ProofShape.forallE A C = a at H
  generalize Eb : ProofShape.forallE B D = b at H
  induction H generalizing A B C D with
  | refl => cases Ea.trans Eb.symm; exact .refl
  | forallE HA _ => cases Ea; cases Eb; exact HA
  | etaL H => cases Ea; obtain ⟨_, _, E, _⟩ := H.shape; cases E
  | etaR H => cases Eb; obtain ⟨_, _, E, _⟩ := H.shape; cases E
  | structL H => cases Ea; exact H.not_forallE.elim
  | structR H => cases Eb; exact H.not_forallE.elim
  | compute Ra Rb _ ih =>
    cases Ea; cases Eb
    obtain ⟨_, _, EA, HA⟩ := Ra.forallE_shape hroot
    obtain ⟨_, _, EB, HB⟩ := Rb.forallE_shape hroot
    exact .compute HA HB (ih EA.symm EB.symm)
  | sort | const | app | proj | lam | etaLams => cases Ea

/-- Recovered eta does not change domain reflection for Pi endpoints. -/
theorem RecoveredCompare.forallE_domains (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : RecoveredCompare Step σ τ mode (.forallE A C) (.forallE B D)) :
    RecoveredCompare Step σ τ false A B := by
  generalize Ea : ProofShape.forallE A C = a at H
  generalize Eb : ProofShape.forallE B D = b at H
  induction H generalizing A B C D with
  | base H => cases Ea; cases Eb; exact .base (H.forallE_domains hroot)
  | forallE HA _ => cases Ea; cases Eb; exact HA
  | etaR => cases Eb
  | compute Ra Rb _ ih =>
    cases Ea; cases Eb
    obtain ⟨_, _, EA, HA⟩ := Ra.forallE_shape hroot
    obtain ⟨_, _, EB, HB⟩ := Rb.forallE_shape hroot
    exact .compute HA HB (ih EA.symm EB.symm)
  | app | proj | lam | etaL => cases Ea

/-- Checking-mode lambda relaxation leaves Pi domain reflection intact. A
recovered-type mode switch uses the common certificate's Pi comparison. -/
theorem CheckedCompare.forallE_domains (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : CheckedCompare Step σ τ mode (.forallE A C) (.forallE B D)) :
    CheckedCompare Step σ τ false A B := by
  generalize Ea : ProofShape.forallE A C = a at H
  generalize Eb : ProofShape.forallE B D = b at H
  induction H generalizing A B C D with
  | base H => cases Ea; cases Eb; exact .base (H.forallE_domains hroot)
  | forallE HA _ => cases Ea; cases Eb; exact HA
  | etaR => cases Eb
  | recover _ _ _ _ _ ihC => exact ihC Ea Eb
  | compute Ra Rb _ ih =>
    cases Ea; cases Eb
    obtain ⟨_, _, EA, HA⟩ := Ra.forallE_shape hroot
    obtain ⟨_, _, EB, HB⟩ := Rb.forallE_shape hroot
    exact .compute HA HB (ih EA.symm EB.symm)
  | app | proj | lam | etaL | lamCommon => cases Ea

/-- Inferred comparison still reflects lambda domains. Common-mode comparison
alone cannot be promoted without recovered type alignment. -/
theorem CheckedCompare.lam_domains (hroot : ∀ {a b}, Step a b → ComputationalRoot a)
    (H : CheckedCompare Step σ τ false (.lam A a) (.lam B b)) :
    CheckedCompare Step σ τ false A B := by
  generalize Ea : ProofShape.lam A a = x at H
  generalize Eb : ProofShape.lam B b = y at H
  generalize Em : false = mode at H
  induction H generalizing A B a b with
  | base H => cases Ea; cases Eb; cases Em; exact .base (H.lam_domains hroot)
  | lam HA _ => cases Em; cases Ea; cases Eb; exact HA
  | etaL HR HD _ =>
    cases Em; cases Ea; cases Eb
    obtain ⟨_, _, E, RD⟩ := HR.lam_shape hroot
    cases E
    exact .compute .refl RD HD
  | etaR HR HD _ =>
    cases Em; cases Ea; cases Eb
    obtain ⟨_, _, E, RD⟩ := HR.lam_shape hroot
    cases E
    exact .compute RD .refl HD
  | lamCommon => cases Em
  | recover RA RB HT HC =>
    cases Em; cases Ea; cases Eb
    obtain ⟨_, _, rfl, RA'⟩ := RA.lam_shape hroot
    obtain ⟨_, _, rfl, RB'⟩ := RB.lam_shape hroot
    exact .compute RA' RB' (HT.forallE_domains hroot)
  | compute Ra Rb _ ih =>
    cases Ea; cases Eb
    obtain ⟨_, _, EA, HA⟩ := Ra.lam_shape hroot
    obtain ⟨_, _, EB, HB⟩ := Rb.lam_shape hroot
    exact .compute HA HB (ih EA.symm EB.symm Em)
  | app | proj | forallE => cases Ea

end Lean4Lean.VEnv.Strengthening.ProofShape
