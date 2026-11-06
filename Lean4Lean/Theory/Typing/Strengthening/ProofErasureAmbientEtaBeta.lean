import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAmbientVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetainedEtaReflection

/-! # Arbitrary protected eta functions through consumer beta reduction

An eta origin may contain any ambient function, including a lambda or a term
which computes to one. Crossing its opened beta boundary creates an annotation
mark recording the exposed domain. This module treats retained fresh arguments;
typed proof-argument simulation and full core primitives remain separate work.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private liftN_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable {Guard EtaGuard : ProofShape → ProofShape → Prop}

/-- Eta syntax with a retained fresh argument. -/
def retainedEta (A f : ProofShape) : ProofShape := .lam A (.app (f.liftN 1) (.bvar 0))

/-- A protected eta origin records its domain and unrestricted short function. -/
inductive RetainedEtaAtom (EtaGuard : ProofShape → ProofShape → Prop) : ProofShape → ProofShape → Prop where
  | etaL : EtaGuard A f → RetainedEtaAtom EtaGuard (retainedEta A f) f
  | etaR : EtaGuard A f → RetainedEtaAtom EtaGuard f (retainedEta A f)

/-- Both orientations retain the identical ambient certificate. -/
theorem RetainedEtaAtom.symm (H : RetainedEtaAtom EtaGuard a b) : RetainedEtaAtom EtaGuard b a := by
  cases H with
  | etaL H => exact .etaR H
  | etaR H => exact .etaL H

private theorem beta_app_cases (R : BetaRed (.app f x) out) :
    ∃ f' x', BetaRed f f' ∧ BetaRed x x' ∧
      (out = .app f' x' ∨ ∃ A b, f' = .lam A b ∧ BetaRed (b.inst x') out) := by
  generalize E : ProofShape.app f x = source at R
  induction R generalizing f x with
  | refl => exact ⟨_, _, .refl, .refl, .inl E.symm⟩
  | trans _ R₂ ih₁ ih₂ =>
    obtain ⟨f₁, x₁, RF, RX, H⟩ := ih₁ E
    rcases H with rfl | ⟨A, b, rfl, RB⟩
    · obtain ⟨f₂, x₂, RF₂, RX₂, H₂⟩ := ih₂ rfl
      exact ⟨_, _, RF.trans RF₂, RX.trans RX₂, H₂⟩
    · exact ⟨_, _, RF, RX, .inr ⟨A, b, rfl, RB.trans R₂⟩⟩
  | app RF RX => cases E; exact ⟨_, _, RF, RX, .inl rfl⟩
  | beta => cases E; exact ⟨_, _, .refl, .refl, .inr ⟨_, _, rfl, .refl⟩⟩
  | lam | forallE | proj => cases E

/-- Raw beta at a retained fresh argument reflects into the original function.
The crossed-boundary branch retains the exact exposed lambda and computed body. -/
theorem BetaRed.retained_fresh_application (R : BetaRed (.app (f.liftN 1) (.bvar 0)) out) :
    ∃ g, BetaRed f g ∧ (out = .app (g.liftN 1) (.bvar 0) ∨ ∃ C, g = .lam C out) := by
  obtain ⟨f', x', RF, RX, H⟩ := beta_app_cases R
  have EX : x' = .bvar 0 := RX.fixed_of_normal (Step := fun _ _ => False)
    ⟨fun _ H => H, trivial⟩
  subst x'
  obtain ⟨g, RG, EF⟩ := RF.liftN_inv
  rcases H with rfl | ⟨A, b, E, RB⟩
  · exact ⟨g, RG, .inl (by rw [EF])⟩
  · obtain ⟨C, c, rfl, _, EB⟩ := liftN_lam_inv (EF.symm.trans E)
    rw [← EB, lift_eta_inst_bvar] at RB
    exact ⟨_, RG.trans (.lam .refl RB), .inr ⟨C, rfl⟩⟩

/-- Applying a retained eta body substitutes the supplied argument exactly. -/
theorem retained_eta_body_inst :
    (ProofShape.app (f.liftN 1) (.bvar 0)).inst x = .app f x := by
  simp only [inst_eq_subst, Subst.liftN, subst, Subst.one, lift_subst_cons, subst_id, Subst.cons]

/-- Retained eta of a raw lambda contracts to the same body at the eta domain. -/
theorem retained_eta_lambda_beta : BetaRed (retainedEta A (.lam C b)) (.lam A b) := by
  apply BetaRed.lam .refl
  simpa only [retainedEta, liftN, lift_eta_inst_bvar] using
    (BetaRed.beta (A := C.liftN 1) (b := b.liftN 1 1) (a := .bvar 0))

/-- An arbitrary eta origin simulates every beta path. If its opened body
crosses beta, the updated origin supplies a guard for the exposed annotation. -/
theorem retained_eta_origin_beta
    (heta : ∀ {A f A' g}, EtaGuard A f → BetaRed A A' → BetaRed f g → EtaGuard A' g)
    (hlam : ∀ {A C b}, EtaGuard A (.lam C b) → Guard A C)
    (H : LiftedOrigin (RetainedEtaAtom EtaGuard) n a b) (R : BetaRed a a') :
    ∃ b', BetaRed b b' ∧ AmbientVariant Guard (RetainedEtaAtom EtaGuard) n a' b' := by
  obtain ⟨x, y, H, rfl, rfl⟩ := H
  obtain ⟨out, R0, rfl⟩ := R.liftN_inv
  cases H with
  | @etaL A f HG =>
    obtain ⟨A', body, rfl, RA, RB⟩ := R0.lam_inv
    obtain ⟨g, RF, HR⟩ := RB.retained_fresh_application
    have HG' := heta HG RA RF
    refine ⟨g.liftN n, RF.liftN, ?_⟩
    rcases HR with rfl | ⟨C, rfl⟩
    · exact .origin ⟨retainedEta A' g, g, .etaL HG', rfl, rfl⟩
    · exact .marked (hlam HG') .refl
  | @etaR A f HG =>
    refine ⟨(retainedEta A out).liftN n, ?_, ?_⟩
    · exact (BetaRed.lam .refl (.app R0.liftN .refl)).liftN
    · exact .origin ⟨out, retainedEta A out, .etaR (heta HG .refl R0), rfl, rfl⟩

/-- Applying a protected eta origin whose left endpoint is a lambda preserves
paired arguments. This includes short functions which are themselves lambdas;
no assumption that the protected function stays neutral is used. -/
theorem retained_eta_origin_apply
    (H : LiftedOrigin (RetainedEtaAtom EtaGuard) n (.lam A body) g)
    (VX : AmbientVariant Guard (RetainedEtaAtom EtaGuard) n x y) :
    ∃ out, BetaRed (.app g y) out ∧
      AmbientVariant Guard (RetainedEtaAtom EtaGuard) n (body.inst x) out := by
  obtain ⟨a, b, H, EA, rfl⟩ := H
  cases H with
  | @etaL C _ HG =>
    change ProofShape.lam A body = ProofShape.lam (C.liftN n) (.app ((b.liftN 1).liftN n 1) (.bvar 0)) at EA
    obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj EA
    rw [← liftN_comm b n 1 0 0 (Nat.zero_le _)]
    rw [retained_eta_body_inst]
    exact ⟨_, .refl, .app .refl VX⟩
  | @etaR C f HG =>
    obtain ⟨D, b, rfl, rfl, rfl⟩ := liftN_lam_inv EA.symm
    refine ⟨(b.liftN n 1).inst y, ?_, AmbientVariant.refl.inst_pair VX⟩
    exact (BetaRed.app retained_eta_lambda_beta.liftN .refl).trans .beta

/-- Beta simulation of arbitrary protected eta functions and emerging domain
marks. The only guard premises concern their retained ambient histories. -/
theorem ambient_eta_beta_left
    (hg : ∀ {A C A'}, Guard A C → BetaRed A A' → Guard A' C)
    (heta : ∀ {A f A' g}, EtaGuard A f → BetaRed A A' → BetaRed f g → EtaGuard A' g)
    (hlam : ∀ {A C b}, EtaGuard A (.lam C b) → Guard A C)
    (R : BetaRed a a') (V : AmbientVariant Guard (RetainedEtaAtom EtaGuard) n a b) :
    ∃ b', BetaRed b b' ∧ AmbientVariant Guard (RetainedEtaAtom EtaGuard) n a' b' :=
  AmbientVariant.beta_left (Guard := Guard) (Atom := RetainedEtaAtom EtaGuard)
    (fun H R => hg H R) (fun H R => retained_eta_origin_beta (fun H RA RF => heta H RA RF)
      (fun H => hlam H) H R) (fun H V => retained_eta_origin_apply H V) R V

/-- Independent beta paths of arbitrary protected eta consumers have further
paired residuals, retaining every exposed lambda-domain obligation. -/
theorem ambient_eta_beta_residuals
    (hs : ∀ {A C}, Guard A C → Guard C A)
    (hg : ∀ {A C A'}, Guard A C → BetaRed A A' → Guard A' C)
    (heta : ∀ {A f A' g}, EtaGuard A f → BetaRed A A' → BetaRed f g → EtaGuard A' g)
    (hlam : ∀ {A C b}, EtaGuard A (.lam C b) → Guard A C)
    (V : AmbientVariant Guard (RetainedEtaAtom EtaGuard) n a b)
    (RA : BetaRed a p) (RB : BetaRed b q) :
    ∃ p' q', BetaRed p p' ∧ BetaRed q q' ∧ AmbientVariant Guard (RetainedEtaAtom EtaGuard) n p' q' :=
  AmbientVariant.beta_residuals (Guard := Guard) (Atom := RetainedEtaAtom EtaGuard)
    (fun H => hs H) (fun H => H.symm) (fun H R => hg H R)
    (fun H R => retained_eta_origin_beta (fun H RA RF => heta H RA RF) (fun H => hlam H) H R)
    (fun H V => retained_eta_origin_apply H V) V RA RB

end Lean4Lean.VEnv.Strengthening.ProofShape
