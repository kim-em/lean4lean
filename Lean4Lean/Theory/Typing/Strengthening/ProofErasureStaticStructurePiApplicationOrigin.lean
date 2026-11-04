import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureDependentReturn

/-! # A neutral family retains the computation history of its Pi argument

The argument and result carry different finite demands. Pi payloads keep their
original component histories; the neutral family transports those payloads to
the result. Neither component is required to return to its original syntax.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape.PiApplicationObservation
open _root_.Lean4Lean
open PureObservation (Ob)
open PiOriginObservation (FixedTail)

/-- One demand reads the argument Pi; the other reads the fixed family
applied to that Pi. Both retain the same lower payload predicate. -/
def Realizes (P : ProofShape → ProofShape → Prop) (head : ProofShape) (n : Nat)
    (e : ProofShape) : Ob → Prop
  | .pi => ∃ A B, P A B ∧ BetaRed e ((ProofShape.forallE A B).liftN n)
  | .sort => ∃ A B, P A B ∧ BetaRed e ((ProofShape.app head (.forallE A B)).liftN n)
  | .app keys o => ∀ a, (∀ key ∈ keys, Realizes P head n a key) → Realizes P head n (.app e a) o
termination_by o => sizeOf o

/-- Beta predecessors retain the same lower argument history. -/
theorem Realizes.beta_back (R : BetaRed e e') (H : Realizes P head n e' o) :
    Realizes P head n e o := by
  cases o with
  | pi | sort =>
    simp only [Realizes] at H ⊢
    obtain ⟨A, B, HP, H⟩ := H
    exact ⟨A, B, HP, R.trans H⟩
  | app keys o =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.beta_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- The marked-Pi observation supports a second result demand while
substitutions fix its original payload context. -/
theorem realizes (H : PiOriginObservation.Obs P n S e o) (HT : FixedTail n m σ)
    (hσ : ∀ i key, S i key → Realizes P head m (σ i) key) :
    Realizes P head m (e.subst σ) o := by
  induction H generalizing m σ with
  | var h => exact hσ _ _ h
  | payload h => rw [HT.payload]; simp only [Realizes]; exact ⟨_, _, h, .refl⟩
  | app _ _ ihf iha =>
    have HF := ihf HT hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => iha key hk HT hσ)
  | @lam n keys S b o A _ ih =>
    simp only [Realizes]
    intro a ha
    have HB := ih HT.cons (fun i key hi => by
      cases i with
      | zero => exact ha key hi
      | succ i => exact hσ i key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [inst_eq_subst, Subst.liftN, subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i => simp only [Subst.comp, Subst.lift, Subst.one, Subst.cons, lift_subst_cons, subst_id]
    exact Realizes.beta_back (E ▸ (BetaRed.beta (A := A.subst σ))) HB

end Lean4Lean.VEnv.Strengthening.ProofShape.PiApplicationObservation

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Every computation of F (Pi A B) beta-reads as F (Pi X Y), retaining
actual representatives and computation histories for X and Y in their original
contexts. A and B are arbitrary typed components, including data-indexed types.
This is an argument-origin theorem, not an exact return or confluence claim. -/
theorem static_structure_neutral_pi_application_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hf : env.HasType univs Γ (.bvar f) (.forallE (.sort (.imax u v)) (.sort w)))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) out) :
    ∃ X Y, StaticStructurePiOrigin D Γ A B u v X Y ∧
      ProofShape.BetaRed out (.app (.bvar f) (.forallE X Y)) := by
  have hPi := HasType.forallE hA hB
  have ht : env.HasType univs Γ (.app (.bvar f) (.forallE A B)) (.sort w) := hf.app hPi
  have EF : proofErase Γ (.bvar f) = .bvar f := if_neg (not_isProof_function_to_sort hΓ hf)
  have EP : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have EE : proofErase Γ (.app (.bvar f) (.forallE A B)) =
      .app (.bvar f) (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) := by
    rw [show proofErase Γ (.app (.bvar f) (.forallE A B)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ ht), EF, EP]
  have HF : ControlTyping (proofEraseCtx Γ) (.bvar f) (.arrow (.sort (.imax u v)) (.sort w)) :=
    ⟨Γ, _, hΓ, rfl, hf, EF⟩
  have HP : ControlTyping (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) (.sort (.imax u v)) :=
    ⟨Γ, _, hΓ, rfl, hPi, EP⟩
  have HT : ControlTyping (proofEraseCtx Γ)
      (.app (.bvar f) (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) (.sort w) :=
    ⟨Γ, _, hΓ, rfl, ht, EE⟩
  let S : ControlObservation.Sets := fun j t o =>
    j = f ∧ t = .arrow (.sort (.imax u v)) (.sort w) ∧ o = .app [.pi] .sort
  have HS : S.Typed (proofEraseCtx Γ) := by
    rintro j t o ⟨rfl, rfl, rfl⟩
    exact HF
  have H : ControlObservation.Obs (StaticStructurePiOrigin D Γ A B u v) 0 (proofEraseCtx Γ) S
      (.app (.bvar f) (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) (.sort w) .sort := by
    apply ControlObservation.Obs.app HT (keys := [.pi])
    · exact .var HF (.fn (by intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .payload)
        .neutral) ⟨rfl, rfl, rfl⟩
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      simpa only [ProofShape.liftN_zero] using
        (ControlObservation.Obs.payload (n := 0) (S := S)
          (by simpa only [ProofShape.liftN_zero] using HP) (StaticStructurePiOrigin.refl hA hB))
  have HO := proofErase_scoped_compute_controlObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_controlObservation heq hs)
    (static_structure_piOrigin_componentClosure heq hs hΓ)
    R hΓ (Ctx.LiftN.zero []) ht rfl EE HS H
  have HN := HO.forget (T := fun j key => j = f ∧ key = .app [.pi] .sort)
    (fun _ _ _ H => ⟨H.1, H.2.2⟩)
  have HR := PiApplicationObservation.realizes (head := .bvar f) HN
    (show PiOriginObservation.FixedTail 0 0 ProofShape.Subst.id from fun _ => rfl)
    (fun j key hj => by
      obtain ⟨rfl, rfl⟩ := hj
      simp only [PiApplicationObservation.Realizes, ProofShape.Subst.id, ProofShape.liftN_zero]
      intro a ha
      have HA := ha .pi (by simp)
      simp only [PiApplicationObservation.Realizes, ProofShape.liftN_zero] at HA
      obtain ⟨X, Y, HP, RB⟩ := HA
      exact ⟨X, Y, HP, .app .refl RB⟩)
  simpa only [ProofShape.subst_id, PiApplicationObservation.Realizes, ProofShape.liftN_zero] using HR

/-- Joining forks of the argument type suffices to join every fork of the
neutral family applied to it. The local argument-joining premise is explicit
and remains unproved for arbitrary Pi components. No native argument recovery
or whole-language confluence is required by this reduction. -/
theorem static_structure_neutral_pi_application_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hf : env.HasType univs Γ (.bvar f) (.forallE (.sort (.imax u v)) (.sort w)))
    (HJ : ∀ {left right},
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE A B)) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.forallE A B)) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) left)
    (RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) right) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared := by
  obtain ⟨XL, YL, ⟨_, _, _, _, _, _, RAL, RBL⟩, BL⟩ :=
    static_structure_neutral_pi_application_origin heq hs hΓ hA hB hf RL
  obtain ⟨XR, YR, ⟨_, _, _, _, _, _, RAR, RBR⟩, BR⟩ :=
    static_structure_neutral_pi_application_origin heq hs hΓ hA hB hf RR
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))
  have PL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (.forallE XL YL) := E ▸ ScopedCompute.forallE RAL RBL
  have PR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (.forallE XR YR) := E ▸ ScopedCompute.forallE RAR RBR
  obtain ⟨shared, JL, JR⟩ := HJ PL PR
  exact ⟨.app (.bvar f) shared,
    (ScopedCompute.beta BL).trans (.app .refl JL),
    (ScopedCompute.beta BR).trans (.app .refl JR)⟩

/-- If the Pi argument has variable/universe/Pi syntax, the local premise
above is discharged by its established return theorem. The neutral application
itself then returns exactly, despite not belonging to that initial syntax. -/
theorem static_structure_neutral_dependent_pi_application_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hf : env.HasType univs Γ (.bvar f) (.forallE (.sort (.imax u v)) (.sort w)))
    (HA : UniversePiSyntax A) (HB : UniversePiSyntax B)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.bvar f) (.forallE (proofErase Γ A) (proofErase (A :: Γ) B))) := by
  obtain ⟨X, Y, ⟨_, _, _, _, _, _, RA, RB⟩, Rβ⟩ :=
    static_structure_neutral_pi_application_origin heq hs hΓ hA hB hf R
  have E : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (.forallE X Y) := E ▸ ScopedCompute.forallE RA RB
  have RR := static_structure_dependent_return heq hs hΓ (HasType.forallE hA hB) (.forallE HA HB) RP
  rw [E] at RR
  exact (ScopedCompute.beta Rβ).trans (.app .refl RR)

end Lean4Lean.VEnv.Strengthening
