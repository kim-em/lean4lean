import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFamilyCast

/-! # Retaining the primitive heads used by recursive cast certificates

Ordinary core steps and guarded Eq prefixes have constant, projection or sort
heads. The ambient stage also permits other expansions, but those are not
needed by these certificate interpretations. Guard subderivations still use
the complete ambient stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- The outer computation skeleton has only primitive or sort heads. This
restricts actual primitive uses, not the language of the guards inside them. -/
def PiInertStage (D : Definitions) (n : Nat) (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ErasedStaticStructureEtaExpansionStage D n Δ a b ∧
    (PrimitiveHead a ∨ ∃ u, a = .sort u)

/-- The retained computation skeleton embeds at its original finite stage. -/
theorem pi_inert_stage_embed (H : PiInertStage D n Δ a b) :
    ErasedStaticStructureEtaExpansionStage D n Δ a b := H.1

/-- Increasing the guard bound preserves the retained outer head. -/
theorem pi_inert_stage_mono (hle : n ≤ m) (H : PiInertStage D n Δ a b) : PiInertStage D m Δ a b :=
  ⟨erased_static_structure_eta_expansion_stage_mono hle H.1, H.2⟩

omit [Params] in
/-- Substitution preserves a constant or projection head, regardless of the
substituted arguments. This is only a head fact, not primitive closure. -/
theorem ProofShape.PrimitiveHead.subst (H : PrimitiveHead a) : PrimitiveHead (a.subst τ) := by
  induction a with
  | const | proj => trivial
  | app _ _ ih _ => exact ih H
  | proof | bvar | sort | lam | forallE => exact H.elim

/-- Exact interpreted renaming preserves both the original stage guard and
the extra head evidence. No new native recovery certificate is synthesized. -/
theorem pi_inert_stage_rename (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (n : Nat) (H : PiInertStage D n Δ a b) (W : ContextRenaming Δ Δ' τ) :
    PiInertStage D n Δ' (a.subst τ) (b.subst τ) := by
  refine ⟨erased_static_structure_eta_expansion_stage_rename heq hs n H.1 W, ?_⟩
  rcases H.2 with H | ⟨u, rfl⟩
  · exact .inl H.subst
  · exact .inr ⟨u, rfl⟩

/-- In particular, none of these primitives rewrites a literal Pi root. -/
theorem pi_inert_stage_no_pi (H : PiInertStage D n Δ (.forallE A B) out) : False := by
  rcases H.2 with H | ⟨u, H⟩
  · exact H
  · cases H

/-- Every ordinary level-core primitive belongs to the restricted skeleton
at every stage, including sort universe conversions. -/
theorem pi_inert_stage_core (H : ErasedLevelCore D a b) : PiInertStage D n Δ a b := by
  refine ⟨erased_static_structure_eta_expansion_stage_mono (Nat.zero_le n) (.inl H), ?_⟩
  rcases H with H | H
  · exact .inl (erased_iota_primitive_head H)
  · cases H with
    | sort => exact .inr ⟨_, rfl⟩
    | const => exact .inl trivial

/-- Compatible ordinary core paths use only the retained primitives. -/
theorem ProofShape.Compute.in_pi_inert_stage (R : Compute (ErasedLevelCore D) a b) :
    ScopedCompute (PiInertStage D n) Δ a b := R.scoped (fun H => .base (pi_inert_stage_core H))

/-- A full earlier-stage comparison licenses the same Eq-prefix repair in
the restricted next-stage skeleton. Its root is constant-headed. -/
theorem ProofShape.ComputedJointCompare.next_pi_inert_stage
    (H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a b) :
    ScopedCompute (PiInertStage D (n+1)) Δ
      (.app (ProofShape.eqRecBeforeMajor v w α a M m b) p) m := by
  have RP : ScopedCompute (PiInertStage D (n+1)) Δ (ProofShape.eqRecBeforeMajor v w α a M m b)
      (.lam (ProofShape.eqProofType w α a b) (m.liftN 1)) :=
    .base ⟨.inr (.inr (.inl (.intro (.carrierChecked H)))), .inl trivial⟩
  apply ScopedCompute.trans (.app RP .refl)
  exact .beta (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ProofShape.BetaRed.beta (A := ProofShape.eqProofType w α a b)
      (b := m.liftN 1) (a := p)))

end Lean4Lean.VEnv.Strengthening
