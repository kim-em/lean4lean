import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelRecursiveTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaStages

/-! # First-stage Eq residuals from recursive level-core guards

Independent core computation of every Eq argument retains an actual prefix
certificate at stage one. Only the endpoint guard needs recursive transport;
all other arguments may compute freely, including universe conversions. This
is a local argument/prefix square, not confluence of the higher-stage system.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

private theorem level_lift {a b : ProofShape} (H : ErasedLevelCore D a b) :
    ErasedLevelCore D (a.liftN n k) (b.liftN n k) := by
  rcases H with H | H
  · exact .inl (erased_iota_primitive_liftN H)
  · cases H with
    | sort H hw => exact .inr (.sort H hw)
    | const H hw => exact .inr (.const H hw)

/-- A raw level-core check supplies the existing first-stage Eq-prefix guard
in any ambient checking context. No new primitive or semantic oracle is added. -/
theorem ProofShape.RawCheckedCompare.first_stage_prefix
    (H : RawCheckedCompare (ErasedLevelCore D) true a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w α a M m b)
      (.lam (ProofShape.eqProofType w α a b) (m.liftN 1)) :=
  .base (.inr (.inr (.inl (.intro (.carrierChecked
    ((H.scoped (fun H => .base (.inl H))).joint.computed))))))

/-- Applying the prefix to any proof-major shape computes to its minor. The
major need not be a constructor, and its erased shape need not be inspected. -/
theorem ProofShape.RawCheckedCompare.first_stage_full
    (H : RawCheckedCompare (ErasedLevelCore D) true a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (.app (ProofShape.eqRecBeforeMajor v w α a M m b) p) m := by
  apply ScopedCompute.trans (.app H.first_stage_prefix .refl)
  exact .beta (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using
    (ProofShape.BetaRed.beta (A := ProofShape.eqProofType w α a b)
      (b := m.liftN 1) (a := p)))

/-- Contracting an Eq prefix and independently computing all five arguments
form a literal stage-one square whenever the endpoint guard is recursive.
The residual guard is constructed; it is not an additional assumption. -/
theorem LevelRecursiveGuard.first_stage_prefix_square
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D true a b)
    (Rα : ProofShape.Compute (ErasedLevelCore D) α α')
    (Ra : ProofShape.Compute (ErasedLevelCore D) a a')
    (RM : ProofShape.Compute (ErasedLevelCore D) M M')
    (Rm : ProofShape.Compute (ErasedLevelCore D) m m')
    (Rb : ProofShape.Compute (ErasedLevelCore D) b b') :
    let S := ErasedStaticStructureEtaExpansionStage D 1
    let source := ProofShape.eqRecBeforeMajor v w α a M m b
    let initial := ProofShape.lam (ProofShape.eqProofType w α a b) (m.liftN 1)
    let computed := ProofShape.eqRecBeforeMajor v w α' a' M' m' b'
    let target := ProofShape.lam (ProofShape.eqProofType w α' a' b') (m'.liftN 1)
    ScopedCompute S Δ source initial ∧ ScopedCompute S Δ source computed ∧
      ScopedCompute S Δ initial target ∧ ScopedCompute S Δ computed target := by
  dsimp only
  have embed {Δ x y} (R : ProofShape.Compute (ErasedLevelCore D) x y) :
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ x y :=
    R.scoped (fun H => .base (.inl (.inl H)))
  have RC : ProofShape.Compute (ErasedLevelCore D)
      (ProofShape.eqRecBeforeMajor v w α a M m b)
      (ProofShape.eqRecBeforeMajor v w α' a' M' m' b') :=
    .app (.app (.app (.app (.app .refl Rα) Ra) RM) Rm) Rb
  have RD : ProofShape.Compute (ErasedLevelCore D)
      (ProofShape.eqProofType w α a b) (ProofShape.eqProofType w α' a' b') :=
    .app (.app (.app .refl Rα) Ra) Rb
  exact ⟨(H.forward hs hl hcon hc .refl .refl).first_stage_prefix,
    embed RC, .lam (embed RD) (embed (Rm.liftN (fun H => level_lift H))),
    (H.forward hs hl hcon hc Ra Rb).first_stage_prefix⟩

/-- The saturated prefix/argument square joins at the computed minor. All six
arguments may take arbitrary finite level-core paths; no path normalization,
return to the original arguments, or higher-stage confluence is required. -/
theorem LevelRecursiveGuard.first_stage_full_square
    (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : LevelRecursiveGuard D true a b)
    (Rα : ProofShape.Compute (ErasedLevelCore D) α α')
    (Ra : ProofShape.Compute (ErasedLevelCore D) a a')
    (RM : ProofShape.Compute (ErasedLevelCore D) M M')
    (Rm : ProofShape.Compute (ErasedLevelCore D) m m')
    (Rb : ProofShape.Compute (ErasedLevelCore D) b b')
    (Rp : ProofShape.Compute (ErasedLevelCore D) p p') :
    let S := ErasedStaticStructureEtaExpansionStage D 1
    let source := ProofShape.app (ProofShape.eqRecBeforeMajor v w α a M m b) p
    let computed := ProofShape.app (ProofShape.eqRecBeforeMajor v w α' a' M' m' b') p'
    ScopedCompute S Δ source m ∧ ScopedCompute S Δ source computed ∧
      ScopedCompute S Δ m m' ∧ ScopedCompute S Δ computed m' := by
  dsimp only
  have RC : ProofShape.Compute (ErasedLevelCore D)
      (.app (ProofShape.eqRecBeforeMajor v w α a M m b) p)
      (.app (ProofShape.eqRecBeforeMajor v w α' a' M' m' b') p') :=
    .app (.app (.app (.app (.app (.app .refl Rα) Ra) RM) Rm) Rb) Rp
  exact ⟨(H.forward hs hl hcon hc .refl .refl).first_stage_full,
    RC.scoped (fun H => .base (.inl (.inl H))),
    Rm.scoped (fun H => .base (.inl (.inl H))),
    (H.forward hs hl hcon hc Ra Rb).first_stage_full⟩

end Lean4Lean.VEnv.Strengthening
