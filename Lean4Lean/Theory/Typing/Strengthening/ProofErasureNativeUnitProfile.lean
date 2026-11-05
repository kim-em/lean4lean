import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidFunctionCanonical
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerCanonicalArgument

/-! # Dependent native profiles with a canonical unit-valued inhabitant

Finite profiles permit open, dependent positive domains and actual directed
computations of their codomains. Their canonical functions retain the selected
annotations. Ordinary equality alone does not construct a profile.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- A finite native normalization certificate. Pi annotations have actual
sort witnesses and may depend on ambient or preceding variables. Conversion
requires a directed computation, not merely an ordinary type equality. -/
inductive NativeUnitProfile (D : PureObservation.Definitions) (s uc : Name) :
    List ProofShape → ProofShape → ProofShape → Prop where
  | unit : NativeUnitProfile D s uc Δ (.const s []) (.const uc [])
  | pi : DomainSort Δ A u → ¬ u ≈ .zero →
      NativeUnitProfile D s uc (A :: Δ) B c →
      NativeUnitProfile D s uc Δ (.forallE A B) (.lam A c)
  | convert : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ T T' →
      NativeUnitProfile D s uc Δ T' c → NativeUnitProfile D s uc Δ T c

/-- Exact context renaming transports both the chosen annotations and every
computation used to expose a profile. No arbitrary substitution is asserted. -/
theorem NativeUnitProfile.rename
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : NativeUnitProfile D s uc Δ T c) (W : ContextRenaming Δ Δ' τ) :
    NativeUnitProfile D s uc Δ' (T.subst τ) (c.subst τ) := by
  induction H generalizing Δ' τ with
  | unit => exact .unit
  | pi SD hp _ ih => exact .pi (ContextSubstitution.sort W.interpretation SD) hp (ih W.cons)
  | convert R _ ih =>
    exact .convert (R.rename (RigidFunctionObservation.union_world_rename heq hs) W) (ih W)

/-- A native certificate normalizes according to its finite profile. The
recursive call is on the native application to a fresh variable; it never
requires native recovery to survive a computation of the original function. -/
theorem NativeUnitProfile.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (H : NativeUnitProfile D s info.ctorName Δ T c)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ e T) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ e c := by
  induction H generalizing e with
  | unit => exact unit_native_compute hi hp hx hz RN
  | convert R _ ih => exact ih (.convert RN R)
  | @pi Δ A u B c SD hpos H ih =>
    have RE : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ e
        (.lam A (.app (e.liftN 1) (.bvar 0))) := by
      simpa only [etaArgument, if_neg hpos] using
        (ScopedCompute.base (erased_static_structure_eta_expansion_union_eta (.intro RN SD)))
    obtain ⟨Γ, A₀, hΓ, EΓ, hA, EA⟩ := SD
    have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    have W : ContextRenaming Δ (A :: Δ) (fun i => .bvar (liftVar 1 i 0)) := by
      simpa only [proofEraseCtx, EΓ, EA] using (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
    have RL := RN.rename (RigidFunctionObservation.union_world_rename heq hs) W
    rw [subst_bvar_liftN, subst_bvar_liftN] at RL
    have RB : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (A :: Δ) (.app (e.liftN 1) (.bvar 0)) B := by
      simpa only [ProofShape.liftN, Nat.zero_add, lift_eta_inst_bvar] using (ScopedTypeRecovery.app (a := .bvar 0) RL)
    exact RE.trans (.lam .refl (ih RB))

/-- Normalize a fresh generic parameter before any supplied argument is
substituted. The result is independent of that fresh parameter, even when
its annotations depend on the ambient context. -/
theorem NativeUnitProfile.generic_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (H : NativeUnitProfile D s info.ctorName Δ A c)
    (SD : DomainSort Δ A u) (hpos : ¬ u ≈ .zero) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (A :: Δ)
      (etaArgument u) (c.liftN 1) := by
  obtain ⟨Γ, A₀, hΓ, EΓ, hA, EA⟩ := SD
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have W : ContextRenaming Δ (A :: Δ) (fun i => .bvar (liftVar 1 i 0)) := by
    simpa only [proofEraseCtx, EΓ, EA] using (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  have HL := H.rename heq hs W
  rw [subst_bvar_liftN, subst_bvar_liftN] at HL
  have RC := HL.compute heq hs hi hp hx hz (e := .bvar 0) ScopedTypeRecovery.bvar
  simpa only [etaArgument, if_neg hpos] using RC

/-- A positive selected domain carrying a finite native profile makes every
raw supplied argument interchangeable inside its caller. Canonical annotations
may be open and dependent. Only the caller needs native recovery. -/
theorem NativeUnitProfile.caller
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (H : NativeUnitProfile D s info.ctorName Δ A c)
    (SD : DomainSort Δ A u) (hpos : ¬ u ≈ .zero)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f (.forallE A B)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f x) (.app f c) :=
  static_structure_caller_constant_argument RN SD
    (H.generic_argument heq hs hi hp hx hz SD hpos)

/-- A finite profiled domain extends the existing dependent caller telescope.
Later domains retain their substitution by the chosen canonical value. -/
theorem CallerCanonicalTelescope.native_unit_profile
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections s info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (H : NativeUnitProfile D s info.ctorName Δ A c)
    (SD : DomainSort Δ A u) (hpos : ¬ u ≈ .zero)
    (HT : CallerCanonicalTelescope D Δ (B.inst c) n cs) :
    CallerCanonicalTelescope D Δ (.forallE A B) (n+1) (c :: cs) :=
  .cons SD (H.generic_argument heq hs hi hp hx hz SD hpos) HT

end Lean4Lean.VEnv.Strengthening
