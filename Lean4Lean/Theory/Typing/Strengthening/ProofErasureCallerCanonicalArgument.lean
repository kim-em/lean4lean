import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentNeutralHead
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaReplay
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTemplateComputation

/-! # Canonicalizing an argument through its caller

The caller's native Pi supplies a fresh variable with an exact declared type.
If that variable computes to a value independent of it, eta and beta replace
any supplied argument with that value. No recovery of the supplied argument is
needed. Proof-only structures give a concrete instance with arbitrary parameters.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A computation of the caller's generic argument to a binder-independent
value replaces any actual argument. This is a computation of the whole call;
it does not assert a computation of the supplied argument in isolation. -/
theorem static_structure_caller_constant_argument
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f (.forallE A B))
    (SD : DomainSort Δ A u)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (A :: Δ)
      (etaArgument u) (canonical.liftN 1)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f x) (.app f canonical) := by
  have RF : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.lam A (.app (f.liftN 1) (etaArgument u))) :=
    ScopedCompute.base (erased_static_structure_eta_expansion_union_eta (.intro RN SD))
  apply (ScopedCompute.app RF .refl).trans
  apply (ScopedCompute.app (ScopedCompute.lam .refl (ScopedCompute.app .refl RC)) .refl).trans
  have RB := BetaRed.beta (A := A) (b := .app (f.liftN 1) (canonical.liftN 1)) (a := x)
  exact .beta (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.subst, ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id] using RB)

/-- The retained generic value of a proof-only structure computes to a
constructor that no longer refers to that generic value. -/
theorem static_structure_proof_structure_generic_argument
    (hi : env.projections family info) (hx : info.nindices = 0)
    (HF : StructureReplay.ProofFields env univs info ls) (hp : ps.length = info.nparams)
    (hu : ¬ u ≈ .zero) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (ProofShape.mkApps (.const family ls) ps :: Δ) (etaArgument u)
      ((ProofShape.mkApps (.const info.ctorName ls)
        (ps ++ List.replicate info.numFields .proof)).liftN 1) := by
  have RX : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (ProofShape.mkApps (.const family ls) ps :: Δ) (.bvar 0)
      (ProofShape.mkApps (.const family ls) (ps.map (fun a => a.liftN 1))) := by
    have R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (ProofShape.mkApps (.const family ls) ps :: Δ) (.bvar 0)
        ((ProofShape.mkApps (.const family ls) ps).liftN 1) := .bvar
    simpa only [ProofShape.liftN_mkApps, ProofShape.liftN] using R
  have RE := ScopedCompute.base (erased_static_structure_eta_expansion_union_structure
    (NativeMaskedStructureExpansion.intro hi hx (.inr HF) (by simpa using hp) RX))
  rw [nativeStructureOutput_proofFields hi HF] at RE
  simpa only [etaArgument, if_neg hu, ProofShape.liftN_mkApps, ProofShape.liftN, List.map_append,
    List.map_replicate] using RE

/-- A caller whose argument is a positive proof-only structure replaces every
argument by the same masked constructor. Parameters may be open and dependent;
the supplied argument has no native-recovery premise. Empty units are included. -/
theorem static_structure_caller_proof_structure_argument
    (hi : env.projections family info) (hx : info.nindices = 0)
    (HF : StructureReplay.ProofFields env univs info ls) (hp : ps.length = info.nparams)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f
      (.forallE (ProofShape.mkApps (.const family ls) ps) B))
    (SD : DomainSort Δ (ProofShape.mkApps (.const family ls) ps) u) (hu : ¬ u ≈ .zero) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ (.app f x)
      (.app f (ProofShape.mkApps (.const info.ctorName ls)
        (ps ++ List.replicate info.numFields .proof))) :=
  static_structure_caller_constant_argument RN SD
    (static_structure_proof_structure_generic_argument hi hx HF hp hu)

/-- A finite caller telescope can replace each supplied parameter by a fixed
value. Later domains are instantiated by earlier canonical values, so parameter
dependence is retained. Every step carries an actual computation of the generic
argument; no general value-normalization or native-coverage law is assumed. -/
inductive CallerCanonicalTelescope (D : PureObservation.Definitions) (Δ : List ProofShape) :
    ProofShape → Nat → List ProofShape → Prop where
  | nil : CallerCanonicalTelescope D Δ T 0 []
  | cons : DomainSort Δ A u →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (A :: Δ)
        (etaArgument u) (c.liftN 1) →
      CallerCanonicalTelescope D Δ (B.inst c) n cs →
      CallerCanonicalTelescope D Δ (.forallE A B) (n+1) (c :: cs)

/-- Canonicalization preserves the supplied telescope's arity. -/
theorem CallerCanonicalTelescope.length (H : CallerCanonicalTelescope D Δ T n cs) :
    cs.length = n := by
  induction H with
  | nil => rfl
  | cons _ _ _ ih => simp only [List.length_cons, ih]

/-- Proof parameters need no computation or native certificate; their generic
eta argument is already the erased proof marker. -/
theorem CallerCanonicalTelescope.proof
    (SD : DomainSort Δ A u) (hu : u ≈ .zero)
    (H : CallerCanonicalTelescope D Δ (B.inst .proof) n cs) :
    CallerCanonicalTelescope D Δ (.forallE A B) (n+1) (.proof :: cs) :=
  .cons SD (by simpa only [etaArgument, if_pos hu, ProofShape.liftN] using
    (ScopedCompute.refl (Step := ErasedStaticStructureEtaExpansionUnion D)
      (Δ := A :: Δ) (e := ProofShape.proof))) H

/-- A positive proof-only structure parameter has a fixed masked constructor
even when it carries open parameters depending on earlier canonical arguments. -/
theorem CallerCanonicalTelescope.proof_structure
    (hi : env.projections family info) (hx : info.nindices = 0)
    (HF : StructureReplay.ProofFields env univs info ls) (hp : ps.length = info.nparams)
    (SD : DomainSort Δ (ProofShape.mkApps (.const family ls) ps) u) (hu : ¬ u ≈ .zero)
    (H : CallerCanonicalTelescope D Δ
      (B.inst (ProofShape.mkApps (.const info.ctorName ls) (ps ++ List.replicate info.numFields .proof))) n cs) :
    CallerCanonicalTelescope D Δ (.forallE (ProofShape.mkApps (.const family ls) ps) B) (n+1)
      (ProofShape.mkApps (.const info.ctorName ls) (ps ++ List.replicate info.numFields .proof) :: cs) :=
  .cons SD (static_structure_proof_structure_generic_argument hi hx HF hp hu) H

/-- Every raw argument vector of the right length canonicalizes through the
caller. Native recovery is used only for the caller and its partial applications
to canonical values, never for any supplied argument. -/
theorem CallerCanonicalTelescope.compute (H : CallerCanonicalTelescope D Δ T n cs)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) Δ f T)
    (hlen : args.length = n) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
      (ProofShape.mkApps f args) (ProofShape.mkApps f cs) := by
  induction H generalizing f args with
  | nil => have E := List.eq_nil_of_length_eq_zero hlen; subst args; exact .refl
  | cons SD RC H ih =>
    cases args with
    | nil => simp at hlen
    | cons a args =>
      have R := static_structure_caller_constant_argument (x := a) RN SD RC
      exact (ScopedCompute.mkApps R (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))).trans
        (ih (.app RN) (by simpa using hlen))

end Lean4Lean.VEnv.Strengthening
