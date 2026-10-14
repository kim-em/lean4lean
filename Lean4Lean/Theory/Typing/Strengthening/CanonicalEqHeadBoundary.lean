import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqRegistry
import Lean4Lean.Theory.Typing.Strengthening.EqConstructorBoundary
import Lean4Lean.Theory.Typing.Confluence.WFParams

/-! # Canonical equality and the augmented head model

Eq's projection metadata cannot be unindexed, and the family of every registered
Eq.rec is Eq itself. These facts exclude closed structure unfoldings as well as
unindexed singleton unfoldings at this recursor head.
-/
namespace Lean4Lean.VEnv
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
variable {env : VEnv}

/-- A projection entry of Eq has a nonzero index count. Its only constructor
has two arguments while the family takes three arguments. -/
theorem HasCanonicalEq.projection_indexed (heq : env.HasCanonicalEq) (henv : env.WF)
    (hi : env.projections ``Eq info) : info.nindices ≠ 0 := by
  obtain ⟨doms, hc, _, hp⟩ := heq.2.2.2
  have hpat : IsPatCtor env ``Eq.refl := ⟨_, _, ``Eq.rec, 5, 2, hp, rfl⟩
  have hname := henv.structureCtorCoherent ``Eq info hi ``Eq.refl hpat
    ⟨_, [.param 0], heq.2.1, rfl⟩
  have hctor := henv.ordered.projectionConstructor hi
  rw [← hname, heq.2.1] at hctor
  have htype := congrArg VConstant.type (Option.some.inj hctor)
  change canonicalEqReflType = info.ctorType at htype
  obtain ⟨decl, fam, ctor, _, _, _, _, _, hnparams, _, _, _, hct,
    _, _, _, hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨domains, result, _, hle, _, _, harity⟩ := hraw.forallArity
  rw [hct, ← htype] at harity
  change 2 = domains.length at harity
  have hprop : env.HasType 0 []
      (mkApps (.const ``Eq [.succ (.succ .zero)])
        [.sort (.succ .zero), .sort .zero, .sort .zero]) (.sort .zero) :=
    HasType.eqApp heq (by trivial) (.sort (by trivial))
      (.sort (by trivial)) (.sort (by trivial))
  have ha := Strengthening.StructureReplay.family_arity henv (by trivial) hi ⟨_, hprop⟩
  simp only [List.length_cons, List.length_nil] at ha
  omega

/-- The major-family head in a registered canonical Eq.rec is syntactically Eq.
The proof reads the sixth domain of its installed telescope. -/
theorem RecursorRegistered.eqRec_family (heq : env.HasCanonicalEq)
    (hr : RecursorRegistered env data) (hn : data.name = ``Eq.rec) :
    Strengthening.ClosedStructure.family data = ``Eq := by
  obtain ⟨type, ht⟩ := hr.recursorType_exists
  have hc := hr.recursorType ht
  rw [hn, heq.2.2.1] at hc
  have htype := congrArg VConstant.type (Option.some.inj hc)
  change canonicalEqRecType = type at htype
  obtain ⟨ci, hci, harity⟩ := hr.constant_piArity
  rw [hn, heq.2.2.1] at hci
  cases Option.some.inj hci
  change 6 = data.majorOffset + 1 at harity
  have hoff : data.majorOffset = 5 := by omega
  obtain ⟨domains, body, args, hs, hlen, hd⟩ := RecursorData.recursorType_major ht
  have hscan : canonicalEqRecType.takeForalls 6 = some (domains, body) := by
    rw [htype, hs, harity, ← hlen]
    exact takeForalls_wrapForalls _ _
  have hds := congrArg Prod.fst (Option.some.inj hscan)
  dsimp only [Prod.fst] at hds
  rw [hoff, ← hds] at hd
  have hh := congrArg (fun e => e.getAppFnArgs.1) (Option.some.inj hd)
  simp only [VExpr.getAppFnArgs_mkApps_const] at hh
  exact (VExpr.const.inj hh).1.symm

namespace Strengthening.ConstructorObservation

/-- The extra structure equations cannot unfold canonical Eq.rec: their
unindexed-family premise contradicts Eq's projection metadata. -/
theorem eqRec_no_structure_unfold (henv : env.WF) (heq : env.HasCanonicalEq) :
    ¬ @ClosedStructure.Unfolds (henv.params U) ``Eq.rec levels rhs := by
  intro h
  generalize hn : ``Eq.rec = name at h
  cases h with
  | intro hr _ _ hi hz _ _ _ =>
    rw [hr.eqRec_family heq hn.symm] at hi
    exact heq.projection_indexed henv hi hz

/-- None of the equations in the full current head model unfolds Eq.rec.
Stored definitions, Quot, structures, and unindexed singleton additions are
all excluded; these are all the model's existing closed-equation additions. -/
theorem eqRec_no_full_unfold (henv : env.WF) (heq : env.HasCanonicalEq) :
    ¬ (FullHead.definitions henv heq U).unfolds ``Eq.rec levels rhs := by
  letI := henv.params U
  rintro ((h | h) | h)
  · unfold FullHead.quotDefinitions at h
    split at h
    · rcases h with h | ⟨h, _⟩
      · exact eqRec_no_stored_unfold henv heq h
      · exact (by decide : (``Eq.rec : Name) ≠ ``Quot.lift) h
    · exact eqRec_no_stored_unfold henv heq h
  · exact eqRec_no_structure_unfold henv heq h
  · exact eqRec_no_unindexed_unfold henv heq h

/-- Even with all added closed equations, a variable-major reflexive cast
cannot expose a Pi in this head model, although the typed K equation holds. -/
theorem canonical_cast_full_boundary (henv : env.WF) (heq : env.HasCanonicalEq)
    (hu : u.WF U) (hΓ : OnCtx Γ (env.IsType U))
    (hX : env.HasType U Γ X (.sort u))
    (hq : env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) X X))
    (hpi : env.HasType U Γ (.forallE A B) X) :
    env.IsDefEq U Γ (typeCast u X X (.bvar i) (.forallE A B)) (.forallE A B) X ∧
      ∀ A' B', ¬ @EtaCompute (henv.params U) (FullHead.definitions henv heq U)
        (typeCast u X X (.bvar i) (.forallE A B)) (.forallE A' B') := by
  letI := henv.params U
  obtain ⟨data, hl, _, _, hoff, _⟩ := heq.recursorRegistration henv
  refine ⟨IsDefEq.typeCast_refl henv heq hu hΓ hX hq hpi, fun _ _ => ?_⟩
  exact recursor_variable_no_pi (D := FullHead.definitions henv heq U) hl
    (fun _ => eqRec_no_full_unfold henv heq)
    (args := [.sort u, X, castMotive u X, .forallE A B, X])
    (by simp [hoff]) (FullHead.rigid henv heq)

end Strengthening.ConstructorObservation

namespace Strengthening

/-- A normal comparison with a Pi has a Pi at its other end too. Proof
irrelevance and function eta cannot disguise a Pi as another head form. -/
theorem normal_pi_right [Params] (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (H : NormalEq Γ e (.forallE A B)) : ∃ A' B', e = .forallE A' B' := by
  obtain ⟨n, H⟩ := H
  generalize he : VExpr.forallE A B = right at H
  cases H with
  | refl => cases he; exact ⟨_, _, rfl⟩
  | forallEDF => cases he; exact ⟨_, _, rfl⟩
  | etaL ht _ => subst he; exact (ht.forallE_not_pi hΓ ht).elim
  | etaBoth _ ht _ => subst he; exact (ht.forallE_not_pi hΓ ht).elim
  | proofIrrel hp _ ht => subst he; exact (HasType.forallE_not_proof hΓ hp ht).elim
  | _ => cases he

/-- Confluence turns an actual equality with a Pi into a full reduction to
some Pi. No normalization or reflection hypothesis is needed. -/
theorem defeq_pi_full_exposure (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e (.forallE A B) T) :
    ∃ A' B', @FullReduction (henv.params U) Γ e (.forallE A' B') := by
  letI := henv.params U
  obtain ⟨left, right, hl, hr, hn⟩ := henv.church_rosser heq hΓ H
  obtain ⟨_, _, rfl, _, _⟩ := hr.forallE_inv hΓ H.hasType.2
  obtain ⟨_, _, rfl⟩ := normal_pi_right hΓ hn
  exact ⟨_, _, hl⟩

/-- The indexed-prefix replay premise of the current full head model is false
in every canonical-Eq environment. A reflexive cast has actual full Pi exposure,
but the augmented model cannot expose a Pi through its free proof major.
This refutes the model obligation, not strengthening or typed head recovery. -/
theorem not_indexedPrefixReplay (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) :
    ¬ FullHead.IndexedPrefixReplay henv heq U := by
  letI := henv.params U
  intro hi
  let u : VLevel := .succ (.succ .zero)
  let X : VExpr := .sort (.succ .zero)
  let Q := eqApp (.succ u) (.sort u) X X
  have hu : u.WF U := by trivial
  have hX {Γ} : env.HasType U Γ X (.sort u) := .sort (by trivial)
  have hQ : env.HasType U [] Q (.sort .zero) :=
    HasType.eqApp heq (by trivial) (.sort hu) hX hX
  have hΓ : OnCtx [Q] (env.IsType U) := ⟨trivial, _, hQ⟩
  have hq : env.HasType U [Q] (.bvar 0) Q := by
    have h : env.HasType U [Q] (.bvar 0) Q.lift := .bvar .zero
    simpa [Q, X, eqApp, liftN] using h
  have hpi : env.HasType U [Q] (.forallE (.sort .zero) (.sort .zero)) X := by
    have ht : env.HasType U [Q] (.forallE (.sort .zero) (.sort .zero))
        (.sort (.imax (.succ .zero) (.succ .zero))) :=
      .forallE (.sort (by trivial)) (.sort (by trivial))
    exact (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq ht
  obtain ⟨he, hn⟩ := ConstructorObservation.canonical_cast_full_boundary
    henv heq hu hΓ hX hq hpi
  obtain ⟨A, B, hr⟩ := defeq_pi_full_exposure henv heq hΓ he
  exact hn A B (FullHead.reduction_of_indexed henv heq hi hr hΓ he.hasType.1).2

end Strengthening
end Lean4Lean.VEnv
