import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldFrames

/-! # Descend the remaining native root without forgetting the supplied field

The two-binder witness from the actual empty-prefix cut embeds in the marked
continuation. Native function eta decreases its count with the same supplying
argument through either eta branch. Native structure eta retains a smaller
full-pair minimum, whose fresh field is fixed by the recorded components.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private eta_argument_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertMinimalEtaSpineCut
variable [Params] {D : Definitions}

/-- The actual two-binder root retains the distinguished application in its
smaller minimum. This records the root's original source and pending vector;
its positive primitive charge is included, not silently discarded. -/
theorem PiInertFreshFieldObservedRoot.marked_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : PiInertFreshFieldObservedRoot D Δ family out bound A C v x stage source target) :
    ∃ pending smaller frames, smaller < bound ∧
      PiInertFreshFieldMinimum D Δ Δ family out A x [C]
        (ProofShape.mkApps source pending) smaller frames := by
  obtain ⟨pending, tailCost, e, C', domainStage, cd, suffixArgs, suffixStage, cs, endpoint,
    ck, K, frames, hsmall, HT, HR, RT, SD, RD, HTlam, W, HTnext, RNext, HK, HM⟩ := H
  have RRoot := ((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := pending))).trans RT
  have HTe := HT.pi_inert_compute heq hs RRoot.forget
  let KP : ProofShape → Nat → Prop := fun body k =>
    PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) suffixArgs K (.lam C' body) k
  have HRun : PiInertFreshFieldRun D Δ Δ family out A x [C] KP e (cs+ck) (frames+2) :=
    .retained (args := []) HTe SD RD (pi_inert_retained_frame_interpretation heq hs SD RD)
      (.supply HTlam W HTnext RNext HK)
  refine ⟨pending, 1+tailCost+cs+ck, frames+2, hsmall, KP, stage, 1+tailCost, cs+ck,
    e, HT, ?_, HRun, by omega, HM⟩
  simpa only [Nat.add_zero, List.cons_append, List.nil_append] using RRoot

/-- A function eta at the selected fresh-field root descends below one more
binder, with strict count decrease and the same distinguished future argument.
Both the retained and consumed lambda branches are handled by the marked eta
step; neither branch replaces the actual continuation with an unrelated one. -/
theorem PiInertFreshFieldObservedRoot.eta_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (RN : ScopedTypeRecovery Guard (C :: A :: Δ) source (.forallE B E))
    (SDinner : DomainSort (C :: A :: Δ) B w)
    (H : PiInertFreshFieldObservedRoot D Δ family out bound A C v x stage source
      (.lam B (.app (source.liftN 1) (etaArgument w)))) :
    ∃ smaller frames, smaller < bound ∧
      PiInertFreshFieldMinimum D Δ Δ family out A x [B, C]
        (.app (source.liftN 1) (etaArgument w)) smaller frames := by
  obtain ⟨pending, tailCost, e, C', domainStage, cd, suffixArgs, suffixStage, cs, endpoint,
    ck, K, frames, hsmall, HT, HR, RT, SD, RD, HTlam, W, HTnext, RNext, HK, HM⟩ := H
  have RRoot := ((ScopedComputeCount.base HR).mkApps (ScopedArgumentsCount.refl (args := pending))).trans RT
  have HTe := HT.pi_inert_compute heq hs RRoot.forget
  let KP : ProofShape → Nat → Prop := fun body k =>
    PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) suffixArgs K (.lam C' body) k
  have HRun : PiInertFreshFieldRun D Δ Δ family out A x [C] KP e (cs+ck) (frames+2) :=
    .retained (args := []) HTe SD RD (pi_inert_retained_frame_interpretation heq hs SD RD)
      (.supply HTlam W HTnext RNext HK)
  obtain ⟨smaller, hless, HMin⟩ := pi_inert_eta_fresh_field_descent heq hs hguard HT RN SDinner
    (ScopedComputeCount.beta BetaRed.refl) HR RT HRun (cost := 1+tailCost+cs+ck) (by omega) HM
  exact ⟨smaller, frames+3, by omega, HMin⟩

/-- A selected native structure root has no pending application and retains
its smaller full-source minimum with the distinguished future argument.
Its root charge remains part of that minimum, so this does not claim a
structure-eta bypass. -/
theorem PiInertFreshFieldObservedRoot.structure_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HE : NativeMaskedStructureExpansion Guard (C :: A :: Δ) source target)
    (H : PiInertFreshFieldObservedRoot D Δ family out bound A C v x stage source target) :
    ∃ smaller frames, smaller < bound ∧
      PiInertFreshFieldMinimum D Δ Δ family out A x [C] source smaller frames := by
  obtain ⟨pending, smaller, frames, hsmall, HMin⟩ := H.marked_minimum heq hs
  have HT : TypedSource (C :: A :: Δ) (ProofShape.mkApps source pending) := by
    obtain ⟨_, _, _, _, _, HT, _⟩ := HMin
    exact HT
  have E := TypedSource.structure_eta_pending_nil hguard HT HE
  subst pending
  exact ⟨smaller, frames, hsmall, HMin⟩

private theorem fresh_pair_components_fixed
    (HA : ScopedArgumentsCount (PiInertStage D n) Ξ ca [.bvar i, etaArgument v] fields) :
    fields = [.bvar i, etaArgument v] := by
  cases HA with
  | cons RF rest =>
    cases rest with
    | cons RV last =>
      cases last
      rw [RF.forget.pi_inert_bvar_fixed, eta_argument_fixed RV.forget]

/-- Refine the remaining native-root alternative from the global cut.
Function eta produces a strictly smaller marked body minimum below another
binder. Structure eta is saturated: component ancestry fixes its full source
to the original fresh type/value pair, yielding a smaller marked pair minimum.
Both alternatives retain the exact future argument `x` and the caller's bound.
Recursive readout of these marked minima is the remaining obligation. -/
theorem PiInertFreshFieldObservedRoot.constructor_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (harity : info.nparams + info.numFields = 2)
    (HA : ScopedArgumentsCount (PiInertStage D stage) (C :: A :: Δ) ca
      [.bvar 1, etaArgument v] (pre ++ pending))
    (HR : ConstructorEtaBodyRoot D stage (C :: A :: Δ)
      (ProofShape.mkApps (.const info.ctorName []) pre) target)
    (H : PiInertFreshFieldObservedRoot D Δ family out bound A C v x stage
      (ProofShape.mkApps (.const info.ctorName []) pre) target) :
    (∃ B w smaller frames, smaller < bound ∧
      PiInertFreshFieldMinimum D Δ Δ family out A x [B, C]
        (.app ((ProofShape.mkApps (.const info.ctorName []) pre).liftN 1) (etaArgument w)) smaller frames) ∨
    (∃ smaller frames, smaller < bound ∧
      PiInertFreshFieldMinimum D Δ Δ family out A x [C]
        (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v]) smaller frames) := by
  obtain ⟨k, _, HE | HE⟩ := HR
  · cases HE with
    | intro RN SD =>
      obtain ⟨smaller, frames, hsmall, HMin⟩ := H.eta_descent heq hs
        (erased_static_structure_eta_expansion_stage_descent heq hs k) RN SD
      exact .inl ⟨_, _, smaller, frames, hsmall, HMin⟩
  · have hguard : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D k) :=
      erased_static_structure_eta_expansion_stage_descent heq hs k
    obtain ⟨smaller, frames, hsmall, HMin⟩ := H.structure_minimum heq hs hguard HE
    have HT : TypedSource (C :: A :: Δ) (ProofShape.mkApps (.const info.ctorName []) pre) := by
      obtain ⟨_, _, _, _, _, HT, _⟩ := HMin
      exact HT
    have hlen := TypedSource.structure_constructor_saturated hguard hi HT HE
    have E := fresh_pair_components_fixed HA
    have hargs := congrArg List.length E
    have EP : pending = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_append, List.length_cons, List.length_nil] at hargs
      omega)
    have EPre : pre = [.bvar 1, etaArgument v] := by simpa only [EP, List.append_nil] using E
    exact .inr ⟨smaller, frames, hsmall, EPre ▸ HMin⟩

/-- The actual empty-prefix global cut now either activates the original type
field above the observer or descends to a smaller marked minimum. The native
function case keeps the exact prefix ancestry of its source; the structure
case keeps the full fresh pair. Every alternative reserves the SAME original
field charge and, until activation, the SAME future supplying argument.
This is a proved recursive reduction, not a proof that all marked minima admit
field readout; closing that recursive invariant remains necessary. -/
theorem CountedEtaBodySpineCut.empty_pair_prefix_marked_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hu : info.uvars = 0) (hp : info.nparams = 0)
    (harity : info.nparams + info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hout : ∀ C b rest, out ≠ ProofShape.mkApps (.lam C b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (SD : DomainSort Δ A u)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D outerStage) Δ
      (.const info.ctorName []) (.forallE A B))
    (HTfield : TypedSource Δ field)
    (HT : TypedSource Δ (ProofShape.mkApps (.const info.ctorName []) args))
    (ROuter : ScopedArgumentsCount (PiInertStage D n) Δ outerCost [field, value] args)
    (houter : outerCost ≤ cp)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original
      (ProofShape.mkApps (.const info.ctorName []) args))
    (REta : PiInertStage D n Δ (.const info.ctorName [])
      (.lam A (.app (.const info.ctorName []) (etaArgument u))))
    (H : CountedEtaBodySpineCut D n Δ info.ctorName [] [] A u args major ct
      (ConstructorEtaBodyRoot D))
    (HK : PiInertProjectionRunFrames D Δ family 0 out Δ K major ck frames)
    (hcost : cp+1+ct+ck ≤ budget)
    (HM : ∀ later j endpoint k, ScopedComputeCount (PiInertStage D later) j Δ original endpoint →
      K endpoint k → budget ≤ j+k) :
    ∃ x charge, TypedSource Δ x ∧
      ScopedComputeCount (PiInertStage D n) charge Δ field x ∧
      ((∃ domain value' smaller, charge+smaller < budget ∧
        PiInertProjectionFrameMinimum D Δ family 0 out (domain :: Δ)
          (ProofShape.mkApps (.const info.ctorName []) [x.liftN 1, value']) smaller (frames+1)) ∨
       (∃ C v, DomainSort (A :: Δ) C v ∧
        ((∃ B w pre smaller nextFrames, List.IsPrefix pre [.bvar 1, etaArgument v] ∧
          charge+smaller < budget ∧ PiInertFreshFieldMinimum D Δ Δ family out A x [B, C]
            (.app ((ProofShape.mkApps (.const info.ctorName []) pre).liftN 1) (etaArgument w)) smaller nextFrames) ∨
         (∃ smaller nextFrames, charge+smaller < budget ∧
          PiInertFreshFieldMinimum D Δ Δ family out A x [C]
            (ProofShape.mkApps (.const info.ctorName []) [.bvar 1, etaArgument v]) smaller nextFrames)))) := by
  obtain ⟨x, charge, HTx, RField, HNext | HRoot⟩ :=
    H.empty_pair_prefix_activation_or_root heq hs hi hu hp harity hshape hD hout hproj
      SD RN HTfield HT ROuter houter RP REta HK hcost HM
  · exact ⟨x, charge, HTx, RField, .inl HNext⟩
  · obtain ⟨C, v, stage, pre, pending, target, ca, SDC, HA, HR, HO⟩ := HRoot
    have E := fresh_pair_components_fixed HA
    have HPre : List.IsPrefix pre [.bvar 1, etaArgument v] := ⟨pending, E⟩
    refine ⟨x, charge, HTx, RField, .inr ⟨C, v, SDC, ?_⟩⟩
    rcases HO.constructor_descent heq hs hi harity HA HR with
      ⟨B, w, smaller, nextFrames, hsmall, HMin⟩ | ⟨smaller, nextFrames, hsmall, HMin⟩
    · exact .inl ⟨B, w, pre, smaller, nextFrames, HPre, by omega, HMin⟩
    · exact .inr ⟨smaller, nextFrames, by omega, HMin⟩

end Lean4Lean.VEnv.Strengthening
