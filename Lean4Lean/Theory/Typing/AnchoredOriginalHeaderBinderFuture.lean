import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFuture

/-! Future target contexts preserve the actual heterogeneous capture and
binder frames, including every original rich declared-domain certificate.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private subst_cons_future from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
set_option backward.isDefEq.respectTransparency false

noncomputable def RichBinderValue.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    (value : RichBinderValue sourceEnv env U registry Γ owner locals left right available input) :
    RichBinderValue sourceEnv env U registry Δ owner locals (left.lift_r ρ) (right.lift_r ρ)
      (available.rename ρ) (input.rename ρ) where
  support := value.support.rename ρ
  footprint := Footprint.rename ρ value.footprint
  certificate := value.certificate.future henv future
  resources := value.resources.rename ρ
  typed := Profile.rename_hasType_iff.mpr value.typed
  related := by simpa only [lift'_subst] using value.related.future henv future

noncomputable def HeaderValueAlignment.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (answer : HeaderValueAlignment owner domain env registry Γ ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) :
    HeaderValueAlignment owner domain env registry Δ ownerLocals headerLocals
      (ownerLeft.lift_r ρ) (ownerRight.lift_r ρ) (declaredLeft.lift_r ρ)
      (ownerAvailable.rename ρ) (headerAvailable.rename ρ) (input.rename ρ) where
  value := answer.value.future henv future
  aligned := {
    footprint := Footprint.rename ρ answer.aligned.footprint
    certificate := answer.aligned.certificate.future henv future
    resources := answer.aligned.resources.rename ρ
    related := by simpa only [RichBinderValue.future, lift'_subst] using answer.aligned.related.future henv future }
  path := by simpa only [lift'_subst] using answer.path.weak' henv future.weakening

private theorem renamedBound (needs : List Need) (ρ : Lift)
    (bounded : ∀ need ∈ needs, need.rank ≤ n) :
    ∀ need ∈ needs.map (Need.rename ρ), need.rank ≤ n := by
  intro need member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  exact bounded old oldMember

private theorem renamedCoverage (needs : List Need) (ρ : Lift) {input : Profile n}
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    ∀ need ∈ needs.map (Need.rename ρ),
      ∀ atom ∈ (need.atGrade n).atoms, atom ∈ (input.rename ρ).atoms := by
  intro need member atom atomMember
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  rw [← Need.atGrade_rename] at atomMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp atomMember
  exact List.mem_map_of_mem (covered old oldMember original originalMember)

noncomputable def HeaderRichTail.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    {context : ContextDerivation headerEnv U headerSource}
    (tail : HeaderRichTail header field major env registry Γ context locals left right available) :
    HeaderRichTail header field major env registry Δ context locals (left.lift_r ρ) (right.lift_r ρ)
      (available.rename ρ) := by
  match tail with
  | .nil => exact .nil
  | .skip tail domain location lineage arguments =>
    have shifted := arguments.weak' henv future.weakening
    rw [lift'_subst] at shifted
    simpa only [subst_cons_future, Valuation.rename_push, List.map_nil] using
      HeaderRichTail.skip (tail.future henv future) domain location lineage shifted
  | .push tail domain location lineage owner answer arguments needs bounded covered =>
    have shifted := arguments.future henv future
    simp only [lift'_subst] at shifted
    simpa only [subst_cons_future, lift'_subst, Valuation.rename_push] using
      HeaderRichTail.push (tail.future henv future) domain location lineage owner
        (answer.future henv future) shifted (needs.map (Need.rename ρ))
        (renamedBound needs ρ bounded) (renamedCoverage needs ρ covered)
termination_by sizeOf tail
decreasing_by all_goals simp_wf <;> omega

noncomputable def HeaderBinderFrame.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (future : FutureInsertion env U Γ Δ ρ)
    {context : ContextDerivation headerEnv U headerSource}
    (frame : HeaderBinderFrame header field major env registry Γ context locals left right available) :
    HeaderBinderFrame header field major env registry Δ context locals (left.lift_r ρ) (right.lift_r ρ)
      (available.rename ρ) := by
  match frame with
  | .captured tail => exact .captured (tail.future henv future)
  | .bind tail domain location lineage certificate resources typed arguments needs bounded covered =>
    have shifted := arguments.future henv future
    rw [lift'_subst] at shifted
    simpa only [subst_cons_future, Valuation.rename_push] using
      HeaderBinderFrame.bind (tail.future henv future) domain location lineage
        (certificate.future henv future) (resources.rename ρ) (Profile.rename_hasType_iff.mpr typed)
        shifted (needs.map (Need.rename ρ)) (renamedBound needs ρ bounded)
        (renamedCoverage needs ρ covered)
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
