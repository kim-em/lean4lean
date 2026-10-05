import Lean4Lean.Theory.Typing.AnchoredOriginalLambdaCoherence

/-! Structural replay of every current observation/certificate wrapper around
literal Pi queries. The primitive callback is instantiated by the fixed
original lambda body-pair induction, not by a global coherence supplier. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private def PiAtom : {n : Nat} → Atom n → Prop
  | 0, _ => False
  | _ + 1, .pi .. => True
  | _ + 1, .pad atom => PiAtom atom
  | _ + 1, _ => False

private theorem piAtom_view_eq
    {a b : Atom n} (view : AtomView env U registry target a b)
    (shape : PiAtom a) : a = b := by
  match n, a, b, view with
  | _, _, _, .refl _ => rfl
  | _ + 1, _, _, .reanchor _ => cases shape
  | _ + 1, _, _, .domainRekey .. => cases shape
  | _ + 1, _, _, .input .. => cases shape
  | _ + 2, _, _, .commutePadFn .. => cases shape
  | _ + 2, _, _, .uncommutePadFn .. => cases shape
  | _ + 1, _, _, .fn .. => cases shape
  | _ + 1, _, _, .pad child => exact congrArg AtomData.pad (piAtom_view_eq child shape)
  | _, _, _, .trans first second =>
    have eq := piAtom_view_eq first shape
    exact eq.trans (piAtom_view_eq second (eq ▸ shape))
termination_by sizeOf view

private theorem Obs.piShape
    (observation : Obs env U registry target locals σ (.forallE A B) profile footprint) :
    ∀ atom ∈ profile.atoms, PiAtom atom := by
  match observation with
  | .empty => exact fun _ member => nomatch member
  | .pi .. =>
    intro atom member
    cases List.mem_singleton.mp member
    trivial
  | .union left right =>
    intro atom member
    exact (List.mem_append.mp member).elim (Obs.piShape left atom) (Obs.piShape right atom)
  | .view source view =>
    have eq := piAtom_view_eq view (Obs.piShape source _ (List.mem_singleton_self _))
    intro atom member
    cases List.mem_singleton.mp member
    exact eq ▸ Obs.piShape source _ (List.mem_singleton_self _)
  | .pad source =>
    intro atom member
    obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp member
    cases equal
    exact Obs.piShape source old oldMember
  | .unpad source =>
    intro atom member
    exact Obs.piShape source (.pad atom) (List.mem_map_of_mem member)
  | .rowShift source =>
    have impossible := Obs.piShape source _ (List.mem_singleton_self _)
    exact False.elim impossible
termination_by sizeOf observation

section
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {leftLocals rightLocals : List Nat} {σ τ : Subst}
  {leftAvailable rightAvailable : Valuation} {A B C D : VExpr}

/-- Only literal Pi leaves reach this finite algebra. All outer wrappers are
handled by the checked workers below, including hereditary focus. -/
def LambdaPiCase :=
  ∀ {n : Nat} {ambient : Profile n} {table : List (Key n × Profile n)}
    {prototypeDomain prototypeBody : VExpr} {domainFootprint rowFootprint : Footprint},
    (domain : CodeCert env U registry target leftLocals σ A ambient domainFootprint) →
    (guard : PiGuard env U target σ A B prototypeDomain prototypeBody) →
    (rows : PiRows env U registry target leftLocals σ A B ambient table rowFootprint) →
    (domainFootprint ++ rowFootprint).Available leftAvailable →
    Nonempty (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      (.forallE A B) (.forallE C D) (Profile.pi prototypeDomain prototypeBody ambient table))

theorem Obs.transferLambdaPi
    (henv : env.Ordered)
    (piCase : LambdaPiCase (env := env) (U := U) (registry := registry)
      (target := target) (leftLocals := leftLocals) (rightLocals := rightLocals)
      (σ := σ) (τ := τ) (leftAvailable := leftAvailable) (rightAvailable := rightAvailable)
      (A := A) (B := B) (C := C) (D := D))
    (observation : Obs env U registry target leftLocals σ (.forallE A B) profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      (.forallE A B) (.forallE C D) profile) := by
  match observation with
  | .empty =>
    exact ⟨⟨[], .seed .empty (Profile.HasType.empty (Profile.HasType.sort true).wf_value),
      (fun _ _ member => nomatch member), by rename_i rank; cases rank <;> exact fun _ _ _ _ member => nomatch member⟩⟩
  | .pi domain guard rows => exact piCase domain guard rows resources
  | .union left right =>
    obtain ⟨a⟩ := Obs.transferLambdaPi henv piCase left
      (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := Obs.transferLambdaPi henv piCase right
      (fun i need member => resources i need (List.mem_append_right _ member))
    refine ⟨⟨a.footprint ++ b.footprint, .union a.certificate b.certificate,
      (fun i need member => (List.mem_append.mp member).elim
        (a.available i need) (b.available i need)), ?_⟩⟩
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => a.related.singleton h) (fun h => b.related.singleton h)
  | .view source view =>
    have equal := piAtom_view_eq view (Obs.piShape source _ (List.mem_singleton_self _))
    subst equal
    exact Obs.transferLambdaPi henv piCase source resources
  | .pad source =>
    obtain ⟨answer⟩ := Obs.transferLambdaPi henv piCase source resources
    exact ⟨⟨answer.footprint, .pad answer.certificate, answer.available, answer.related.pad henv⟩⟩
  | .unpad source =>
    obtain ⟨answer⟩ := Obs.transferLambdaPi henv piCase source resources
    exact ⟨⟨answer.footprint, .unpad answer.certificate, answer.available,
      (TypeRelated.pad_iff henv).mp answer.related⟩⟩
  | .rowShift source =>
    exact False.elim (Obs.piShape source _ (List.mem_singleton_self _))
termination_by sizeOf observation

/-- Replay every current certificate constructor, including map/input views,
selection, down, familyPad and hereditary focus, without altering its query. -/
theorem CodeCert.transferLambdaPi
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (piCase : LambdaPiCase (env := env) (U := U) (registry := registry)
      (target := target) (leftLocals := leftLocals) (rightLocals := rightLocals)
      (σ := σ) (τ := τ) (leftAvailable := leftAvailable) (rightAvailable := rightAvailable)
      (A := A) (B := B) (C := C) (D := D))
    (cert : CodeCert env U registry target leftLocals σ (.forallE A B) profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      (.forallE A B) (.forallE C D) profile) := by
  match cert with
  | .seed observation _ => exact Obs.transferLambdaPi henv piCase observation resources
  | .union left right =>
    obtain ⟨hl⟩ := CodeCert.transferLambdaPi henv hscoped piCase left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨hr⟩ := CodeCert.transferLambdaPi henv hscoped piCase right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    refine ⟨⟨hl.footprint ++ hr.footprint, .union hl.certificate hr.certificate, ?_, ?_⟩⟩
    · intro i need hm
      exact (List.mem_append.mp hm).elim (hl.available i need) (hr.available i need)
    · apply TypeRelated.of_singletons
      intro atom hm
      exact (List.mem_append.mp hm).elim
        (fun h => hl.related.singleton h) (fun h => hr.related.singleton h)
  | .pad source =>
    obtain ⟨result⟩ := CodeCert.transferLambdaPi henv hscoped piCase source resources
    exact ⟨⟨result.footprint, .pad result.certificate, result.available,
      result.related.pad henv⟩⟩
  | .familyPad source =>
    obtain ⟨result⟩ := CodeCert.transferLambdaPi henv hscoped piCase source resources
    exact ⟨⟨result.footprint, .familyPad result.certificate, result.available,
      result.related.familyPad henv⟩⟩
  | .unpad source =>
    obtain ⟨result⟩ := CodeCert.transferLambdaPi henv hscoped piCase source resources
    exact ⟨⟨result.footprint, .unpad result.certificate, result.available,
      (TypeRelated.pad_iff henv).mp result.related⟩⟩
  | .down source =>
    obtain ⟨result⟩ := CodeCert.transferLambdaPi henv hscoped piCase source resources
    exact ⟨⟨result.footprint, .down result.certificate, result.available,
      result.related.down henv⟩⟩
  | .map view source =>
    obtain ⟨result⟩ := CodeCert.transferLambdaPi henv hscoped piCase source resources
    exact ⟨⟨result.footprint, .map view result.certificate, result.available,
      view.codeMap henv hscoped result.related⟩⟩
  | .select source member =>
    obtain ⟨result⟩ := CodeCert.transferLambdaPi henv hscoped piCase source resources
    exact ⟨⟨result.footprint, .select result.certificate member, result.available,
      result.related.singleton member⟩⟩
  | .focusMinimal source minimal focusedBound =>
    obtain ⟨result⟩ := CodeCert.transferLambdaPi henv hscoped piCase source resources
    exact ⟨⟨result.footprint, .focusMinimal result.certificate minimal focusedBound, result.available,
      result.related.focusMinimal henv minimal focusedBound⟩⟩
termination_by sizeOf cert

end
end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
