import Lean4Lean.Theory.Typing.AnchoredViewMaps
import Lean4Lean.Theory.Typing.AnchoredAdmission
import Lean4Lean.Theory.Typing.AnchoredMixedTransport

/-! Domain rekeying copies only rows whose ambient support types the input.
This decidable proposition is equivalent to a nonempty finite support basis,
and is invariant under renaming. The entire support map is fixed in advance. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

theorem domainRekeyTypes.wf {key : Key n} {newDomain : VExpr} {profile : Profile (n + 1)}
    (h : profile.WF) : (domainRekeyTypes key newDomain profile).WF := by
  classical
  intro atom hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
  have hw := h old ho
  cases old with
  | sort | fn | pad | family | ctor | record => exact hw
  | pi A B domain rows =>
    dsimp only [domainRekeyAtom]
    split
    · refine ⟨hw.1, ?_⟩
      intro k result hr
      rcases mem_reanchorRows.mp hr with old | ⟨rfl, old⟩
      · exact hw.2 k result old
      · exact hw.2 key result old
    · exact hw

theorem domainRekeyTypes.sort {key : Key n} {newDomain : VExpr} {profile : Profile (n + 1)}
    (h : profile.HasType (.sort relevant)) :
    (domainRekeyTypes key newDomain profile).HasType (.sort relevant) := by
  classical
  refine ⟨domainRekeyTypes.wf h.wf_value, h.wf_type, ?_⟩
  intro atom hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
  obtain ⟨cover, hc, ht⟩ := h.2.2 old ho
  cases List.mem_singleton.mp hc
  refine ⟨.sort relevant, List.mem_singleton_self _, ?_⟩
  cases old with
  | sort | fn | pad | family | ctor | record => exact ht
  | pi A B domain rows =>
    dsimp only [domainRekeyAtom]
    split
    · intro k result hr
      rcases mem_reanchorRows.mp hr with old | ⟨rfl, old⟩
      · exact ht k result old
      · exact ht key result old
    · exact ht

theorem domainRekeyTypes.typed {key : Key n} {newDomain : VExpr} {output : Atom n}
    {profile : Profile (n + 1)} (h : (Profile.fn key output).HasType profile) :
    (Profile.fn (domainKey key newDomain) output).HasType (domainRekeyTypes key newDomain profile) := by
  classical
  obtain ⟨A, B, domain, rows, result, hm, hw, _, inputTyped, hr, ht⟩ :=
    h.fn_inv (List.mem_singleton_self _)
  have oldWF := Profile.WF.pi_iff.mp hw
  have newWF : (Profile.pi A B domain (reanchorRows key (domainKey key newDomain) rows)).WF := by
    apply Profile.WF.pi_iff.mpr
    refine ⟨oldWF.1, ?_⟩
    intro k result hr
    rcases mem_reanchorRows.mp hr with old | ⟨rfl, old⟩
    · exact oldWF.2 k result old
    · exact oldWF.2 key result old
  have typed := Profile.HasType.fn newWF (reanchorRows.changed hr) ht
  apply typed.enlarge ?_ (domainRekeyTypes.wf h.wf_type)
  intro atom ha
  cases List.mem_singleton.mp ha
  apply Profile.le_refl (domainRekeyTypes key newDomain profile)
  apply List.mem_map.mpr
  exact ⟨_, hm, by simp only [domainRekeyAtom, inputTyped, if_pos]⟩

private theorem exposureInsertion {Γ Δ : List VExpr} {e head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (E : Exposure env U registry Γ e Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := E.insertion henv

def PiWitness.domainRekey
    {Γ : List VExpr} {left right A B newDomain : VExpr} {key : Key n}
    {domain guard : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered)
    (path : TypeConversion env U Γ key.domain newDomain)
    (guardTyped : key.input.HasType guard) (guardFormation : guard.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ key.domain newDomain guard)
    (inputTyped : key.input.HasType domain)
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) :
    PiWitness env U registry (relations env U registry n)
      Γ left right A B domain (reanchorRows key (domainKey key newDomain) rows) := by
  have insertion := exposureInsertion henv display.leftExposure
  have path' := insertion.path henv path
  have bridge' := insertion.code henv bridge
  have guardTyped' := (Profile.rename_hasType_iff (ρ := display.map)).mpr guardTyped
  refine { display with rowDomains := ?_, rowBodies := ?_ }
  · intro k result hm
    rcases mem_reanchorRows.mp hm with old | ⟨rfl, old⟩
    · exact display.rowDomains k result old
    · obtain ⟨support, hs, hsort, _, oldPath, oldLink⟩ := display.rowDomains key result old
      change TypeRelated env U registry display.context (key.domain.lift' display.map)
        display.leftDomain support at oldLink
      obtain ⟨selected, hselected⟩ := Basis.exists inputTyped
      obtain ⟨selectedTyped, selectedBound⟩ := Basis.valid hselected
      have minimal := Basis.minimal hselected
      have minimal' := minimal.rename display.map
      have domainCode : TypeRelated env U registry display.context
          display.leftDomain display.rightDomain (domain.rename display.map) := display.domainRelated
      have focused := domainCode.focusMinimal henv minimal'
        (Profile.rename_le_iff.mpr selectedBound)
      have toOld := focused.left_diagonal.composeMinimal henv minimal' hs
        (oldLink.symm henv hs.wf_type)
      have toNew := toOld.composeMinimal henv minimal' guardTyped' bridge'
      refine ⟨selected.rename display.map, Profile.rename_hasType_iff.mpr selectedTyped,
        ?_, Profile.rename_le_iff.mpr selectedBound, path'.symm.trans oldPath,
        toNew.symm henv (Profile.rename_wf_iff.mpr selectedTyped.wf_type)⟩
      simpa only [Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := display.map)).mpr minimal.formation
  · intro k result hm Δ ρ future x y admitted
    rcases mem_reanchorRows.mp hm with old | ⟨rfl, old⟩
    · exact display.rowBodies k result old Δ ρ future x y admitted
    · have reversePath := (insertion.path henv path.symm).weak' henv future.weakening
      have reverseBridge := TypeRelated.future henv future (insertion.code henv (bridge.symm henv guardTyped.wf_type))
      have ht := (Profile.rename_hasType_iff (ρ := display.map.comp ρ)).mpr guardTyped
      have hf := (Profile.rename_hasType_iff (ρ := display.map.comp ρ)).mpr guardFormation
      rw [Profile.rename_sort] at hf
      simp only [← lift'_comp, ← Profile.rename_comp] at reversePath reverseBridge
      have oldAdmission := Admitted.rekey henv reversePath ht hf reverseBridge admitted
      exact display.rowBodies key result old Δ ρ future x y oldAdmission

theorem TypeRelated.domainRekey
    {Γ : List VExpr} {left right newDomain : VExpr} {key : Key n}
    {guard : Profile n} {profile : Profile (n + 1)}
    (henv : env.Ordered)
    (path : TypeConversion env U Γ key.domain newDomain)
    (guardTyped : key.input.HasType guard) (guardFormation : guard.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ key.domain newDomain guard)
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (domainRekeyTypes key newDomain profile) := by
  classical
  intro Δ ρ future atom ha
  rw [domainRekeyTypes_rename] at ha
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp ha
  have hc := h Δ ρ future old hm
  cases old with
  | sort | fn | pad | family | ctor | record => exact hc
  | pi A B domain rows =>
    dsimp only [domainRekeyAtom]
    split
    · obtain ⟨display⟩ := hc
      have hf := (Profile.rename_hasType_iff (ρ := ρ)).mpr guardFormation
      rw [Profile.rename_sort] at hf
      exact ⟨display.domainRekey henv (path.weak' henv future.weakening)
        (Profile.rename_hasType_iff.mpr guardTyped) hf
        (TypeRelated.future henv future bridge) ‹_›⟩
    · exact hc

theorem FunctionBehavior.domainRekey
    {Γ : List VExpr} {left right type newDomain : VExpr} {key : Key n} {output : Atom n}
    {guard : Profile n} {profile : Profile (n + 1)}
    (henv : env.Ordered)
    (path : TypeConversion env U Γ key.domain newDomain)
    (guardTyped : key.input.HasType guard) (guardFormation : guard.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ key.domain newDomain guard)
    (typed : (Profile.fn key output).HasType profile)
    (h : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ left right type (domainKey key newDomain) output (domainRekeyTypes key newDomain profile) := by
  classical
  obtain ⟨seed, A, B, domain, rows, result, hmem, hrow, ht, display, behavior⟩ := h
  have hw := typed.wf_type _ hmem
  have inputTyped : key.input.HasType domain := (hw.2 key result hrow).1
  refine ⟨Admitted.rekey henv path guardTyped guardFormation bridge seed,
    A, B, domain, reanchorRows key (domainKey key newDomain) rows, result,
    List.mem_map.mpr ⟨_, hmem, ?_⟩, reanchorRows.changed hrow, ht,
    display.domainRekey henv path guardTyped guardFormation bridge inputTyped, ?_⟩
  · simp only [domainRekeyAtom, inputTyped, if_pos]
  · intro Δ ρ future x y admitted
    have insertion := exposureInsertion henv display.leftExposure
    have ht := (Profile.rename_hasType_iff (ρ := display.map.comp ρ)).mpr guardTyped
    have hf := (Profile.rename_hasType_iff (ρ := display.map.comp ρ)).mpr guardFormation
    rw [Profile.rename_sort] at hf
    have reversePath := (insertion.path henv path.symm).weak' henv future.weakening
    have reverseBridge := TypeRelated.future henv future (insertion.code henv (bridge.symm henv guardTyped.wf_type))
    simp only [← lift'_comp, ← Profile.rename_comp] at reversePath reverseBridge
    exact behavior Δ ρ future x y (Admitted.rekey henv reversePath ht hf reverseBridge admitted)

/-- The public term leaf requires no new observation or intrinsic gate: its
existing core typing supplies the gate for the chosen function row. -/
theorem Related.domainRekey
    {Γ : List VExpr} {left right type newDomain : VExpr} {key : Key n} {output : Atom n}
    {guard : Profile n} {profile : Profile (n + 1)}
    (henv : env.Ordered)
    (path : TypeConversion env U Γ key.domain newDomain)
    (guardTyped : key.input.HasType guard) (guardFormation : guard.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ key.domain newDomain guard)
    (h : Related env U registry Γ left right type (Profile.fn key output) profile) :
    Related env U registry Γ left right type (Profile.fn (domainKey key newDomain) output)
      (domainRekeyTypes key newDomain profile) := by
  intro requested hrequested Δ ρ future
  cases List.mem_singleton.mp hrequested
  have hs := h (.fn key output) (List.mem_singleton_self _) Δ ρ future
  rcases hs with hempty | ⟨Ω, τ, insertion, typed, code, values⟩
  · cases hempty
  · have full := future.comp insertion.toFuture henv
    have path' := path.weak' henv full.weakening
    have bridge' := TypeRelated.future henv full bridge
    have guardTyped' := (Profile.rename_hasType_iff (ρ := ρ.comp τ)).mpr guardTyped
    have guardFormation' := (Profile.rename_hasType_iff (ρ := ρ.comp τ)).mpr guardFormation
    rw [Profile.rename_sort] at guardFormation'
    simp only [lift'_comp, Profile.rename_comp] at path' bridge' guardTyped' guardFormation'
    change (Profile.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ)).HasType
      ((profile.rename ρ).rename τ) at typed
    change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
      ((type.lift' ρ).lift' τ) ((profile.rename ρ).rename τ) at code
    have newTyped := domainRekeyTypes.typed (newDomain := (newDomain.lift' ρ).lift' τ) typed
    have newCode := TypeRelated.domainRekey (key := (key.rename ρ).rename τ)
      henv path' guardTyped' guardFormation' bridge' code
    have behavior := values (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
      (List.mem_singleton_self _)
    have newBehavior := FunctionBehavior.domainRekey henv path' guardTyped' guardFormation' bridge' typed behavior
    right
    refine ⟨Ω, τ, insertion, ?_, ?_, ?_⟩
    · simpa only [domainRekeyTypes_rename, Profile.fn, Profile.rename_singleton,
        Atom.rename_fn, domainKey, Key.rename] using newTyped
    · change TypeRelated env U registry Ω ((type.lift' ρ).lift' τ)
        ((type.lift' ρ).lift' τ) (((domainRekeyTypes key newDomain profile).rename ρ).rename τ)
      simpa only [domainRekeyTypes_rename] using newCode
    · intro atom ha
      cases List.mem_singleton.mp ha
      simpa only [domainRekeyTypes_rename, domainKey, Key.rename, Atom.rename_fn,
        TermAtom] using newBehavior

end Lean4Lean.AnchoredSemantics
