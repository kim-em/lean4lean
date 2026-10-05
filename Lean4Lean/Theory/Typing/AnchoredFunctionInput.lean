import Lean4Lean.Theory.Typing.AnchoredInputAdmission

/-! Adapt a function row contravariantly along concrete paired input views.
The backward view rebuilds caller-domain capabilities at a fixed finite basis;
the forward view transports every admitted argument. The interpretation laws
are strict lower-rank induction hypotheses discharged by the view interpreter. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

private theorem exposureInsertion {Γ Δ : List VExpr} {e head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (E : Exposure env U registry Γ e Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := E.insertion henv

noncomputable def PiWitness.inputView
    (henv : env.Ordered)
    (lowerCode : ∀ {Δ : List VExpr} {p q : Profile n}
      (v : ProfileView env U registry Δ p q) {l r : VExpr} {d : Profile n},
      TypeRelated env U registry Δ l r d → TypeRelated env U registry Δ l r (v.mapType d))
    (lowerTerm : ∀ {Δ : List VExpr}, OnCtx Δ (env.IsType U) →
      ∀ {p q : Profile n} (v : ProfileView env U registry Δ p q)
      {l r A : VExpr} {d : Profile n}, p.HasType d →
      Related env U registry Δ l r A p d → Related env U registry Δ l r A q (v.mapType d))
    {Γ : List VExpr} {key : Key n} {input domain : Profile n}
    {left right A B : VExpr} {rows : List (Key n × Profile n)}
    (forward : ProfileView env U registry Γ input key.input)
    (backward : ProfileView env U registry Γ key.input input)
    (typed : key.input.HasType domain)
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows) :
    PiWitness env U registry (relations env U registry n) Γ left right A B
      (inputDomain key.input backward.mapType domain)
      (reanchorRows key (inputKey key input) rows) := by
  have insertion := exposureInsertion henv display.leftExposure
  let back := backward.mixed henv insertion
  have hd : (inputDomain key.input backward.mapType domain).rename display.map =
      inputDomain (key.rename display.map).input back.mapType (domain.rename display.map) :=
    inputDomain.rename key.input domain display.map backward.mapType back.mapType
      (backward.mapType_mixed henv insertion)
  refine { display with domainRelated := ?_, rowDomains := ?_, rowBodies := ?_ }
  · rw [hd]
    exact inputDomain.code henv (fun _ h => lowerCode back h) display.domainRelated
  · intro k result hr
    rcases mem_reanchorRows.mp hr with old | ⟨rfl, old⟩
    · obtain ⟨support, hs, hf, hb, path, code⟩ := display.rowDomains k result old
      refine ⟨support, hs, hf, ?_, path, code⟩
      rw [hd]
      exact Profile.le_trans hb inputDomain.original
    · obtain ⟨support, hs, _, _, path, code⟩ := display.rowDomains key result old
      have ht := (Profile.rename_hasType_iff (ρ := display.map)).mpr typed
      obtain ⟨selected, htyped, hformed, hbound, hcode⟩ := inputDomain.bridge henv
        (fun _ h => back.mapType_sort h) (fun _ h => back.mapType_typed h)
        (fun _ h => lowerCode back h) ht hs display.domainRelated code
      refine ⟨selected, htyped, hformed, ?_, path, hcode⟩
      rw [hd]
      exact hbound
  · intro k result hr Δ ρ future x y admitted
    rcases mem_reanchorRows.mp hr with old | ⟨rfl, old⟩
    · exact display.rowBodies k result old Δ ρ future x y admitted
    · have front : ProfileView env U registry Δ (input.rename (display.map.comp ρ))
          (key.input.rename (display.map.comp ρ)) := by
        simpa only [Profile.rename_comp] using (forward.mixed henv insertion).future henv future
      have oldAdmission := front.admissionMapWith (future.targetWF henv)
        lowerCode lowerTerm admitted
      have oldAdmission' : Admitted env U registry Δ
          (key.rename (display.map.comp ρ)) x y := by
        simpa only [inputKey, Key.rename] using oldAdmission
      exact display.rowBodies key result old Δ ρ future x y oldAdmission'

theorem TypeRelated.inputView
    (henv : env.Ordered)
    (lowerCode : ∀ {Δ : List VExpr} {p q : Profile n}
      (v : ProfileView env U registry Δ p q) {l r : VExpr} {d : Profile n},
      TypeRelated env U registry Δ l r d → TypeRelated env U registry Δ l r (v.mapType d))
    (lowerTerm : ∀ {Δ : List VExpr}, OnCtx Δ (env.IsType U) →
      ∀ {p q : Profile n} (v : ProfileView env U registry Δ p q)
      {l r A : VExpr} {d : Profile n}, p.HasType d →
      Related env U registry Δ l r A p d → Related env U registry Δ l r A q (v.mapType d))
    {Γ : List VExpr} {key : Key n} {input : Profile n}
    {left right : VExpr} {profile : Profile (n + 1)}
    (forward : ProfileView env U registry Γ input key.input)
    (backward : ProfileView env U registry Γ key.input input)
    (h : TypeRelated env U registry Γ left right profile) :
    TypeRelated env U registry Γ left right (inputTypes key input backward.mapType profile) := by
  classical
  intro Δ ρ future atom ha
  rw [inputTypes.rename key input profile ρ backward.mapType
    (backward.future henv future).mapType (backward.mapType_future henv future)] at ha
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp ha
  have hc := h Δ ρ future old hm
  cases old with
  | sort | fn | family | ctor | record | pad => exact hc
  | pi A B domain rows =>
    dsimp only
    split
    · obtain ⟨display⟩ := hc
      exact ⟨display.inputView henv lowerCode lowerTerm (key := key.rename ρ)
        (forward.future henv future) (backward.future henv future) ‹_›⟩
    · exact hc

end Lean4Lean.AnchoredSemantics
