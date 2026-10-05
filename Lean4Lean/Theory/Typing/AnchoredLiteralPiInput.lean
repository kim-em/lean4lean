import Lean4Lean.Theory.Typing.AnchoredFunctionDomain
import Lean4Lean.Theory.Typing.AnchoredReanchor

/-! Input extension for a function at an actual literal Pi type. The new
domain support is supplied at that actual domain. This is deliberately not a
generic input-extension view at an arbitrary type expression. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

private theorem typed_subset {old new type : Profile n} (subset : List.Subset old new)
    (typed : new.HasType type) : old.HasType type := by
  cases n with
  | zero => exact fun a ha => typed a (subset ha)
  | succ n => exact ⟨fun a ha => typed.1 a (subset ha), typed.2.1,
      fun a ha => typed.2.2 a (subset ha)⟩

private theorem subset_rename {old new : Profile n} (subset : List.Subset old new) (ρ : Lift) :
    List.Subset (old.rename ρ) (new.rename ρ) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact List.mem_map.mpr ⟨b, subset hb, rfl⟩

private theorem admission_subset {key : Key n} {newInput : Profile n}
    (subset : List.Subset key.input newInput)
    (h : Admitted env U registry Γ (inputKey key newInput) x y) :
    Admitted env U registry Γ key x y := by
  obtain ⟨raw, pair, support, typed, formed, code, first, second⟩ := h
  exact ⟨raw, pair, support, typed_subset subset typed, formed, code,
    Related.of_singletons (fun _ ha => Related.singleton_of_mem first (subset ha)),
    Related.of_singletons (fun _ ha => Related.singleton_of_mem second (subset ha))⟩

private theorem code_union
    (left : TypeRelated env U registry Γ A B p)
    (right : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro a ha
  exact (List.mem_append.mp ha).elim (fun h => left.singleton h) (fun h => right.singleton h)

noncomputable def literalInputTypes (key : Key n) (newInput support : Profile n)
    (profile : Profile (n + 1)) : Profile (n + 1) :=
  profile.map fun
    | .pi A B domain rows => .pi A B (Profile.union domain support)
        (reanchorRows key (inputKey key newInput) rows)
    | atom => atom

theorem literalInputTypes.rename (key : Key n) (newInput support : Profile n)
    (profile : Profile (n + 1)) (ρ : Lift) :
    (literalInputTypes key newInput support profile).rename ρ =
      literalInputTypes (key.rename ρ) (newInput.rename ρ) (support.rename ρ) (profile.rename ρ) := by
  simp only [literalInputTypes, Profile.rename, List.map_map]
  apply List.map_congr_left
  intro atom _
  cases atom <;> simp only [Function.comp_apply, Atom.rename_pi, Atom.rename_sort,
    Atom.rename_fn, Atom.rename_pad, Profile.rename_union, reanchorRows_rename, inputKey, Key.rename]
  rfl

theorem literalInputTypes.wf {key : Key n} {newInput support : Profile n}
    (typed : newInput.HasType support) (formed : support.HasType (.sort true))
    (h : (profile : Profile (n + 1)).WF) : (literalInputTypes key newInput support profile).WF := by
  intro atom hm
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
  have hw := h old ho
  cases old with
  | sort | fn | pad | family | ctor | record => exact hw
  | pi A B domain rows =>
    have domainFormation : Profile.HasType domain (.sort true) := hw.1
    have formation := domainFormation.union formed
    refine ⟨formation, ?_⟩
    intro k result hr
    rcases mem_reanchorRows.mp hr with old | ⟨rfl, old⟩
    · have ht := hw.2 k result old
      exact ⟨Profile.HasType.enlarge ht.1 (Profile.le_union_left _ _) formation.wf_value, ht.2⟩
    · exact ⟨typed.enlarge (Profile.le_union_right _ _) formation.wf_value,
        (hw.2 key result old).2⟩

theorem literalInputTypes.typed {key : Key n} {newInput support : Profile n} {output : Atom n}
    (typed : newInput.HasType support) (formed : support.HasType (.sort true))
    (h : (Profile.fn key output).HasType profile) :
    (Profile.fn (inputKey key newInput) output).HasType
      (literalInputTypes key newInput support profile) := by
  obtain ⟨A, B, domain, rows, result, hm, hw, _, _, hr, ht⟩ := h.fn_inv (List.mem_singleton_self _)
  have newWF := literalInputTypes.wf (key := key) typed formed hw
  change (Profile.pi A B (Profile.union domain support)
    (reanchorRows key (inputKey key newInput) rows)).WF at newWF
  have newTyped := Profile.HasType.fn newWF (reanchorRows.changed hr) ht
  apply newTyped.enlarge ?_ (literalInputTypes.wf typed formed h.wf_type)
  intro atom ha
  cases List.mem_singleton.mp ha
  apply Profile.le_refl (literalInputTypes key newInput support profile)
  exact List.mem_map.mpr ⟨_, hm, rfl⟩

private theorem exposureInsertion {Γ Δ : List VExpr} {e head : VExpr} {ρ : Lift}
    (henv : env.Ordered) (E : Exposure env U registry Γ e Δ ρ head) :
    MixedInsertion env U Γ Δ ρ := E.insertion henv

private theorem literalPi_trace
    (h : CanonicalDataHead.Trace registry (.forallE A B) added result) :
    added = [] ∧ result = .forallE A B := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | next step _ => simp only [CanonicalDataHead.step_pi] at step; contradiction

private theorem literalPi_domain
    (E : Exposure env U registry Γ (.forallE A B) Δ ρ (.forallE C D)) :
    C = A.lift' ρ := by
  have ht := literalPi_trace E.trace
  have hm : E.postMap = ρ := by
    simpa only [ht.1, List.length_nil, Lift.skipN, Lift.refl_comp] using E.map_eq
  have he := E.result_eq
  rw [ht.2, hm] at he
  exact (VExpr.forallE.inj he).1.symm

def PiWitness.literalInput
    {key : Key n} {newInput support domain : Profile n} {rows : List (Key n × Profile n)}
    (henv : env.Ordered) (subset : List.Subset key.input newInput)
    (typed : newInput.HasType support) (formed : support.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ key.domain A support)
    (display : PiWitness env U registry (relations env U registry n)
      Γ (.forallE A B) (.forallE A B) prototypeA prototypeB domain rows) :
    PiWitness env U registry (relations env U registry n)
      Γ (.forallE A B) (.forallE A B) prototypeA prototypeB (Profile.union domain support)
        (reanchorRows key (inputKey key newInput) rows) := by
  have insertion := exposureInsertion henv display.leftExposure
  have hl := literalPi_domain display.leftExposure
  have hr := literalPi_domain display.rightExposure
  have bridge' := insertion.code henv bridge
  have actual := (TypeRelated.symm henv (Profile.rename_wf_iff.mpr typed.wf_type) bridge').left_diagonal
  rw [← hl] at bridge' actual
  have actual' : TypeRelated env U registry display.context display.leftDomain display.rightDomain
      (support.rename display.map) := by simpa only [hr, hl] using actual
  refine { display with domainRelated := ?_, rowDomains := ?_, rowBodies := ?_ }
  · change TypeRelated env U registry display.context display.leftDomain display.rightDomain
      ((domain.union support).rename display.map)
    rw [Profile.rename_union]
    exact code_union display.domainRelated actual'
  · intro k result hm
    rcases mem_reanchorRows.mp hm with old | ⟨rfl, old⟩
    · obtain ⟨selected, hs, hf, hb, raw, code⟩ := display.rowDomains k result old
      exact ⟨selected, hs, hf,
        Profile.le_trans hb (Profile.rename_le_iff.mpr (Profile.le_union_left _ _)), raw, code⟩
    · obtain ⟨_, _, _, _, raw, _⟩ := display.rowDomains key result old
      refine ⟨support.rename display.map, Profile.rename_hasType_iff.mpr typed, ?_,
        Profile.rename_le_iff.mpr (Profile.le_union_right _ _), raw, bridge'⟩
      simpa only [Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := display.map)).mpr formed
  · intro k result hm Δ ρ future x y admitted
    rcases mem_reanchorRows.mp hm with old | ⟨rfl, old⟩
    · exact display.rowBodies k result old Δ ρ future x y admitted
    · exact display.rowBodies key result old Δ ρ future x y
        (admission_subset (subset_rename subset (display.map.comp ρ)) admitted)

theorem TypeRelated.literalInput
    {key : Key n} {newInput support : Profile n} {profile : Profile (n + 1)}
    (henv : env.Ordered) (subset : List.Subset key.input newInput)
    (typed : newInput.HasType support) (formed : support.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ key.domain A support)
    (h : TypeRelated env U registry Γ (.forallE A B) (.forallE A B) profile) :
    TypeRelated env U registry Γ (.forallE A B) (.forallE A B)
      (literalInputTypes key newInput support profile) := by
  intro Δ ρ future atom ha
  rw [literalInputTypes.rename] at ha
  obtain ⟨old, hm, rfl⟩ := List.mem_map.mp ha
  have hc := h Δ ρ future old hm
  cases old with
  | sort | fn | pad | family | ctor | record => exact hc
  | pi pA pB domain rows =>
    obtain ⟨display⟩ := hc
    have hf := (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
    rw [Profile.rename_sort] at hf
    exact ⟨display.literalInput (key := key.rename ρ) henv (subset_rename subset ρ)
      (Profile.rename_hasType_iff.mpr typed) hf (TypeRelated.future henv future bridge)⟩

theorem FunctionBehavior.literalInput
    {key : Key n} {newInput support : Profile n} {output : Atom n} {profile : Profile (n + 1)}
    (henv : env.Ordered) (subset : List.Subset key.input newInput)
    (typed : newInput.HasType support) (formed : support.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ key.domain A support)
    (seed : Admitted env U registry Γ (inputKey key newInput) key.anchor key.anchor)
    (h : FunctionBehavior env U registry (relations env U registry n)
      Γ f g (.forallE A B) key output profile) :
    FunctionBehavior env U registry (relations env U registry n)
      Γ f g (.forallE A B) (inputKey key newInput) output
      (literalInputTypes key newInput support profile) := by
  obtain ⟨_, pA, pB, domain, rows, result, hm, hr, ht, display, behavior⟩ := h
  refine ⟨seed, pA, pB, Profile.union domain support, reanchorRows key (inputKey key newInput) rows,
    result, List.mem_map.mpr ⟨_, hm, rfl⟩, reanchorRows.changed hr, ht,
    display.literalInput henv subset typed formed bridge, ?_⟩
  intro Δ ρ future x y admitted
  exact behavior Δ ρ future x y
    (admission_subset (subset_rename subset (display.map.comp ρ)) admitted)

theorem Related.literalInput
    {key : Key n} {newInput support : Profile n} {output : Atom n} {profile : Profile (n + 1)}
    (henv : env.Ordered) (subset : List.Subset key.input newInput)
    (typed : newInput.HasType support) (formed : support.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ key.domain A support)
    (seed : Admitted env U registry Γ (inputKey key newInput) key.anchor key.anchor)
    (h : Related env U registry Γ f g (.forallE A B) (Profile.fn key output) profile) :
    Related env U registry Γ f g (.forallE A B) (Profile.fn (inputKey key newInput) output)
      (literalInputTypes key newInput support profile) := by
  intro requested hrequested Δ ρ future
  cases List.mem_singleton.mp hrequested
  have hs := h (.fn key output) (List.mem_singleton_self _) Δ ρ future
  rcases hs with hempty | ⟨Ω, τ, insertion, oldTyped, code, values⟩
  · cases hempty
  · have full := future.comp insertion.toFuture henv
    have subset' := subset_rename subset (ρ.comp τ)
    have typed' := (Profile.rename_hasType_iff (ρ := ρ.comp τ)).mpr typed
    have formed' := (Profile.rename_hasType_iff (ρ := ρ.comp τ)).mpr formed
    rw [Profile.rename_sort] at formed'
    have bridge' := TypeRelated.future henv full bridge
    have seed' := Admitted.future henv full seed
    simp only [lift'_comp, Profile.rename_comp] at subset' typed' formed' bridge' seed'
    simp only [Key.rename, inputKey, lift'_comp, Profile.rename_comp] at seed'
    change (Profile.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ)).HasType
      ((profile.rename ρ).rename τ) at oldTyped
    change TypeRelated env U registry Ω
      (.forallE ((A.lift' ρ).lift' τ) ((B.lift' ρ.cons).lift' τ.cons))
      (.forallE ((A.lift' ρ).lift' τ) ((B.lift' ρ.cons).lift' τ.cons))
      ((profile.rename ρ).rename τ) at code
    have newTyped := literalInputTypes.typed typed' formed' oldTyped
    have newCode := TypeRelated.literalInput (key := (key.rename ρ).rename τ)
      henv subset' typed' formed' bridge' code
    have behavior := values (.fn ((key.rename ρ).rename τ) ((output.rename ρ).rename τ))
      (List.mem_singleton_self _)
    have newBehavior := FunctionBehavior.literalInput henv subset' typed' formed' bridge' seed' behavior
    right
    refine ⟨Ω, τ, insertion, ?_, ?_, ?_⟩
    · simpa only [literalInputTypes.rename, Profile.fn, Profile.rename_singleton,
        Atom.rename_fn, inputKey, Key.rename] using newTyped
    · change TypeRelated env U registry Ω
        (((VExpr.forallE A B).lift' ρ).lift' τ) (((VExpr.forallE A B).lift' ρ).lift' τ)
        (((literalInputTypes key newInput support profile).rename ρ).rename τ)
      simpa only [literalInputTypes.rename, lift'] using newCode
    · intro atom ha
      cases List.mem_singleton.mp ha
      simpa only [literalInputTypes.rename, inputKey, Key.rename, Atom.rename_fn,
        TermAtom, lift'] using newBehavior

end Lean4Lean.AnchoredSemantics
