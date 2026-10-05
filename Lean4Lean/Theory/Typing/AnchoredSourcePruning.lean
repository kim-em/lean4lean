import Lean4Lean.Theory.Typing.AnchoredSourceCodeCert
import Lean4Lean.Theory.Typing.AnchoredSourceAvailability

/-! Demand-directed selection of source code observations. Selection of a
computational output never changes an active application's input demand.
The footprint comparison is literal atom inclusion at the original grade;
it is not an intrinsic-profile ordering or a semantic callback. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Finite availability is closed only under literal singleton selection.
This adds no atom, grade, raw key, or type-support demand. -/
def Valuation.AtomClosed (available : Valuation) : Prop :=
  ∀ index need, need ∈ available index → ∀ selected ∈ need.singletons,
    selected ∈ available index

theorem Valuation.atomize_closed (available : Valuation) :
    (Valuation.atomize available).AtomClosed := by
  intro index need member selected hs
  rcases List.mem_append.mp member with original | atomic
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨need, original, hs⟩)
  · obtain ⟨old, ho, hn⟩ := List.mem_flatMap.mp atomic
    obtain ⟨atom, ha, rfl⟩ := List.mem_map.mp hn
    have same : selected = ⟨old.rank, .singleton atom⟩ := List.mem_singleton.mp hs
    subst selected
    exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨old, ho, List.mem_map.mpr ⟨atom, ha, rfl⟩⟩)

theorem Valuation.AtomClosed.mem {available : Valuation}
    (closed : available.AtomClosed) (member : need ∈ Valuation.atomize available index) :
    need ∈ available index := by
  rcases List.mem_append.mp member with original | atomic
  · exact original
  · obtain ⟨old, ho, hs⟩ := List.mem_flatMap.mp atomic
    exact closed index old ho need hs

theorem Footprint.Available.of_atomize {available : Valuation}
    (resources : Footprint.Available required (Valuation.atomize available))
    (closed : available.AtomClosed) : required.Available available :=
  fun index need member => closed.mem (resources index need member)

theorem Footprint.Atomizes.available_closed {available : Valuation}
    (selection : Footprint.Atomizes selected original)
    (resources : Footprint.Available original available)
    (closed : available.AtomClosed) : selected.Available available :=
  (selection.available resources).of_atomize closed

def Footprint.Refines (selected original : Footprint) : Prop :=
  ∀ index rank (profile : Profile rank), (index, ⟨rank, profile⟩) ∈ selected →
    ∃ old : Profile rank, (index, ⟨rank, old⟩) ∈ original ∧
      ∀ atom ∈ profile.atoms, atom ∈ old.atoms

theorem Footprint.Refines.refl (footprint : Footprint) : footprint.Refines footprint := by
  intro index rank profile member
  exact ⟨profile, member, fun _ h => h⟩

theorem Footprint.Refines.trans {first second third : Footprint}
    (left : first.Refines second) (right : second.Refines third) : first.Refines third := by
  intro index rank profile member
  obtain ⟨middle, hm, hpm⟩ := left index rank profile member
  obtain ⟨last, hl, hml⟩ := right index rank middle hm
  exact ⟨last, hl, fun atom ha => hml atom (hpm atom ha)⟩

theorem Footprint.Refines.append_left {selected original : Footprint}
    (h : selected.Refines original) (other : Footprint) :
    selected.Refines (original ++ other) := by
  intro index rank profile member
  obtain ⟨old, hm, sub⟩ := h index rank profile member
  exact ⟨old, List.mem_append_left _ hm, sub⟩

theorem Footprint.Refines.append_right {selected original : Footprint}
    (h : selected.Refines original) (other : Footprint) :
    selected.Refines (other ++ original) := by
  intro index rank profile member
  obtain ⟨old, hm, sub⟩ := h index rank profile member
  exact ⟨old, List.mem_append_right _ hm, sub⟩

theorem Footprint.Atomizes.refl (footprint : Footprint) : footprint.Atomizes footprint := by
  intro index need member
  exact ⟨need, member, .inl rfl⟩

theorem Footprint.Atomizes.refines {selected original : Footprint}
    (h : selected.Atomizes original) : selected.Refines original := by
  intro index rank profile member
  obtain ⟨old, hm, same | selected⟩ := h index ⟨rank, profile⟩ member
  · cases same
    exact ⟨profile, hm, fun _ h => h⟩
  · obtain ⟨atom, ha, he⟩ := List.mem_map.mp selected
    cases he
    exact ⟨old.profile, hm, fun a h => (List.mem_singleton.mp h) ▸ ha⟩

theorem Footprint.Atomizes.append_left {selected original : Footprint}
    (h : selected.Atomizes original) (other : Footprint) :
    selected.Atomizes (original ++ other) := by
  intro index need member
  obtain ⟨old, hm, hs⟩ := h index need member
  exact ⟨old, List.mem_append_left _ hm, hs⟩

theorem Footprint.Atomizes.append_right {selected original : Footprint}
    (h : selected.Atomizes original) (other : Footprint) :
    selected.Atomizes (other ++ original) := by
  intro index need member
  obtain ⟨old, hm, hs⟩ := h index need member
  exact ⟨old, List.mem_append_right _ hm, hs⟩

structure Obs.AtomSelection
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {sourceFootprint : Footprint}
    (_source : Obs env U registry Γ locals σ expression profile sourceFootprint)
    (atom : Atom n) where
  footprint : Footprint
  observation : Obs env U registry Γ locals σ expression (.singleton atom) footprint
  atomizes : footprint.Atomizes sourceFootprint

theorem Obs.AtomSelection.refines
    {sourceFootprint : Footprint}
    {source : Obs env U registry Γ locals σ expression profile sourceFootprint}
    (selected : source.AtomSelection atom) :
    selected.footprint.Refines sourceFootprint := selected.atomizes.refines

/-- Select one value atom. In the application case the entire original
function and argument observations are retained. -/
theorem Obs.atom
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (source : Obs env U registry Γ locals σ expression profile footprint)
    {atom : Atom n} (member : atom ∈ profile.atoms) : Nonempty (source.AtomSelection atom) := by
  match n, atom, profile, source with
  | _, a, _, .var locals σ index demand =>
    refine ⟨⟨[(index, ⟨_, .singleton a⟩)], .var locals σ index _, ?_⟩⟩
    intro other need hm
    cases List.mem_singleton.mp hm
    exact ⟨⟨_, demand⟩, List.mem_singleton_self _, .inr
      (List.mem_map.mpr ⟨a, member, rfl⟩)⟩
  | _, _, _, .empty => cases member
  | 0, _, _, .sort relevant =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .sort relevant, .refl _⟩⟩
  | _ + 1, _, _, .sort relevant =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .sort relevant, .refl _⟩⟩
  | _, _, _, .app fn arg admitted =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .app fn arg admitted, .refl _⟩⟩
  | _, _, _, .lam domain guard body normal =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .lam domain guard body normal, .refl _⟩⟩
  | _, _, _, .pi domain guard bodies =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .pi domain guard bodies, .refl _⟩⟩
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with member | member
    · obtain ⟨selected⟩ := left.atom member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_left _⟩⟩
    · obtain ⟨selected⟩ := right.atom member
      exact ⟨⟨selected.footprint, selected.observation, selected.atomizes.append_right _⟩⟩
  | _, _, _, .view body v =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .view body v, .refl _⟩⟩
  | _, _, _, .pad body =>
    obtain ⟨lower, hl, rfl⟩ := List.mem_map.mp member
    obtain ⟨selected⟩ := body.atom hl
    exact ⟨⟨selected.footprint, .pad selected.observation, selected.atomizes⟩⟩
  | _, _, _, .unpad body =>
    obtain ⟨selected⟩ := body.atom (List.mem_map_of_mem (f := AtomData.pad) member)
    exact ⟨⟨selected.footprint, .unpad selected.observation, selected.atomizes⟩⟩
  | _, _, _, .rowShift body =>
    cases List.mem_singleton.mp member
    exact ⟨⟨_, .rowShift body, .refl _⟩⟩
termination_by sizeOf source
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource

namespace Lean4Lean.AnchoredSemantics
open VExpr AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Every computed atomic type map has an original outer-atom occurrence.
Tests inside a Pi atom do not inspect other outer atoms. -/
theorem AtomView.mapType_lists
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {a b : Atom n} (view : AtomView env U registry Γ a b) :
    view.mapType [] = [] ∧ ∀ left right : Profile n,
      view.mapType (left.union right) = (view.mapType left).union (view.mapType right) := by
  match n, a, b, view with
  | _, _, _, .refl _ => exact ⟨rfl, fun _ _ => rfl⟩
  | _ + 1, _, _, .reanchor _ =>
    exact ⟨rfl, fun _ _ => List.map_append⟩
  | _ + 1, _, _, .domainRekey _ _ _ _ =>
    exact ⟨rfl, fun _ _ => List.map_append⟩
  | _ + 1, _, _, .input _ _ =>
    exact ⟨rfl, fun _ _ => List.map_append⟩
  | _ + 2, _, _, .commutePadFn _ _ =>
    refine ⟨rfl, ?_⟩
    intro left right
    simp only [AtomView.mapType, Profile.down, Profile.rankShift, Profile.union, Profile.mk, Profile.atoms, List.flatMap_append,
      List.map_append]
  | _ + 2, _, _, .uncommutePadFn _ _ =>
    refine ⟨rfl, ?_⟩
    intro left right
    simp only [AtomView.mapType, Profile.unshift, Profile.pad, Profile.union, Profile.mk, Profile.atoms, List.flatMap_append,
      List.map_append]
  | _ + 1, _, _, .fn _ _ =>
    exact ⟨rfl, fun _ _ => List.map_append⟩
  | _ + 1, _, _, .pad child =>
    obtain ⟨empty, append⟩ := child.mapType_lists
    constructor
    · change (child.mapType []).pad = []
      rw [empty]; rfl
    · intro left right
      change (child.mapType (left.union right).down).pad = _
      rw [show (left.union right).down = left.down.union right.down from List.flatMap_append,
        append]
      exact List.map_append
  | _, _, _, .trans first second =>
    obtain ⟨ef, af⟩ := first.mapType_lists
    obtain ⟨es, ass⟩ := second.mapType_lists
    constructor
    · change second.mapType (first.mapType []) = []
      rw [ef, es]
    · intro left right
      change second.mapType (first.mapType (left.union right)) = _
      rw [af, ass]
      rfl
termination_by (n, sizeOf view)
decreasing_by all_goals simp_wf; omega

theorem AtomView.mapType_mem
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {a b : Atom n} (view : AtomView env U registry Γ a b)
    {profile : Profile n} {output : Atom n} :
    output ∈ (view.mapType profile).atoms ↔
      ∃ original ∈ profile.atoms, output ∈ (view.mapType (.singleton original)).atoms := by
  induction profile with
  | nil => simp [view.mapType_lists.1, Profile.atoms]
  | cons head tail ih =>
    rw [show head :: tail = (Profile.singleton head).union tail from rfl, view.mapType_lists.2]
    simp only [Profile.atoms, Profile.union, Profile.singleton, Profile.mk, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, exists_eq_or_imp]
    exact or_congr Iff.rfl ih

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- One surviving code atom and its actual source observations. A transform
retains only a selected output occurrence of one input atom. In particular,
there is no `down` constructor from a Pi atom, whose down image is empty. -/
inductive CodeAtomCert (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (expression : VExpr) :
    {n : Nat} → Atom n → Footprint → Type where
  | seed {atom : Atom n}
      (observation : Obs env U registry Γ locals σ expression (.singleton atom) footprint)
      (formed : (Profile.singleton atom).HasType (.sort true)) :
      CodeAtomCert env U registry Γ locals σ expression atom footprint
  | pad {atom : Atom n}
      (source : CodeAtomCert env U registry Γ locals σ expression atom footprint) :
      CodeAtomCert env U registry Γ locals σ expression (n := n + 1) (.pad atom) footprint
  | unpad {atom : Atom n}
      (source : CodeAtomCert env U registry Γ locals σ expression (n := n + 1) (.pad atom) footprint) :
      CodeAtomCert env U registry Γ locals σ expression atom footprint
  | down {input : Atom (n + 1)} {output : Atom n}
      (source : CodeAtomCert env U registry Γ locals σ expression input footprint)
      (selected : output ∈ input.down.atoms) :
      CodeAtomCert env U registry Γ locals σ expression output footprint
  | map {a b input output : Atom n} (view : AtomView env U registry Γ a b)
      (source : CodeAtomCert env U registry Γ locals σ expression input footprint)
      (selected : output ∈ (view.mapType (.singleton input)).atoms) :
      CodeAtomCert env U registry Γ locals σ expression output footprint

/-- An empty code demand has no retained provenance. Nonempty demands are
assembled from independently selected, surviving atomic certificates. -/
inductive PrunedCodeCert (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (expression : VExpr) :
    {n : Nat} → Profile n → Footprint → Type where
  | nil : PrunedCodeCert env U registry Γ locals σ expression (n := n) [] []
  | cons {atom : Atom n} {profile : Profile n}
      (head : CodeAtomCert env U registry Γ locals σ expression atom headFootprint)
      (tail : PrunedCodeCert env U registry Γ locals σ expression profile tailFootprint) :
      PrunedCodeCert env U registry Γ locals σ expression (atom :: profile)
        (headFootprint ++ tailFootprint)

theorem CodeAtomCert.formed {atom : Atom n}
    (cert : CodeAtomCert env U registry Γ locals σ expression (n := n) atom footprint) :
    (Profile.singleton atom).HasType (.sort true) := by
  induction cert with
  | seed _ formed => exact formed
  | pad _ ih => exact ih.pad_sort
  | unpad _ ih =>
    rw [← Profile.pad_singleton] at ih
    simpa only [Profile.down_sort] using ih.pad_inv
  | down _ selected ih =>
    have h := ih.down
    rw [Profile.down_sort, Profile.down_singleton] at h
    exact h.singleton_of_mem selected
  | map v _ selected ih => exact (v.mapType_sort ih).singleton_of_mem selected

theorem PrunedCodeCert.formed {profile : Profile n}
    (cert : PrunedCodeCert env U registry Γ locals σ expression profile footprint) :
    profile.HasType (.sort true) := by
  induction cert with
  | nil => exact Profile.HasType.empty (Profile.WF.sort true)
  | cons head _ ih => exact head.formed.union ih

structure CodeCert.AtomSelection
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {sourceFootprint : Footprint}
    (_source : CodeCert env U registry Γ locals σ expression profile sourceFootprint)
    (atom : Atom n) where
  footprint : Footprint
  certificate : CodeAtomCert env U registry Γ locals σ expression atom footprint
  atomizes : Footprint.Atomizes footprint sourceFootprint

/-- Follow a demanded output occurrence back through the actual certificate.
No branch producing only erased atoms contributes a source requirement. -/
theorem CodeCert.atom
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (source : CodeCert env U registry Γ locals σ expression profile footprint)
    {atom : Atom n} (member : atom ∈ profile.atoms) : Nonempty (source.AtomSelection atom) := by
  match n, atom, profile, source with
  | _, _, _, .seed observation formed =>
    obtain ⟨selected⟩ := observation.atom member
    exact ⟨⟨selected.footprint, .seed selected.observation (formed.singleton_of_mem member),
      selected.atomizes⟩⟩
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with member | member
    · obtain ⟨selected⟩ := left.atom member
      exact ⟨⟨selected.footprint, selected.certificate, selected.atomizes.append_left _⟩⟩
    · obtain ⟨selected⟩ := right.atom member
      exact ⟨⟨selected.footprint, selected.certificate, selected.atomizes.append_right _⟩⟩
  | _, _, _, .pad body =>
    obtain ⟨lower, hl, rfl⟩ := List.mem_map.mp member
    obtain ⟨selected⟩ := body.atom hl
    exact ⟨⟨selected.footprint, .pad selected.certificate, selected.atomizes⟩⟩
  | _, _, _, .unpad body =>
    obtain ⟨selected⟩ := body.atom (List.mem_map_of_mem (f := AtomData.pad) member)
    exact ⟨⟨selected.footprint, .unpad selected.certificate, selected.atomizes⟩⟩
  | _, _, _, .down body =>
    obtain ⟨higher, hh, hd⟩ := Profile.mem_down_iff.mp member
    obtain ⟨selected⟩ := body.atom hh
    exact ⟨⟨selected.footprint, .down selected.certificate hd, selected.atomizes⟩⟩
  | _, _, _, .map v body =>
    obtain ⟨old, ho, hm⟩ := v.mapType_mem.mp member
    obtain ⟨selected⟩ := body.atom ho
    exact ⟨⟨selected.footprint, .map v selected.certificate hm, selected.atomizes⟩⟩
  | _, _, _, .select body selected =>
    cases List.mem_singleton.mp member
    obtain ⟨chosen⟩ := body.atom selected
    exact ⟨⟨chosen.footprint, chosen.certificate, chosen.atomizes⟩⟩
termination_by sizeOf source
decreasing_by all_goals simp_wf; omega

theorem Footprint.Atomizes.append {left right original : Footprint}
    (hl : Footprint.Atomizes left original) (hr : Footprint.Atomizes right original) :
    Footprint.Atomizes (left ++ right) original := by
  intro index need hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hl index need hm
  · exact hr index need hm

structure CodeCert.Pruning
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {sourceFootprint : Footprint}
    (_source : CodeCert env U registry Γ locals σ expression profile sourceFootprint) where
  footprint : Footprint
  certificate : PrunedCodeCert env U registry Γ locals σ expression profile footprint
  atomizes : Footprint.Atomizes footprint sourceFootprint

/-- Produce the full finite pruned certificate, using original occurrences
for every surviving atom. The zero-demand case is exactly the empty tree. -/
theorem CodeCert.prune
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (source : CodeCert env U registry Γ locals σ expression profile footprint) :
    Nonempty source.Pruning := by
  suffices ∀ selected : Profile n, (∀ atom ∈ selected.atoms, atom ∈ profile.atoms) →
      ∃ required, Nonempty (PrunedCodeCert env U registry Γ locals σ expression selected required) ∧
        Footprint.Atomizes required footprint by
    obtain ⟨required, ⟨cert⟩, atomizes⟩ := this profile (fun _ h => h)
    exact ⟨⟨required, cert, atomizes⟩⟩
  intro selected included
  induction selected with
  | nil => exact ⟨[], ⟨.nil⟩, fun _ _ h => nomatch h⟩
  | cons head tail ih =>
    obtain ⟨selected⟩ := source.atom (included head List.mem_cons_self)
    obtain ⟨tailFootprint, ⟨tailCert⟩, tailAtomizes⟩ := ih
      (fun atom h => included atom (List.mem_cons_of_mem _ h))
    exact ⟨selected.footprint ++ tailFootprint, ⟨.cons selected.certificate tailCert⟩,
      selected.atomizes.append tailAtomizes⟩

/-- The interpretation premise ranges only over computational observations
actually retained by the atomic certificate. -/
inductive CodeAtomCert.Leaf
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr} :
    {n : Nat} → {atom : Atom n} → {footprint : Footprint} →
      CodeAtomCert env U registry Γ locals σ expression atom footprint →
    {m : Nat} → {input : Atom m} → {required : Footprint} →
      Obs env U registry Γ locals σ expression (.singleton input) required → Prop where
  | seed {observation : Obs env U registry Γ locals σ expression (.singleton input) required}
      {formed : (Profile.singleton input).HasType (.sort true)} :
      Leaf (.seed observation formed) observation
  | pad (leaf : Leaf source observation) : Leaf (.pad source) observation
  | unpad (leaf : Leaf source observation) : Leaf (.unpad source) observation
  | down (leaf : Leaf source observation) : Leaf (.down source selected) observation
  | map (leaf : Leaf source observation) : Leaf (.map view source selected) observation

theorem CodeAtomCert.interpret
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression left right : VExpr}
    {atom : Atom n} {footprint : Footprint}
    (cert : CodeAtomCert env U registry Γ locals σ expression (n := n) atom footprint)
    (seeds : ∀ {m : Nat} {input : Atom m} {required : Footprint}
      (observation : Obs env U registry Γ locals σ expression (.singleton input) required),
      cert.Leaf observation → TypeRelated env U registry Γ left right (.singleton input)) :
    TypeRelated env U registry Γ left right (.singleton atom) := by
  induction cert with
  | seed observation _ => exact seeds observation .seed
  | pad source ih =>
    exact (ih fun observation leaf => seeds observation (.pad leaf)).pad henv
  | unpad source ih =>
    exact (TypeRelated.pad_iff henv).mp
      (ih fun observation leaf => seeds observation (.unpad leaf))
  | down source selected ih =>
    have ih := (ih fun observation leaf =>
      seeds observation (.down leaf)).down henv
    rw [Profile.down_singleton] at ih
    exact ih.singleton selected
  | map v source selected ih =>
    have ih := ih fun observation leaf => seeds observation (.map leaf)
    exact (v.codeMap henv hscoped ih).singleton selected

inductive PrunedCodeCert.Leaf
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr} :
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
      PrunedCodeCert env U registry Γ locals σ expression profile footprint →
    {m : Nat} → {input : Atom m} → {required : Footprint} →
      Obs env U registry Γ locals σ expression (.singleton input) required → Prop where
  | head (leaf : CodeAtomCert.Leaf head observation) : Leaf (.cons head tail) observation
  | tail (leaf : Leaf tail observation) : Leaf (.cons head tail) observation

theorem PrunedCodeCert.interpret
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression left right : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (cert : PrunedCodeCert env U registry Γ locals σ expression profile footprint)
    (seeds : ∀ {m : Nat} {input : Atom m} {required : Footprint}
      (observation : Obs env U registry Γ locals σ expression (.singleton input) required),
      cert.Leaf observation → TypeRelated env U registry Γ left right (.singleton input)) :
    TypeRelated env U registry Γ left right profile := by
  induction cert with
  | nil => exact TypeRelated.of_singletons fun _ h => nomatch h
  | cons head tail ih =>
    have hh := head.interpret henv hscoped fun observation leaf => seeds observation (.head leaf)
    have ht := ih fun observation leaf => seeds observation (.tail leaf)
    apply TypeRelated.of_singletons
    intro atom member
    rcases List.mem_cons.mp member with same | member
    · subst atom; exact hh
    · exact ht.singleton member

/-- Compile only recursively retained atomic provenance. Selection after a
map or `down` keeps this exact footprint and cannot restore an erased branch. -/
noncomputable def CodeAtomCert.toCodeCert
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {atom : Atom n} {footprint : Footprint}
    (cert : CodeAtomCert env U registry Γ locals σ expression (n := n) atom footprint) :
    CodeCert env U registry Γ locals σ expression (.singleton atom) footprint := by
  induction cert with
  | seed observation formed => exact .seed observation formed
  | pad _ ih => exact .pad ih
  | unpad _ ih => exact .unpad ih
  | down _ selected ih =>
    apply CodeCert.select (.down ih)
    simpa only [Profile.down_singleton] using selected
  | map v _ selected ih => exact .select (.map v ih) selected

/-- The empty case compiles to a genuinely empty source seed. -/
noncomputable def PrunedCodeCert.toCodeCert
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (cert : PrunedCodeCert env U registry Γ locals σ expression profile footprint) :
    CodeCert env U registry Γ locals σ expression profile footprint := by
  induction cert with
  | nil => exact .seed .empty (Profile.HasType.empty (Profile.WF.sort true))
  | cons head _ ih => exact .union head.toCodeCert ih

/-- A ready-to-use ordinary code certificate with only selected provenance.
Existing binder and original-type-child interfaces therefore remain valid. -/
theorem CodeCert.prune_code
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {locals : List Nat} {σ : Subst} {expression : VExpr}
    {profile : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry Γ locals σ expression profile footprint) :
    ∃ selected, Nonempty (CodeCert env U registry Γ locals σ expression profile selected) ∧
      Footprint.Atomizes selected footprint := by
  obtain ⟨pruned⟩ := cert.prune
  exact ⟨pruned.footprint, ⟨pruned.certificate.toCodeCert⟩, pruned.atomizes⟩

end Lean4Lean.AnchoredSource
