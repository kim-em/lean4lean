import Lean4Lean.Theory.Typing.Strengthening.RegisteredStructureEquations

/-! # Closed structure unfolding excludes singleton-prefix unfolding

A uniform pattern-check certificate is realized at the fresh complete recursor
telescope. The typed structure reconstruction there gives an actual matching
occurrence, so the ordinary iota guard is enabled. Its complementary singleton
prefix guard cannot be enabled at the same head and universes. No caller-side
inhabitant, canonical Eq or strengthening front is needed.
-/
namespace Lean4Lean.VEnv
open _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Equivalent universe syntax cannot enable the singleton guard when the
ordinary iota guard is enabled. The two occurrences may have unrelated contexts. -/
theorem Params.iota_no_delta_levels
    (hp : Pat (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hck : r.2.OK df levels captures)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (H : PrefixUnfold env univs recursorData Γ rc levels' pre rhs) : False := by
  cases H with
  | @intro data program hl _ hname hlarge _ hz _ _ =>
    rcases pat_recursor (recursor := rc) (major := mr) (ctor := cc) (fields := kc) hp with
      ⟨data', _, _, _, hrd, _, hguard⟩ | ⟨_, hq, _⟩
    · rw [hrd] at hl
      cases hl
      obtain ⟨rest, hr⟩ := hguard hlarge
      rw [hr] at hck
      exact hck.1 ((VLevel.inst_congr (by rfl) he).trans hz)
    · subst hq
      rw [recursorData_quot (by assumption)] at hl
      cases hl

end Lean4Lean.VEnv

namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature Params
open PureObservation
variable [Params]

/-- The check carried by a closed structure unfolding is non-vacuous: its
fresh complete telescope contains a typed matching structure reconstruction. -/
theorem check_realized
    {r : (pattern data info).RHS × (pattern data info).Check}
    (hr : RecursorRegistered env data)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = data.uvars)
    (hi : env.projections (family data) info) (hx : info.nindices = 0)
    (hz : Admissible env univs data info levels)
    (hc : CheckFromTyping env univs _ r levels) :
    ∃ Γ captures, r.2.OK (env.IsDefEqU univs Γ) levels captures := by
  obtain ⟨type, htype⟩ := hr.recursorType_exists
  obtain ⟨hshape, hlen⟩ := type_shape (levels := levels) htype
  have ht : HasType env univs [] (.const data.name levels)
      (wrapForalls (domainsOf data levels) (resultOf data levels)) := by
    rw [← hshape]
    exact .const (hr.recursorType htype) hw hl
  obtain ⟨hctx, hopen⟩ := ht.etaOpen_wf henv (by trivial)
  rw [opened data levels hlen] at hopen
  obtain ⟨_, _, params, hm⟩ := hr.major_type henv hctx hopen (by simp)
  have hp : params.length = info.nparams := by
    have H := StructureReplay.family_arity henv hctx hi (hm.isType henv hctx)
    simpa only [hx, Nat.add_zero] using H
  have hexp := (StructureReplay.expansion_typed_iff henv hctx hi hp hx hm).2 hz
  have RE : TypedEtaExpansion _
      (.app (mkApps (.const data.name levels) (vars data.majorOffset 1)) (.bvar 0))
      (.app (mkApps (.const data.name levels) (vars data.majorOffset 1))
        (structExpand (family data) info (familyLevels data levels) params (.bvar 0))) :=
    .app .refl (.structEta hi hp hx hm hexp)
  have htExp := (RE.simAt hctx _ hopen).hasType.2
  have hrec := spineCaptures_match (c := data.name) (n := data.majorOffset)
    (vars data.majorOffset 1) (by simp) levels
  have hctor := spineCaptures_match (c := info.ctorName) (n := info.nparams + info.numFields)
    (params ++ (List.range info.numFields).map (fun i => VExpr.proj (family data) i (.bvar 0)))
    (by simp [hp]) (familyLevels data levels)
  exact ⟨_, _, hc hctx (.app hrec hctor) htExp⟩

/-- An actual singleton prefix cannot overlap a closed structure equation at
any supplied prefix length. Its zero-source guard contradicts the enabled
ordinary iota guard realized in the fresh telescope. -/
theorem Unfolds.no_singleton (H : Unfolds name levels rhs₀)
    (R : PrefixUnfold env univs recursorData Γ name levels args rhs) : False := by
  cases H with
  | intro hr hw hl hi hx hz hp hc =>
    obtain ⟨Δ, captures, hck⟩ := check_realized hr hw hl hi hx hz hc
    exact Params.iota_no_delta hp hck R

/-- Singleton-prefix exclusion is unchanged by equivalent universe instances. -/
theorem Unfolds.no_singleton_levels (H : Unfolds name levels rhs₀)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (R : PrefixUnfold env univs recursorData Γ name levels' args rhs) : False := by
  cases H with
  | intro hr hw hl hi hx hz hp hc =>
    obtain ⟨Δ, captures, hck⟩ := check_realized hr hw hl hi hx hz hc
    exact Params.iota_no_delta_levels hp hck he R

end Lean4Lean.VEnv.Strengthening.ClosedStructure

namespace Lean4Lean.VEnv.Strengthening.RegisteredStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Registry selection preserves the exclusion of all actual singleton prefixes. -/
theorem Unfolds.no_singleton (H : Unfolds name levels value)
    (R : PrefixUnfold env univs recursorData Γ name levels args rhs) : False :=
  H.closedStructure.no_singleton R

/-- Registry-selected unfoldings also exclude prefixes at equivalent universes. -/
theorem Unfolds.no_singleton_levels (H : Unfolds name levels value)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (R : PrefixUnfold env univs recursorData Γ name levels' args rhs) : False :=
  H.closedStructure.no_singleton_levels he R

/-- Quotient-prefix unfolding is also disjoint: its registered primitive head
has no recursor datum in the actual registry. -/
theorem Unfolds.not_quotient (H : Unfolds name levels value)
    (hq : QuotRegistered env) : name ≠ ``Quot.lift := by
  cases H with
  | intro hreg _ _ _ _ _ _ _ =>
    intro he
    rw [he, recursorData_quot hq] at hreg
    cases hreg

end Lean4Lean.VEnv.Strengthening.RegisteredStructure
