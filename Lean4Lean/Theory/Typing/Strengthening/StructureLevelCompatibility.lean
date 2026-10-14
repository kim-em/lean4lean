import Lean4Lean.Theory.Typing.Strengthening.DeclarationLevelCompatibility
import Lean4Lean.Theory.Typing.Strengthening.StructurePrefixDisjoint

/-! # Universe compatibility of selected structure unfoldings

Equivalent universe arguments preserve projection admissibility, the enabled
concrete pattern guard, and the generated closed program up to level equivalence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation
variable [Params]

private theorem levels_context (henv : env.WF)
    (he : List.Forall₂ (EqUpToLevels U) Γ Γ') (hc : OnCtx Γ (env.IsType U)) :
    IsDefEqCtx env U [] Γ Γ' := by
  induction he with
  | nil => exact .zero
  | cons hd hs ih =>
    obtain ⟨u, ht⟩ := hc.2
    exact .succ (ih hc.1) (ht.eqUpToLevels henv.orderedStrong hc.1 hd)

/-- Closed proof-field certificates survive equivalent universe instances,
including the conversion of every preceding field domain in their contexts. -/
theorem StructureReplay.ProofFields.congr_levels
    (hi : env.projections family info)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = info.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    (H : StructureReplay.ProofFields env univs info ls) :
    StructureReplay.ProofFields env univs info ls' := by
  intro doms result hshape hlen j hj hp
  have hc := HasType.const (Γ := []) (henv.ordered.projectionConstructor hi) hw hl
  rw [hshape, instL_wrapForalls] at hc
  have hctx := (IsType.wrapForalls_inv henv (by trivial) (hc.isType henv (by trivial))).1
  simp only [List.append_nil] at hctx
  have hprefix : OnCtx ((doms.map (instL ls)).take j).reverse (env.IsType univs) := by
    have heq : (doms.map (instL ls)).reverse =
        ((doms.map (instL ls)).drop j).reverse ++ ((doms.map (instL ls)).take j).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [heq] at hctx
    exact hctx.of_append
  have hds : List.Forall₂ (EqUpToLevels univs) (doms.map (instL ls)) (doms.map (instL ls')) :=
    by
      apply List.forall₂_of_getElem (by simp)
      intro i hi hi'
      simp only [List.getElem_map]
      exact .instL_expr _ hw hw' he
  have hW := levels_context henv ((List.Forall₂.reverse.mpr (List.forall₂_take hds j))) hprefix
  have hf := (H doms result hshape hlen j hj hp).eqUpToLevels henv.orderedStrong hprefix
    (EqUpToLevels.instL_expr doms[j] hw hw' he)
  exact hf.hasType.2.defeqDFC henv hW

/-- Equivalent levels preserve the enabling guard of every concrete pattern.
Parameter alignment checks are reconstructed from the new occurrence's typing. -/
theorem concrete_check_levels {p : Pattern} {r : p.RHS × p.Check}
    {relation : VExpr → VExpr → Prop} {captures : p.Path → VExpr}
    (hp : ConcretePattern env p r) (he : List.Forall₂ (· ≈ ·) ls ls')
    (H : r.2.OK relation ls captures) : CheckFromTyping env univs p r ls' := by
  intro Γ e T captures' hΓ hm ht
  rcases hp with hd | hq | hi
  · cases hd; trivial
  · cases hq
    simp only [quotPatternCheck, Pattern.Check.OK] at H
    exact quot_check_of_typed henv hΓ ‹QuotRegistered env› hm ht
      (fun hz => H.1 ((VLevel.inst_congr rfl he).trans hz))
  · cases hi with | intro _ _ =>
    unfold InductiveSignature.RecursorData.guard
    unfold InductiveSignature.RecursorData.guard at H
    split at H
    · rename_i h
      simp only [h, if_true, Pattern.Check.OK]
      exact ⟨fun hz => H.1 ((VLevel.inst_congr rfl he).trans hz), trivial⟩
    · rename_i h
      simp [h, Pattern.Check.OK]

namespace ClosedStructure

private theorem family_levels_wf (hr : RecursorRegistered env data)
    (hw : ∀ l ∈ levels, l.WF univs) (hl : levels.length = data.uvars)
    (hi : env.projections (family data) info) :
    (∀ l ∈ familyLevels data levels, l.WF univs) ∧
      (familyLevels data levels).length = info.uvars := by
  obtain ⟨type, htype⟩ := hr.recursorType_exists
  obtain ⟨hshape, hlen⟩ := type_shape (levels := levels) htype
  have ht : HasType env univs [] (.const data.name levels)
      (wrapForalls (domainsOf data levels) (resultOf data levels)) := by
    rw [← hshape]
    exact .const (hr.recursorType htype) hw hl
  obtain ⟨hctx, hopen⟩ := ht.etaOpen_wf henv (by trivial)
  rw [opened data levels hlen] at hopen
  obtain ⟨_, _, params, hm⟩ := hr.major_type henv hctx hopen (by simp)
  obtain ⟨_, hfamily⟩ := hm.isType henv hctx
  obtain ⟨_, hc, hwf, hlf⟩ := (VExpr.WF.of_mkApps henv hctx ⟨_, hfamily⟩).const_inv henv hctx
  obtain ⟨decl, fam, ctor, _, _, hname, _, huvars, _, _, _, _, _, hlookup,
    hwctor, _, Hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hsh, _, _, hhead, _⟩ := Hraw.forallArity
  rw [hsh] at hwctor
  obtain ⟨hdctx, _, hres⟩ := IsType.wrapForalls_inv henv (by trivial) hwctor
  have he : result = mkApps (.const fam.name (VLevel.params decl.uvars)) result.getAppFnArgs.2 := by
    rw [← hhead]
    exact (mkApps_getAppFnArgs_eq result).symm
  rw [he] at hres
  obtain ⟨_, hci, _, hcount⟩ := (VExpr.WF.of_mkApps henv hdctx ⟨_, hres⟩).const_inv henv hdctx
  rw [hname, hlookup] at hci
  cases hci
  change env.constants (family data) = _ at hc
  rw [hlookup] at hc
  cases hc
  exact ⟨hwf, hlf.trans ((by simpa using hcount.symm) : fam.uvars = decl.uvars) |>.trans huvars⟩

/-- Equivalent recursor universes preserve both sources of structure projection
admissibility: never-zero result universes and closed proof-field telescopes. -/
theorem Admissible.congr_levels (hr : RecursorRegistered env data)
    (hi : env.projections (family data) info)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (hl : ls.length = data.uvars) (he : List.Forall₂ (· ≈ ·) ls ls')
    (H : Admissible env univs data info ls) : Admissible env univs data info ls' := by
  have hf : List.Forall₂ (· ≈ ·) (familyLevels data ls) (familyLevels data ls') := by
    apply List.forall₂_of_getElem (by simp [familyLevels])
    intro i hi hi'
    simp only [familyLevels, List.getElem_map]
    exact VLevel.inst_congr rfl he
  rcases H with hz | hp
  · exact .inl (hz.of_equiv (VLevel.inst_congr rfl hf))
  · have hlf := family_levels_wf hr hw hl hi
    have hrf := family_levels_wf hr hw' (he.length_eq.symm.trans hl) hi
    exact .inr (hp.congr_levels hi hlf.1 hrf.1 hlf.2 hf)

private theorem rhs_level_equiv {p : Pattern} (r : p.RHS)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (he : List.Forall₂ (· ≈ ·) ls ls') (captures : p.Path → VExpr) :
    LEquiv univs (r.apply ls captures) (r.apply ls' captures) := by
  induction r with
  | fixed e _ => exact .instL_expr e hw hw' he
  | var _ => exact .refl
  | app _ _ ihf iha => exact .app ihf iha

/-- The selected closed projection program changes only universe annotations
when its recursor levels change by universe equivalence. -/
theorem value_level_equiv (hr : RecursorRegistered env data)
    (r : (pattern data info).RHS)
    (hw : ∀ l ∈ ls, l.WF univs) (hw' : ∀ l ∈ ls', l.WF univs)
    (he : List.Forall₂ (· ≈ ·) ls ls') :
    LEquiv univs (value data info ls r (domainsOf data ls))
      (value data info ls' r (domainsOf data ls')) := by
  obtain ⟨type, htype⟩ := hr.recursorType_exists
  obtain ⟨domains, result, _, hshape, hlen, hmajor⟩ := RecursorData.recursorType_major htype
  have hd (levels : List VLevel) : domainsOf data levels = domains.map (·.instL levels) := by
    have hs : (type.instL levels).takeForalls (data.majorOffset + 1) =
        some (domains.map (·.instL levels), result.instL levels) := by
      rw [hshape, instL_wrapForalls, ← hlen, ← List.length_map (f := (·.instL levels))]
      exact takeForalls_wrapForalls _ _
    simp only [domainsOf, telescopeOf, htype, Option.getD_some, hs]
  have hb : LEquiv univs (body data info ls r) (body data info ls' r) :=
    rhs_level_equiv r hw hw' he _
  simp only [value, hd]
  clear hd hlen hshape hmajor
  induction domains with
  | nil => exact hb
  | cons d ds ih => exact .lam (.instL_expr d hw hw' he) ih

end ClosedStructure
namespace RegisteredStructure

/-- A selected structure unfolding remains enabled at equivalent universes.
Its generated result is structurally level-equivalent, with no equation closure. -/
theorem Unfolds.congr_levels
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : Unfolds name ls rhs) (hw' : ∀ l ∈ ls', l.WF univs)
    (he : List.Forall₂ (· ≈ ·) ls ls') :
    ∃ rhs', Unfolds name ls' rhs' ∧ LEquiv univs rhs rhs' := by
  cases H with
  | intro hreg hw hl hi hx hz hp hc =>
    obtain ⟨hr, _⟩ := recursorData_registered hreg
    obtain ⟨Γ, captures, Hcheck⟩ := ClosedStructure.check_realized hr hw hl hi hx hz hc
    refine ⟨_, .intro hreg hw' (he.length_eq.symm.trans hl) hi hx
      (hz.congr_levels hr hi hw hw' hl he)
      hp (concrete_check_levels (hcon hp) he Hcheck), ?_⟩
    exact ClosedStructure.value_level_equiv hr _ hw hw' he

/-- Stored definitions and registry-selected closed structure programs form a
universe-compatible collection while retaining their fixed-universe determinism. -/
theorem definitions_ofEnv_levelCompatible
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    (definitions (Definitions.ofEnv env univs henv)).LevelCompatible univs := by
  intro name ls ls' rhs H hw he
  rcases H with HD | HS
  · obtain ⟨rhs', H', HE⟩ := Definitions.ofEnv_levelCompatible henv HD hw he
    exact ⟨rhs', .inl H', HE⟩
  · obtain ⟨rhs', H', HE⟩ := HS.congr_levels hcon hw he
    exact ⟨rhs', .inr H', HE⟩

end RegisteredStructure
end Lean4Lean.VEnv.Strengthening
