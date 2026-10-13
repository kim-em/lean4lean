import Lean4Lean.Theory.Typing.Strengthening.StructureFamilyArity
import Lean4Lean.Theory.Typing.Strengthening.StructureIotaReplay
import Lean4Lean.Theory.Typing.Strengthening.ConstructorObservation
import Lean4Lean.Theory.Typing.Confluence.SingletonCoverage

/-! # Closed projection unfoldings for registered structure recursors

At a never-zero source universe, an unindexed structure recursor is equal to a
closed lambda term computing its rule on projections of the generic major.
The constructor's parameter captures are closed dummy terms: the checked rule
ignores them. Every occurrence can therefore replay this equation by weakening.
-/
namespace Lean4Lean.VEnv.Strengthening.ClosedStructure
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
open PureObservation (CheckFromTyping)

/-- Number a constant-spine capture in application order. -/
def spineIndex {c : Name} : {n : Nat} → ((Pattern.const c).varN n).Path → Fin n
  | 0, p => nomatch p
  | n+1, none => ⟨n, by omega⟩
  | n+1, some p => ⟨(spineIndex p).val, Nat.lt_succ_of_lt (spineIndex p).isLt⟩

/-- Numbered paths recover their original argument position. -/
theorem spineIndex_path {c : Name} : ∀ n i (hi : i < n),
    (spineIndex (c := c) (Pattern.varN_pathOf n i hi)).val = i
  | n+1, i, hi => by
    by_cases h : i = n
    · subst i; simp [Pattern.varN_pathOf, spineIndex]
    · simp [Pattern.varN_pathOf, h, spineIndex, spineIndex_path n i (by omega)]

/-- Deterministic captures of a fully supplied constant spine. -/
def spineCaptures {c : Name} {n : Nat} (args : List VExpr) (hlen : args.length = n) :
    ((Pattern.const c).varN n).Path → VExpr :=
  fun p => args[(spineIndex p).val]'(hlen ▸ (spineIndex p).isLt)

/-- These deterministic captures match at every choice of constructor levels. -/
theorem spineCaptures_match {c : Name} {n : Nat} (args : List VExpr) (hlen : args.length = n)
    (levels : List VLevel) :
    ((Pattern.const c).varN n).Matches (mkApps (.const c levels) args) levels (spineCaptures args hlen) := by
  obtain ⟨captures, hm, hg⟩ := Pattern.matches_varN_const (c := c) (ls := levels) n args hlen
  have he : captures = spineCaptures args hlen := by
    funext p
    obtain ⟨i, hi, rfl⟩ := ConstructorObservation.spine_path_surj n p
    simp only [spineCaptures, spineIndex_path]
    exact hg i hi
  rwa [he] at hm

/-- The registered recursor's restored major-family name. -/
def family (data : RecursorData) : Name :=
  data.schema.restoration.headName data.schema.signature.families[data.owner].name

/-- Its universe instance at this recursor occurrence. -/
def familyLevels (data : RecursorData) (levels : List VLevel) : List VLevel :=
  (data.schema.restoration.headLevels data.schema.signature.families[data.owner].name
    data.levels).map (·.inst levels)

abbrev pattern (data : RecursorData) (info : VProjectionInfo) : Pattern :=
  .app ((Pattern.const data.name).varN data.majorOffset)
    ((Pattern.const info.ctorName).varN (info.nparams + info.numFields))

/-- The rule is run under the fully opened recursor telescope. Parameter holes
receive closed dummies; field holes receive projections of the innermost major. -/
def body (data : RecursorData) (info : VProjectionInfo) (levels : List VLevel)
    (rhs : (pattern data info).RHS) : VExpr :=
  Pattern.RHS.apply (p := pattern data info) levels (Sum.elim
    (spineCaptures (c := data.name) (n := data.majorOffset) (vars data.majorOffset 1) (by simp))
    (spineCaptures (c := info.ctorName) (n := info.nparams + info.numFields)
      (List.replicate info.nparams (.sort .zero) ++
        (List.range info.numFields).map (fun i => .proj (family data) i (.bvar 0))) (by simp))) rhs

def value (data : RecursorData) (info : VProjectionInfo) (levels : List VLevel)
    (rhs : (pattern data info).RHS) (domains : List VExpr) : VExpr :=
  wrapLams domains (body data info levels rhs)

/-- Opening through the major places that major at bvar zero. -/
theorem opened {domains : List VExpr} (data : RecursorData) (levels : List VLevel)
    (hlen : domains.length = data.majorOffset + 1) :
    etaOpen domains.length (.const data.name levels) =
      .app (mkApps (.const data.name levels) (vars data.majorOffset 1)) (.bvar 0) := by
  rw [hlen, etaOpen_spine, vars_add]
  simp [liftN, vars, mkApps]

/-- Deterministic selection of the recursor telescope through its major. -/
def telescopeOf (data : RecursorData) (levels : List VLevel) : List VExpr × VExpr :=
  (((data.recursorType.getD (.sort .zero)).instL levels).takeForalls (data.majorOffset + 1)).getD
    ([], .sort .zero)

def domainsOf (data : RecursorData) (levels : List VLevel) : List VExpr :=
  (telescopeOf data levels).1

def resultOf (data : RecursorData) (levels : List VLevel) : VExpr :=
  (telescopeOf data levels).2

/-- Recursor generation always exposes exactly the telescope selected above. -/
theorem type_shape (htype : data.recursorType = some type) :
    type.instL levels = wrapForalls (domainsOf data levels) (resultOf data levels) ∧
      (domainsOf data levels).length = data.majorOffset + 1 := by
  obtain ⟨domains, result, _, hshape, hlen, _⟩ := RecursorData.recursorType_major htype
  have hscan : (type.instL levels).takeForalls (data.majorOffset + 1) =
      some (domains.map (·.instL levels), result.instL levels) := by
    rw [hshape, instL_wrapForalls, ← hlen, ← List.length_map (f := (·.instL levels))]
    exact takeForalls_wrapForalls _ _
  have hd : domainsOf data levels = domains.map (·.instL levels) := by
    simp only [domainsOf, telescopeOf, htype, Option.getD_some, hscan]
  have hr : resultOf data levels = result.instL levels := by
    simp only [resultOf, telescopeOf, htype, Option.getD_some, hscan]
  rw [hd, hr]
  exact ⟨by rw [hshape, instL_wrapForalls], by simpa using hlen⟩

section
open Params
variable [Params]

/-- Close the projected iota replay over the actual recursor type. All occurrence
parameters are fresh telescope variables; no equality is strengthened out of it. -/
theorem equation (hregistered : RecursorRegistered env data)
    (htype : data.recursorType = some type)
    (hlevels : ∀ l ∈ levels, l.WF univs) (hlevelCount : levels.length = data.uvars)
    (hshape : type.instL levels = wrapForalls domains result)
    (hlen : domains.length = data.majorOffset + 1)
    (hinfo : env.projections (family data) info) (hindices : info.nindices = 0)
    (hnever : (info.resultLevel.inst (familyLevels data levels)).IsNeverZero)
    {r : (pattern data info).RHS × (pattern data info).Check}
    (hpat : Pat _ r) (hcheck : CheckFromTyping env univs _ r levels) :
    IsDefEq env univs [] (.const data.name levels) (value data info levels r.1 domains)
      (type.instL levels) := by
  have ht : HasType env univs [] (.const data.name levels) (wrapForalls domains result) := by
    rw [← hshape]
    exact .const (hregistered.recursorType htype) hlevels hlevelCount
  obtain ⟨hctx, hopen⟩ := ht.etaOpen_wf henv.ordered (by trivial)
  have hsource : HasType env univs (domains.reverse ++ [])
      (.app (mkApps (.const data.name levels) (vars data.majorOffset 1)) (.bvar 0)) result := by
    rwa [opened data levels hlen] at hopen
  obtain ⟨_, _, params, hmajor⟩ := hregistered.major_type henv hctx hsource (by simp)
  have hparams : params.length = info.nparams := by
    have h := StructureReplay.family_arity henv hctx hinfo (hmajor.isType henv.ordered hctx)
    simpa only [hindices, Nat.add_zero] using h
  have hrec := spineCaptures_match (c := data.name) (n := data.majorOffset) (vars data.majorOffset 1) (by simp) levels
  have hctor := spineCaptures_match (c := info.ctorName)
    (List.replicate info.nparams (.sort .zero) ++
      (List.range info.numFields).map (fun i => .proj (family data) i (.bvar 0)))
    (by simp : _ = info.nparams + info.numFields) []
  have he := StructureReplay.projected_iota_neverZero hctx hinfo hparams hindices hnever hmajor hsource
    hpat hcheck hrec (by simp) hctor
  have hbody : IsDefEq env univs (domains.reverse ++ [])
      (etaOpen domains.length (.const data.name levels)) (body data info levels r.1) result := by
    rw [opened data levels hlen]
    exact he
  rw [hshape]
  exact (ht.etaOpen_defeq henv (by trivial)).trans (hbody.etaOpen_wrapLams (by trivial) hctx)

/-- The projection unfolding body is closed because its equality was checked in
the empty context at the installed recursor's exact type. -/
theorem value_closed (hregistered : RecursorRegistered env data)
    (htype : data.recursorType = some type)
    (hlevels : ∀ l ∈ levels, l.WF univs) (hlevelCount : levels.length = data.uvars)
    (hshape : type.instL levels = wrapForalls domains result)
    (hlen : domains.length = data.majorOffset + 1)
    (hinfo : env.projections (family data) info) (hindices : info.nindices = 0)
    (hnever : (info.resultLevel.inst (familyLevels data levels)).IsNeverZero)
    {r : (pattern data info).RHS × (pattern data info).Check}
    (hpat : Pat _ r) (hcheck : CheckFromTyping env univs _ r levels) :
    (value data info levels r.1 domains).Closed :=
  (equation hregistered htype hlevels hlevelCount hshape hlen hinfo hindices hnever hpat hcheck).hasType.2.closedN
    henv.ordered (by trivial)

/-- The closed equation with the telescope selected entirely from the registry.
No occurrence-specific typing or constructor parameters appear among its premises. -/
theorem canonical_equation (hregistered : RecursorRegistered env data)
    (hlevels : ∀ l ∈ levels, l.WF univs) (hlevelCount : levels.length = data.uvars)
    (hinfo : env.projections (family data) info) (hindices : info.nindices = 0)
    (hnever : (info.resultLevel.inst (familyLevels data levels)).IsNeverZero)
    {r : (pattern data info).RHS × (pattern data info).Check}
    (hpat : Pat _ r) (hcheck : CheckFromTyping env univs _ r levels) :
    IsDefEqU env univs [] (.const data.name levels)
      (value data info levels r.1 (domainsOf data levels)) := by
  obtain ⟨type, htype⟩ := hregistered.recursorType_exists
  obtain ⟨hshape, hlen⟩ := type_shape (levels := levels) htype
  exact ⟨_, equation hregistered htype hlevels hlevelCount hshape hlen hinfo hindices hnever hpat hcheck⟩

/-- The canonical unfolding is closed, independently of any application context. -/
theorem canonical_closed (hregistered : RecursorRegistered env data)
    (hlevels : ∀ l ∈ levels, l.WF univs) (hlevelCount : levels.length = data.uvars)
    (hinfo : env.projections (family data) info) (hindices : info.nindices = 0)
    (hnever : (info.resultLevel.inst (familyLevels data levels)).IsNeverZero)
    {r : (pattern data info).RHS × (pattern data info).Check}
    (hpat : Pat _ r) (hcheck : CheckFromTyping env univs _ r levels) :
    (value data info levels r.1 (domainsOf data levels)).Closed := by
  obtain ⟨_, he⟩ := canonical_equation hregistered hlevels hlevelCount hinfo hindices hnever hpat hcheck
  exact he.hasType.2.closedN henv.ordered (by trivial)

end
end Lean4Lean.VEnv.Strengthening.ClosedStructure
