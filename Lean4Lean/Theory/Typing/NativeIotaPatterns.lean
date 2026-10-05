import Lean4Lean.Theory.Typing.NativeRuleRegistration
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.PatternIotaLemmas
import Lean4Lean.Theory.Typing.DefinitionHeadExclusivity

/-! Native iota patterns are generated from the actual restored equation.
Their RHS applies that equation's closed lambda telescope to captured
parameters, motives, minors and constructor fields. The source guard is
fixed by the registered native elimination instance. -/

namespace Lean4Lean.InductiveSignature.NativeRecursorData

/-- Actual restored constructor arguments, including specialized parameters. -/
def ruleMajorArguments (equation : VDefEq) : List VExpr :=
  (equation.lhs.stripLams.getAppFnArgs.2.getLast?.getD (.bvar 0)).getAppFnArgs.2

def ruleConstructor (data : NativeRecursorData)
    (index : Fin data.schema.signature.constructors.size) : Name :=
  data.schema.restoration.headName data.schema.signature.constructors[index].name

def rulePattern (data : NativeRecursorData)
    (index : Fin data.schema.signature.constructors.size) (equation : VDefEq) : Pattern :=
  (SimplePattern.iota data.name data.majorOffset (data.ruleConstructor index)
    (ruleMajorArguments equation).length).toPattern

def ruleCaptures (data : NativeRecursorData)
    (index : Fin data.schema.signature.constructors.size) (equation : VDefEq) :
    List (data.rulePattern index equation).RHS :=
  let pre := ((Pattern.const data.name).argumentRHS data.majorOffset).take data.indexOffset
  let ctor := (Pattern.const (data.ruleConstructor index)).argumentRHS
    (ruleMajorArguments equation).length
  pre.map (Pattern.RHS.mapPaths Sum.inl) ++
    (ctor.drop ((ruleMajorArguments equation).length -
      data.schema.signature.constructors[index].fields.length)).map (Pattern.RHS.mapPaths Sum.inr)

def ruleRHS (data : NativeRecursorData)
    (index : Fin data.schema.signature.constructors.size) (equation : VDefEq)
    (hclosed : equation.rhs.Closed) : (data.rulePattern index equation).RHS :=
  (Pattern.RHS.fixed equation.rhs hclosed).applyArgs (data.ruleCaptures index equation)

def ruleCheck (data : NativeRecursorData)
    (index : Fin data.schema.signature.constructors.size) (equation : VDefEq) :
    (data.rulePattern index equation).Check :=
  if data.largeTarget then .nonzero (data.schema.sourceLevel data.owner data.levels) .true else .true

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.VEnv
open InductiveSignature

inductive NativeIotaPattern (env : VEnv) (registry : Name → Option NativeRecursorData) :
    (p : Pattern) → p.RHS × p.Check → Prop where
  | intro {data : NativeRecursorData} {index : Fin data.schema.signature.constructors.size}
      {equation : VDefEq} (henv : env.WF)
      (hregistered : NativeRecursorRegistered env data)
      (hlookup : registry data.name = some data)
      (howner : data.schema.signature.constructors[index].owner = data.owner)
      (hgen : data.equation index = some equation) :
      NativeIotaPattern env registry (data.rulePattern index equation)
        (data.ruleRHS index equation (hregistered.equation_closed henv hgen).2.1,
          data.ruleCheck index equation)

private theorem nativeHead_varN (p : Pattern) (n : Nat) :
    (p.varN n).nativeHead = p.nativeHead := by induction n <;> simp [Pattern.varN, Pattern.nativeHead, *]

namespace NativeIotaPattern

theorem simple (H : NativeIotaPattern env registry p rhs) :
    ∃ shape : SimplePattern, p = shape.toPattern := by
  cases H
  exact ⟨.iota _ _ _ _, rfl⟩

theorem origin (H : NativeIotaPattern env registry p rhs) : NativePatternOrigin env p := by
  cases H with
  | intro henv hr hl ho hg =>
    exact ⟨_, _, _, hr.equation_present hg,
      by simp only [NativeRecursorData.rulePattern, SimplePattern.toPattern,
        Pattern.nativeHead, nativeHead_varN],
      (VExpr.nativeEquationHead_eq _).trans (hr.equation_head ho hg)⟩

theorem generated (H : NativeIotaPattern env registry p rhs) :
    ∃ data : NativeRecursorData, ∃ index : Fin data.schema.signature.constructors.size,
      ∃ (equation : VDefEq) (hclosed : equation.rhs.Closed), NativeRecursorRegistered env data ∧ registry data.name = some data ∧
      data.schema.signature.constructors[index].owner = data.owner ∧
      data.equation index = some equation ∧ p = data.rulePattern index equation ∧
      rhs ≍ (data.ruleRHS index equation hclosed, data.ruleCheck index equation) := by
  cases H with
  | @intro data index equation henv hr hl ho hg => exact ⟨data, index, equation, _, hr, hl, ho, hg, rfl, HEq.rfl⟩

/-- The iota pattern retains the exact native metadata required by the core
reduction guard; primitive quotient metadata remain a separate alternative. -/
theorem registered (H : NativeIotaPattern env registry
    (SimplePattern.iota recursor major ctor fields).toPattern rhs) :
    ∃ data, NativeRecursorRegistered env data ∧ data.name = recursor ∧
      data.majorOffset = major ∧ registry recursor = some data ∧
      (data.largeTarget = true → ∃ rest,
        rhs.2 = .nonzero (data.schema.sourceLevel data.owner data.levels) rest) := by
  obtain ⟨data, index, equation, hclosed, hr, hl, ho, hg, he, hrhs⟩ := H.generated
  have hi : (SimplePattern.iota recursor major ctor fields).toPattern.inter
      (data.rulePattern index equation) = some (data.rulePattern index equation) := by
    rw [he]; exact Pattern.inter_self _
  simp only [NativeRecursorData.rulePattern, SimplePattern.toPattern, Pattern.inter,
    bind, Option.bind_eq_some_iff] at hi
  obtain ⟨left, hleft, right, hright, _⟩ := hi
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hleft
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hright
  refine ⟨data, hr, rfl, rfl, hl, ?_⟩
  intro hlarge
  have hc := congrArg Prod.snd (eq_of_heq hrhs)
  exact ⟨.true, hc.trans (by simp only [NativeRecursorData.ruleCheck, hlarge, ↓reduceIte]; rfl)⟩

theorem iota_origin (H : NativeIotaPattern env registry
    (SimplePattern.iota recursor major ctor fields).toPattern rhs) :
    ∃ equation levels, env.defeqs equation ∧
      equation.lhs.nativeEquationHead = .const recursor levels ∧ equation.HasConstructorMajor ctor := by
  obtain ⟨data, index, equation, hclosed, hr, hl, ho, hg, he, _⟩ := H.generated
  have hi : (SimplePattern.iota recursor major ctor fields).toPattern.inter
      (data.rulePattern index equation) = some (data.rulePattern index equation) := by
    rw [he]; exact Pattern.inter_self _
  simp only [NativeRecursorData.rulePattern, SimplePattern.toPattern, Pattern.inter,
    bind, Option.bind_eq_some_iff] at hi
  obtain ⟨left, hleft, right, hright, _⟩ := hi
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hleft
  obtain ⟨rfl, rfl⟩ := Pattern.constVarN_inter hright
  exact ⟨equation, _, hr.equation_present hg,
    (VExpr.nativeEquationHead_eq _).trans (hr.equation_head ho hg), hr.equation_major hg⟩

theorem app_l (H : NativeIotaPattern env registry p rhs)
    (hs : Subpattern (.app fn arg) p) : ¬Subpattern (.app left right) fn := by
  cases H
  obtain ⟨rfl, rfl⟩ := hs.iota_app
  exact Subpattern.constVarN_noapp

theorem app_l_uniq (H : NativeIotaPattern env registry p rhs)
    (H' : NativeIotaPattern env registry p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hb : Subpattern (.var body) fn) : fn'.inter body = none := by
  cases H with
  | @intro data index equation henv hr hl ho hg =>
    cases H' with
    | @intro data' index' equation' henv' hr' hl' ho' hg' =>
      obtain ⟨rfl, rfl⟩ := hs.iota_app
      obtain ⟨rfl, rfl⟩ := hs'.iota_app
      apply SimplePattern.iota_app_l_uniq ?_ hb
      intro hn
      rw [hn] at hl
      cases Option.some.inj (hl.symm.trans hl')
      rfl

theorem app_uniq (H : NativeIotaPattern env registry p rhs)
    (H' : NativeIotaPattern env registry p' rhs')
    (hs : Subpattern (.app fn arg) p) (hs' : Subpattern (.app fn' arg') p')
    (hl : Subpattern left fn) (hright : Subpattern right arg') : left.inter right = none := by
  cases H with
  | @intro data index equation henv hr hlookup ho hg =>
    cases H' with
    | @intro data' index' equation' henv' hr' hlookup' ho' hg' =>
      obtain ⟨rfl, rfl⟩ := hs.iota_app
      obtain ⟨rfl, rfl⟩ := hs'.iota_app
      apply SimplePattern.iota_app_uniq ?_ hl hright
      intro hn
      have hrigid := henv.native_constructor_rigid (hr'.equation_present hg') (hr'.equation_major hg')
      apply hrigid equation (hr.equation_present hg) (VLevel.params data.uvars)
      exact ((VExpr.nativeEquationHead_eq _).trans (hr.equation_head ho hg)).trans (by rw [hn]; rfl)

end NativeIotaPattern
end Lean4Lean.VEnv
