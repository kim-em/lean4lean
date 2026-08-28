import Lean4Lean.Theory.Inductive

namespace Lean4Lean

open Lean

namespace VExpr

/-- Constant-freeness is preserved when applying a constant-free function to
constant-free arguments.  Projection expansion needs the forward direction;
the converse is intentionally not used. -/
theorem containsAnyConst_mkApps_eq_false
    (hfn : fn.containsAnyConst names = false)
    (hargs : ∀ arg ∈ args, arg.containsAnyConst names = false) :
    (VExpr.mkApps fn args).containsAnyConst names = false := by
  induction args generalizing fn with
  | nil => exact hfn
  | cons arg args ih =>
      apply ih
      · exact Bool.or_eq_false_iff.mpr ⟨hfn, hargs arg (by simp)⟩
      · intro current hcurrent
        exact hargs current (by simp [hcurrent])

/-- Exact support decomposition for an application spine.  This converse is
what projection refinement needs: every constant in the expanded term comes
from either the head or one of the explicitly retained arguments. -/
theorem containsAnyConst_mkApps_eq_false_iff
    (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).containsAnyConst names = false ↔
      fn.containsAnyConst names = false ∧
        ∀ arg ∈ args, arg.containsAnyConst names = false := by
  induction args generalizing fn with
  | nil => simp [VExpr.mkApps]
  | cons arg args ih =>
      rw [show VExpr.mkApps fn (arg :: args) =
        VExpr.mkApps (.app fn arg) args by rfl, ih]
      simp [VExpr.containsAnyConst, and_assoc]

/-- A lambda telescope is constant-free exactly when all of its domains and
its body are constant-free.  This forward constructor is sufficient for the
canonical projection minor. -/
theorem containsAnyConst_wrapLams_eq_false
    (hdomains : ∀ domain ∈ domains,
      domain.containsAnyConst names = false)
    (hbody : body.containsAnyConst names = false) :
    (VExpr.wrapLams domains body).containsAnyConst names = false := by
  induction domains with
  | nil => exact hbody
  | cons domain domains ih =>
      apply Bool.or_eq_false_iff.mpr
      exact ⟨hdomains domain (by simp), ih (fun current hcurrent =>
        hdomains current (by simp [hcurrent]))⟩

/-- Exact support decomposition for a lambda telescope. -/
theorem containsAnyConst_wrapLams_eq_false_iff
    (domains : List VExpr) (body : VExpr) :
    (VExpr.wrapLams domains body).containsAnyConst names = false ↔
      (∀ domain ∈ domains,
        domain.containsAnyConst names = false) ∧
      body.containsAnyConst names = false := by
  induction domains with
  | nil => simp [VExpr.wrapLams]
  | cons domain domains ih =>
      constructor
      · intro h
        have hparts : domain.containsAnyConst names = false ∧
            (VExpr.wrapLams domains body).containsAnyConst names = false :=
          Bool.or_eq_false_iff.mp h
        have htail := ih.mp hparts.2
        exact ⟨fun current hcurrent => by
          rcases List.mem_cons.mp hcurrent with rfl | hcurrent
          · exact hparts.1
          · exact htail.1 current hcurrent, htail.2⟩
      · rintro ⟨hdomains, hbody⟩
        apply Bool.or_eq_false_iff.mpr
        refine ⟨hdomains domain (by simp), ih.mpr ⟨?_, hbody⟩⟩
        intro current hcurrent
        exact hdomains current (by simp [hcurrent])

@[simp] theorem instL_mkApps (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).instL levels =
      VExpr.mkApps (fn.instL levels) (args.map (VExpr.instL levels)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
      simpa [VExpr.mkApps, VExpr.instL] using ih (.app fn arg)

@[simp] theorem instL_wrapLams (domains : List VExpr) (body : VExpr) :
    (VExpr.wrapLams domains body).instL levels =
      VExpr.wrapLams (domains.map (VExpr.instL levels))
        (body.instL levels) := by
  induction domains with
  | nil => rfl
  | cons domain domains ih =>
      simpa [VExpr.wrapLams, VExpr.instL] using congrArg
        (VExpr.lam (domain.instL levels)) ih

@[simp] theorem liftN_mkApps (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).liftN n k =
      VExpr.mkApps (fn.liftN n k) (args.map (fun arg => arg.liftN n k)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
      simpa [VExpr.mkApps, VExpr.liftN] using ih (.app fn arg)

@[simp] theorem instN_mkApps (fn : VExpr) (args : List VExpr) :
    (VExpr.mkApps fn args).inst substitution k =
      VExpr.mkApps (fn.inst substitution k)
        (args.map (fun arg => arg.inst substitution k)) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
      simpa [VExpr.mkApps, VExpr.inst] using ih (.app fn arg)

end VExpr

/-- Explicit syntax data for the eliminator term used to implement one
primitive structure projection.  The fields are deliberately visible: a
projection expansion depends not only on its major premise but also on the
eliminator, implicit parameters, motive, and constructor-field domains.

This is a syntax layer, not yet an environment-validity certificate.  A
subsequent environment-indexed relation must derive these fields from the
installed one-constructor inductive declaration. -/
structure CanonicalProjectionExpansion where
  structName : Name
  /-- Universe arguments of the projected inductive family. -/
  familyLevels : List VLevel
  /-- Universe of the projection result, supplied to `.casesOn` before the
  family universe arguments. -/
  resultLevel : VLevel
  params : List VExpr
  indices : List VExpr
  motive : VExpr
  major : VExpr
  fieldDomains : List VExpr
  index : Nat
  index_lt : index < fieldDomains.length

namespace CanonicalProjectionExpansion

/-- Lift telescope domains at the successively deeper binder cutoffs. -/
def liftDomains (domains : List VExpr) (n k : Nat) : List VExpr :=
  match domains with
  | [] => []
  | domain :: domains =>
      domain.liftN n k :: liftDomains domains n (k + 1)

/-- Instantiate telescope domains at the successively deeper binder cutoffs. -/
def instDomains (domains : List VExpr) (substitution : VExpr) (k : Nat) :
    List VExpr :=
  match domains with
  | [] => []
  | domain :: domains =>
      domain.inst substitution k :: instDomains domains substitution (k + 1)

@[simp] theorem liftDomains_length
    (domains : List VExpr) (n k : Nat) :
    (liftDomains domains n k).length = domains.length := by
  induction domains generalizing k with
  | nil => rfl
  | cons domain domains ih =>
      simp [liftDomains, ih]

@[simp] theorem instDomains_length
    (domains : List VExpr) (substitution : VExpr) (k : Nat) :
    (instDomains domains substitution k).length = domains.length := by
  induction domains generalizing k with
  | nil => rfl
  | cons domain domains ih =>
      simp [instDomains, ih]

theorem liftN_wrapLams (domains : List VExpr) (body : VExpr) :
    (VExpr.wrapLams domains body).liftN n k =
      VExpr.wrapLams (liftDomains domains n k)
        (body.liftN n (k + domains.length)) := by
  induction domains generalizing k with
  | nil => rfl
  | cons domain domains ih =>
      simp only [VExpr.wrapLams, List.foldr_cons, VExpr.liftN,
        liftDomains]
      have htail := ih (k := k + 1)
      simp only [VExpr.wrapLams] at htail
      rw [htail]
      congr 2
      simp [Nat.add_comm, Nat.add_left_comm]

theorem instN_wrapLams (domains : List VExpr) (body substitution : VExpr) :
    (VExpr.wrapLams domains body).inst substitution k =
      VExpr.wrapLams (instDomains domains substitution k)
        (body.inst substitution (k + domains.length)) := by
  induction domains generalizing k with
  | nil => rfl
  | cons domain domains ih =>
      simp only [VExpr.wrapLams, List.foldr_cons, VExpr.inst,
        instDomains]
      have htail := ih (k := k + 1)
      simp only [VExpr.wrapLams] at htail
      rw [htail]
      congr 2
      simp [Nat.add_comm, Nat.add_left_comm]

/-- The selected constructor field beneath the complete minor telescope. -/
def fieldVar (P : CanonicalProjectionExpansion) : Nat :=
  P.fieldDomains.length - P.index - 1

/-- The single minor premise selecting the requested constructor field. -/
def minor (P : CanonicalProjectionExpansion) : VExpr :=
  VExpr.wrapLams P.fieldDomains (.bvar P.fieldVar)

/-- Canonical `.casesOn` implementation of a primitive projection.  This is
the eliminator that `Meta.expandProj` actually elaborates.  In particular its
single minor follows the major premise, unlike the primary recursor's minor
telescope.  This distinction matters for indexed and mutual families. -/
def target (P : CanonicalProjectionExpansion) : VExpr :=
  VExpr.mkApps
    (.const (mkCasesOnName P.structName) (P.resultLevel :: P.familyLevels))
    (P.params ++ [P.motive] ++ P.indices ++ [P.major, P.minor])

/-- Universe substitution of every explicit component of a canonical
projection expansion. -/
def instL (P : CanonicalProjectionExpansion) (substitution : List VLevel) :
    CanonicalProjectionExpansion where
  structName := P.structName
  familyLevels := P.familyLevels.map (VLevel.inst substitution)
  resultLevel := P.resultLevel.inst substitution
  params := P.params.map (VExpr.instL substitution)
  indices := P.indices.map (VExpr.instL substitution)
  motive := P.motive.instL substitution
  major := P.major.instL substitution
  fieldDomains := P.fieldDomains.map (VExpr.instL substitution)
  index := P.index
  index_lt := by simpa using P.index_lt

/-- De Bruijn lifting of every component, respecting the increasing cutoff
under the constructor-field telescope. -/
def liftN (P : CanonicalProjectionExpansion) (n k : Nat) :
    CanonicalProjectionExpansion where
  structName := P.structName
  familyLevels := P.familyLevels
  resultLevel := P.resultLevel
  params := P.params.map (fun param => param.liftN n k)
  indices := P.indices.map (fun index => index.liftN n k)
  motive := P.motive.liftN n k
  major := P.major.liftN n k
  fieldDomains := liftDomains P.fieldDomains n k
  index := P.index
  index_lt := by simpa using P.index_lt

/-- Term instantiation of every component, respecting the increasing cutoff
under the constructor-field telescope. -/
def instN (P : CanonicalProjectionExpansion) (substitution : VExpr) (k : Nat) :
    CanonicalProjectionExpansion where
  structName := P.structName
  familyLevels := P.familyLevels
  resultLevel := P.resultLevel
  params := P.params.map (fun param => param.inst substitution k)
  indices := P.indices.map (fun index => index.inst substitution k)
  motive := P.motive.inst substitution k
  major := P.major.inst substitution k
  fieldDomains := instDomains P.fieldDomains substitution k
  index := P.index
  index_lt := by simpa using P.index_lt

@[simp] theorem fieldVar_lt (P : CanonicalProjectionExpansion) :
    P.fieldVar < P.fieldDomains.length := by
  unfold fieldVar
  have := P.index_lt
  omega

theorem minor_noConsts
    (P : CanonicalProjectionExpansion)
    (hdomains : ∀ domain ∈ P.fieldDomains,
      domain.containsAnyConst names = false) :
    P.minor.containsAnyConst names = false := by
  apply VExpr.containsAnyConst_wrapLams_eq_false hdomains
  rfl

/-- Exact sufficient support condition for the canonical expansion.  In
particular, absence from `major` alone is insufficient: all five other
sources of constants are represented explicitly. -/
theorem target_noConsts
    (P : CanonicalProjectionExpansion)
    (heliminator : mkCasesOnName P.structName ∉ names)
    (hparams : ∀ param ∈ P.params,
      param.containsAnyConst names = false)
    (hindices : ∀ index ∈ P.indices,
      index.containsAnyConst names = false)
    (hmotive : P.motive.containsAnyConst names = false)
    (hmajor : P.major.containsAnyConst names = false)
    (hdomains : ∀ domain ∈ P.fieldDomains,
      domain.containsAnyConst names = false) :
    P.target.containsAnyConst names = false := by
  apply VExpr.containsAnyConst_mkApps_eq_false
  · simp [VExpr.containsAnyConst, heliminator]
  · intro arg harg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at harg
    rcases harg with ((hparam | hmotiveArg) | hindex) | hmajorArg | hminor
    · exact hparams arg hparam
    · simpa [hmotiveArg] using hmotive
    · exact hindices arg hindex
    · simpa [hmajorArg] using hmajor
    · simpa [hminor] using P.minor_noConsts hdomains

/-- Exact constant-support boundary for a canonical projection expansion.
Unlike the former global preservation premise, this statement makes the
recovered structure parameters, motive, and field telescope visible. -/
theorem target_noConsts_iff
    (P : CanonicalProjectionExpansion) :
    P.target.containsAnyConst names = false ↔
      mkCasesOnName P.structName ∉ names ∧
      (∀ param ∈ P.params,
        param.containsAnyConst names = false) ∧
      P.motive.containsAnyConst names = false ∧
      (∀ domain ∈ P.fieldDomains,
        domain.containsAnyConst names = false) ∧
      (∀ index ∈ P.indices,
        index.containsAnyConst names = false) ∧
      P.major.containsAnyConst names = false := by
  rw [target, VExpr.containsAnyConst_mkApps_eq_false_iff]
  constructor
  · rintro ⟨hhead, hargs⟩
    have heliminator : mkCasesOnName P.structName ∉ names := by
      simpa [VExpr.containsAnyConst] using hhead
    have hparams : ∀ param ∈ P.params,
        param.containsAnyConst names = false := by
      intro param hparam
      exact hargs param (by simp [hparam])
    have hmotive := hargs P.motive (by simp)
    have hminor := hargs P.minor (by simp)
    have hdomains : ∀ domain ∈ P.fieldDomains,
        domain.containsAnyConst names = false :=
      (VExpr.containsAnyConst_wrapLams_eq_false_iff
        P.fieldDomains (.bvar P.fieldVar)).mp hminor |>.1
    have hindices : ∀ index ∈ P.indices,
        index.containsAnyConst names = false := by
      intro index hindex
      exact hargs index (by simp [hindex])
    have hmajor := hargs P.major (by simp)
    exact ⟨heliminator, hparams, hmotive, hdomains, hindices, hmajor⟩
  · rintro ⟨heliminator, hparams, hmotive, hdomains, hindices, hmajor⟩
    refine ⟨by simpa [VExpr.containsAnyConst] using heliminator, ?_⟩
    intro arg harg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at harg
    rcases harg with ((hparam | hmotiveArg) | hindex) | hmajorArg | hminor
    · exact hparams arg hparam
    · simpa [hmotiveArg] using hmotive
    · exact hindices arg hindex
    · simpa [hmajorArg] using hmajor
    · simpa [hminor] using P.minor_noConsts hdomains

@[simp] theorem fieldVar_instL
    (P : CanonicalProjectionExpansion) (substitution : List VLevel) :
    (P.instL substitution).fieldVar = P.fieldVar := by
  simp [fieldVar, instL]

@[simp] theorem minor_instL
    (P : CanonicalProjectionExpansion) (substitution : List VLevel) :
    (P.instL substitution).minor = P.minor.instL substitution := by
  simp [minor, instL, fieldVar, VExpr.instL]

@[simp] theorem target_instL
    (P : CanonicalProjectionExpansion) (substitution : List VLevel) :
    (P.instL substitution).target = P.target.instL substitution := by
  simp [target, instL, minor, fieldVar, List.map_append, VExpr.instL]

@[simp] theorem fieldVar_liftN
    (P : CanonicalProjectionExpansion) (n k : Nat) :
    (P.liftN n k).fieldVar = P.fieldVar := by
  simp [fieldVar, liftN]

@[simp] theorem minor_liftN
    (P : CanonicalProjectionExpansion) (n k : Nat) :
    (P.liftN n k).minor = P.minor.liftN n k := by
  rw [minor, minor, liftN_wrapLams]
  change VExpr.wrapLams (liftDomains P.fieldDomains n k)
      (VExpr.bvar (P.liftN n k).fieldVar) =
    VExpr.wrapLams (liftDomains P.fieldDomains n k)
      ((VExpr.bvar P.fieldVar).liftN n (k + P.fieldDomains.length))
  rw [fieldVar_liftN]
  simp only [VExpr.liftN, liftVar]
  rw [if_pos]
  exact Nat.lt_of_lt_of_le P.fieldVar_lt (Nat.le_add_left ..)

@[simp] theorem target_liftN
    (P : CanonicalProjectionExpansion) (n k : Nat) :
    (P.liftN n k).target = P.target.liftN n k := by
  unfold target
  rw [VExpr.liftN_mkApps, minor_liftN]
  simp [liftN, List.map_append, VExpr.liftN]

@[simp] theorem fieldVar_instN
    (P : CanonicalProjectionExpansion) (substitution : VExpr) (k : Nat) :
    (P.instN substitution k).fieldVar = P.fieldVar := by
  simp [fieldVar, instN]

@[simp] theorem minor_instN
    (P : CanonicalProjectionExpansion) (substitution : VExpr) (k : Nat) :
    (P.instN substitution k).minor = P.minor.inst substitution k := by
  rw [minor, minor, instN_wrapLams]
  change VExpr.wrapLams (instDomains P.fieldDomains substitution k)
      (VExpr.bvar (P.instN substitution k).fieldVar) =
    VExpr.wrapLams (instDomains P.fieldDomains substitution k)
      ((VExpr.bvar P.fieldVar).inst substitution
        (k + P.fieldDomains.length))
  rw [fieldVar_instN]
  simp only [VExpr.inst, VExpr.instVar]
  rw [if_pos]
  exact Nat.lt_of_lt_of_le P.fieldVar_lt (Nat.le_add_left ..)

@[simp] theorem target_instN
    (P : CanonicalProjectionExpansion) (substitution : VExpr) (k : Nat) :
    (P.instN substitution k).target = P.target.inst substitution k := by
  unfold target
  rw [VExpr.instN_mkApps, minor_instN]
  simp [instN, List.map_append, VExpr.inst]

end CanonicalProjectionExpansion

end Lean4Lean
