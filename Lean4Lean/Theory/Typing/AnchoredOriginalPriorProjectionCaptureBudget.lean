import Lean4Lean.Theory.Typing.AnchoredOriginalDependencyEndpoints
import Lean4Lean.Theory.Typing.AnchoredOriginalParameterRouteReserve

/-! The existing two-parameter outer projection reserve pays one captured
major, provided the formal first projection has the explicit structural
sixteen-fold bound. This does not bound a reified derivation. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure

/-- Numeric obligation for formalizing the first projection inside the
second field of a two-parameter record. The hypotheses refer to actual
original dependency weights, not a caller-chosen reserve. -/
theorem priorProjection_capture_familyReserve
    (priorBound : prior ≤ field) (majorBound : major ≤ owner)
    (large : 4 ≤ field + owner) :
    16 * prior * (1 + 2 * major) ≤
      projectionFamilyReserve 2 field owner := by
  let total := field + owner
  have totalLarge : 4 ≤ total := large
  have square : 4 * total ≤ total * total :=
    Nat.mul_le_mul_right total totalLarge
  have power : 4 * (1 + 2 * total) ≤ (total + 2) ^ 2 := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_add,
      Nat.add_mul] at *
    omega
  have factor : 16 * (1 + 2 * total) ≤
      (total + 2) ^ 2 * (1 + total) := by
    have h := Nat.mul_le_mul power (show 4 ≤ 1 + total by omega)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have left := Nat.mul_le_mul
    (show prior ≤ total by dsimp [total]; omega)
    (show 16 * (1 + 2 * major) ≤ 16 * (1 + 2 * total) from
      Nat.mul_le_mul_left 16 (by dsimp [total]; omega))
  have right := Nat.mul_le_mul_left total factor
  exact Nat.le_trans (by simpa only [Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using left) (by
      simpa only [projectionFamilyReserve, total, Nat.add_assoc, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using right)

/-- A fresh major variable adds only its constructor above the retained
formation. The routed reserve grows by at most sixteen for two slots. -/
theorem routedParameterDependencyReserve_major_succ
    (positive : 0 < major) :
    routedParameterDependencyReserve 2 header equalities field (major + 1) ≤
      16 * routedParameterDependencyReserve 2 header equalities field major := by
  unfold routedParameterDependencyReserve
  have first : 2 * (header + equalities + (major + 1)) ≤
      2 * (2 * (header + equalities + major)) := by omega
  have base : 2 * (header + equalities + (major + 1)) + 2 ≤
      2 * (2 * (header + equalities + major) + 2) := by omega
  have last : 1 + field + (major + 1) ≤ 2 * (1 + field + major) := by omega
  have bound := Nat.mul_le_mul first
    (Nat.mul_le_mul (Nat.pow_le_pow_left base 2) last)
  rw [show (16 : Nat) = 2 * (2 * 2) * 2 from rfl]
  simpa only [Nat.mul_pow, Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem projectionFamilyReserve_major_succ (positive : 0 < major) :
    projectionFamilyReserve 2 field (major + 1) ≤
      16 * projectionFamilyReserve 2 field major := by
  unfold projectionFamilyReserve
  have first : field + (major + 1) ≤ 2 * (field + major) := by omega
  have base : field + (major + 1) + 2 ≤ 2 * (field + major + 2) := by omega
  have last : 1 + field + (major + 1) ≤ 2 * (1 + field + major) := by omega
  have bound := Nat.mul_le_mul first
    (Nat.mul_le_mul (Nat.pow_le_pow_left base 2) last)
  rw [show (16 : Nat) = 2 * (2 * 2) * 2 from rfl]
  simpa only [Nat.mul_pow, Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem parameterDependencyReserve_major_succ :
    parameterDependencyReserve count header equalities field (major + 1) ≤
      2 * parameterDependencyReserve count header equalities field major := by
  unfold parameterDependencyReserve
  have bound := Nat.mul_le_mul_left
    (2 * (header + equalities) * (header + equalities + 2) ^ count)
    (show 1 + field + (major + 1) ≤ 2 * (1 + field + major) by omega)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem projectionDependencyReserve_major_succ
    {env : VEnv} {name : Lean.Name} {info : VProjectionInfo}
    (registered : env.projections name info)
    (two : info.nparams + info.nindices = 2) (positive : 0 < major) :
    projectionDependencyReserve registered index header field (major + 1) ≤
      16 * projectionDependencyReserve registered index header field major := by
  have family := projectionFamilyReserve_major_succ (field := field) positive
  have linear := Nat.mul_le_mul_left
    (header * (header + 2) ^ (info.nparams + index))
    (show 1 + field + (major + 1) ≤ 2 * (1 + field + major) by omega)
  have linearBound : header * ((header + 2) ^ (info.nparams + index) *
      (1 + field + (major + 1))) ≤
      2 * (header * ((header + 2) ^ (info.nparams + index) * (1 + field + major))) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using linear
  unfold projectionDependencyReserve
  rw [two]
  omega

/-- The larger bound also pays reflexivization of an endpoint formation
before constructing the formal major variable. -/
theorem priorProjection_reflexiveCapture_familyReserve
    (priorBound : prior ≤ field) (majorBound : major ≤ field + owner)
    (large : 32 ≤ field + owner) :
    256 * prior * (1 + 2 * major) ≤
      projectionFamilyReserve 2 field owner := by
  let total := field + owner
  have totalLarge : 32 ≤ total := large
  have square : 32 * total ≤ total * total :=
    Nat.mul_le_mul_right total totalLarge
  have power : 16 * (1 + 2 * total) ≤ (total + 2) ^ 2 := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_add,
      Nat.add_mul] at *
    omega
  have factor : 256 * (1 + 2 * total) ≤
      (total + 2) ^ 2 * (1 + total) := by
    have h := Nat.mul_le_mul power (show 16 ≤ 1 + total by omega)
    rw [show (256 : Nat) = 16 * 16 from rfl]
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have left := Nat.mul_le_mul
    (show prior ≤ total by dsimp [total]; omega)
    (show 256 * (1 + 2 * major) ≤ 256 * (1 + 2 * total) from
      Nat.mul_le_mul_left 256 (by dsimp [total]; omega))
  have right := Nat.mul_le_mul_left total factor
  exact Nat.le_trans (by simpa only [Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using left) (by
      simpa only [projectionFamilyReserve, total, Nat.add_assoc, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using right)

private theorem rule_cons_weight_two (first : Origin) (rest : List Origin) :
    2 ≤ (Origin.rule (first :: rest)).weight := by
  have positive := first.weight_pos
  simp only [Origin.weight, List.map_cons, List.sum_cons]
  omega

theorem Derivation.dependencyWeight_two_of_nonsort
    (ordered : env.Ordered) (original : Derivation env U source left right type)
    (notSort : ∀ level, type ≠ VExpr.sort level) :
    2 ≤ (original.dependencyOrigin ordered).weight := by
  cases original <;> rw [Derivation.dependencyOrigin.eq_def]
  all_goals first
    | exact False.elim (notSort _ rfl)
    | exact rule_cons_weight_two _ _

theorem routedParameterDependencyReserve_major_four :
    routedParameterDependencyReserve 2 header equalities field (4 * major) ≤
      256 * routedParameterDependencyReserve 2 header equalities field major := by
  unfold routedParameterDependencyReserve
  have first : 2 * (header + equalities + 4 * major) ≤
      4 * (2 * (header + equalities + major)) := by omega
  have base : 2 * (header + equalities + 4 * major) + 2 ≤
      4 * (2 * (header + equalities + major) + 2) := by omega
  have last : 1 + field + 4 * major ≤ 4 * (1 + field + major) := by omega
  have bound := Nat.mul_le_mul first
    (Nat.mul_le_mul (Nat.pow_le_pow_left base 2) last)
  rw [show (256 : Nat) = 4 * (4 * 4) * 4 from rfl]
  simpa only [Nat.mul_pow, Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem projectionFamilyReserve_major_four :
    projectionFamilyReserve 2 field (4 * major) ≤
      256 * projectionFamilyReserve 2 field major := by
  unfold projectionFamilyReserve
  have first : field + 4 * major ≤ 4 * (field + major) := by omega
  have base : field + 4 * major + 2 ≤ 4 * (field + major + 2) := by omega
  have last : 1 + field + 4 * major ≤ 4 * (1 + field + major) := by omega
  have bound := Nat.mul_le_mul first
    (Nat.mul_le_mul (Nat.pow_le_pow_left base 2) last)
  rw [show (256 : Nat) = 4 * (4 * 4) * 4 from rfl]
  simpa only [Nat.mul_pow, Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem parameterDependencyReserve_major_four :
    parameterDependencyReserve count header equalities field (4 * major) ≤
      4 * parameterDependencyReserve count header equalities field major := by
  unfold parameterDependencyReserve
  have bound := Nat.mul_le_mul_left
    (2 * (header + equalities) * (header + equalities + 2) ^ count)
    (show 1 + field + 4 * major ≤ 4 * (1 + field + major) by omega)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem projectionDependencyReserve_major_four
    {env : VEnv} {name : Lean.Name} {info : VProjectionInfo}
    (registered : env.projections name info)
    (two : info.nparams + info.nindices = 2) :
    projectionDependencyReserve registered index header field (4 * major) ≤
      256 * projectionDependencyReserve registered index header field major := by
  have family := projectionFamilyReserve_major_four (field := field) (major := major)
  have linear := Nat.mul_le_mul_left
    (header * (header + 2) ^ (info.nparams + index))
    (show 1 + field + 4 * major ≤ 4 * (1 + field + major) by omega)
  have linearBound : header * ((header + 2) ^ (info.nparams + index) *
      (1 + field + 4 * major)) ≤
      4 * (header * ((header + 2) ^ (info.nparams + index) * (1 + field + major))) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using linear
  unfold projectionDependencyReserve
  rw [two]
  omega

theorem routedParameterDependencyReserve_two_large
    (headerPositive : 0 < header) (fieldPositive : 0 < field)
    (majorPositive : 0 < major) :
    32 ≤ routedParameterDependencyReserve 2 header equalities field major := by
  have bound := routedParameterDependencyReserve_mono (count := 2)
    (header := 1) (equalities := 0) (field := 1) (major := 1)
    (show 1 ≤ header by omega) (Nat.zero_le equalities)
    (show 1 ≤ field by omega) (show 1 ≤ major by omega)
  have small : routedParameterDependencyReserve 2 1 0 1 1 = 432 := rfl
  rw [small] at bound
  omega

/-- Exact arithmetic shape of the production first-projection endpoint.
All three reserves are those already stored by dependencyOrigin. -/
theorem firstProjectionDependencyWeight_major_four
    {env : VEnv} {name : Lean.Name} {info : VProjectionInfo}
    (registered : env.projections name info)
    (parameters : info.nparams = 2) (indices : info.nindices = 0) :
    2 + field + 4 * major +
      (projectionDependencyReserve registered 0 header field (4 * major) +
        parameterDependencyReserve 2 header equalities field (4 * major) +
        routedParameterDependencyReserve 2 header equalities field (4 * major)) ≤
    256 * (2 + field + major +
      (projectionDependencyReserve registered 0 header field major +
        parameterDependencyReserve 2 header equalities field major +
        routedParameterDependencyReserve 2 header equalities field major)) := by
  have projection := projectionDependencyReserve_major_four
    (index := 0) (header := header) (field := field) (major := major)
    registered (by omega)
  have parameter := parameterDependencyReserve_major_four
    (count := 2) (header := header) (equalities := equalities) (field := field) (major := major)
  have route := routedParameterDependencyReserve_major_four
    (header := header) (equalities := equalities) (field := field) (major := major)
  omega

open private typed_extended_environment_bound from
  Lean4Lean.Theory.Typing.AnchoredOriginalClosureMeasure

/-- The actual bundle stored by a plain major capture fits the existing
outer family reserve. Weakening/reflexivization must establish `formalBound`
for the particular constructed original; no bound on reification is used. -/
theorem formalPriorProjection_capture_cost
    (formal prior major domain : Origin) (environment : List Closure)
    (formalBound : formal.weight ≤ 256 * prior.weight)
    (domainBound : domain.weight ≤ major.weight)
    (priorBound : prior.weight ≤ field) (majorBound : major.weight ≤ field + owner)
    (large : 32 ≤ field + owner) :
    (Closure.close formal
      (.bundle (.close major environment) (.close domain environment) :: environment)).cost ≤
      projectionFamilyReserve 2 field owner * (1 + environmentCost environment) := by
  have captured := typed_extended_environment_bound domain major environment
  have capturedBound : 1 + environmentCost
      (.bundle (.close major environment) (.close domain environment) :: environment) ≤
      (1 + 2 * major.weight) * (1 + environmentCost environment) :=
    Nat.le_trans captured (Nat.mul_le_mul_right _ (by omega))
  have bound := Nat.mul_le_mul formalBound capturedBound
  have paid := Nat.mul_le_mul_right (1 + environmentCost environment)
    (priorProjection_reflexiveCapture_familyReserve priorBound majorBound large)
  exact Nat.le_trans bound (by simpa only [Nat.mul_assoc] using paid)

theorem routedParameterDependencyReserve_joint_four :
    routedParameterDependencyReserve 2 header equalities (4 * field) (4 * major) ≤
      256 * routedParameterDependencyReserve 2 header equalities field major := by
  unfold routedParameterDependencyReserve
  have first : 2 * (header + equalities + 4 * major) ≤
      4 * (2 * (header + equalities + major)) := by omega
  have base : 2 * (header + equalities + 4 * major) + 2 ≤
      4 * (2 * (header + equalities + major) + 2) := by omega
  have last : 1 + 4 * field + 4 * major ≤ 4 * (1 + field + major) := by omega
  have bound := Nat.mul_le_mul first
    (Nat.mul_le_mul (Nat.pow_le_pow_left base 2) last)
  rw [show (256 : Nat) = 4 * (4 * 4) * 4 from rfl]
  simpa only [Nat.mul_pow, Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem projectionFamilyReserve_joint_four :
    projectionFamilyReserve 2 (4 * field) (4 * major) ≤
      256 * projectionFamilyReserve 2 field major := by
  unfold projectionFamilyReserve
  have first : 4 * field + 4 * major ≤ 4 * (field + major) := by omega
  have base : 4 * field + 4 * major + 2 ≤ 4 * (field + major + 2) := by omega
  have last : 1 + 4 * field + 4 * major ≤ 4 * (1 + field + major) := by omega
  have bound := Nat.mul_le_mul first
    (Nat.mul_le_mul (Nat.pow_le_pow_left base 2) last)
  rw [show (256 : Nat) = 4 * (4 * 4) * 4 from rfl]
  simpa only [Nat.mul_pow, Nat.pow_succ, Nat.pow_zero, Nat.one_mul,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem parameterDependencyReserve_joint_four :
    parameterDependencyReserve count header equalities (4 * field) (4 * major) ≤
      4 * parameterDependencyReserve count header equalities field major := by
  unfold parameterDependencyReserve
  have bound := Nat.mul_le_mul_left
    (2 * (header + equalities) * (header + equalities + 2) ^ count)
    (show 1 + 4 * field + 4 * major ≤ 4 * (1 + field + major) by omega)
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bound

theorem projectionDependencyReserve_joint_four
    {env : VEnv} {name : Lean.Name} {info : VProjectionInfo}
    (registered : env.projections name info)
    (two : info.nparams + info.nindices = 2) :
    projectionDependencyReserve registered index header (4 * field) (4 * major) ≤
      256 * projectionDependencyReserve registered index header field major := by
  have family := projectionFamilyReserve_joint_four (field := field) (major := major)
  have linear := Nat.mul_le_mul_left
    (header * (header + 2) ^ (info.nparams + index))
    (show 1 + 4 * field + 4 * major ≤ 4 * (1 + field + major) by omega)
  have linearBound : header * ((header + 2) ^ (info.nparams + index) *
      (1 + 4 * field + 4 * major)) ≤
      4 * (header * ((header + 2) ^ (info.nparams + index) * (1 + field + major))) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using linear
  unfold projectionDependencyReserve
  rw [two]
  omega

theorem firstProjectionDependencyWeight_joint_four
    {env : VEnv} {name : Lean.Name} {info : VProjectionInfo}
    (registered : env.projections name info)
    (parameters : info.nparams = 2) (indices : info.nindices = 0) :
    2 + 4 * field + 4 * major +
      (projectionDependencyReserve registered 0 header (4 * field) (4 * major) +
        parameterDependencyReserve 2 header equalities (4 * field) (4 * major) +
        routedParameterDependencyReserve 2 header equalities (4 * field) (4 * major)) ≤
    256 * (2 + field + major +
      (projectionDependencyReserve registered 0 header field major +
        parameterDependencyReserve 2 header equalities field major +
        routedParameterDependencyReserve 2 header equalities field major)) := by
  have projection := projectionDependencyReserve_joint_four
    (index := 0) (header := header) (field := field) (major := major)
    registered (by omega)
  have parameter := parameterDependencyReserve_joint_four
    (count := 2) (header := header) (equalities := equalities) (field := field) (major := major)
  have route := routedParameterDependencyReserve_joint_four
    (header := header) (equalities := equalities) (field := field) (major := major)
  omega

theorem projectionDependencyReserve_fields_mono
    {env : VEnv} {name : Lean.Name} {info : VProjectionInfo}
    (registered : env.projections name info)
    (fieldBound : field ≤ nextField) (majorBound : major ≤ nextMajor) :
    projectionDependencyReserve registered index header field major ≤
      projectionDependencyReserve registered index header nextField nextMajor := by
  have family := projectionFamilyReserve_mono
    (count := info.nparams + info.nindices) fieldBound majorBound
  have linear := Nat.mul_le_mul_left (header * (header + 2) ^ (info.nparams + index))
    (show 1 + field + major ≤ 1 + nextField + nextMajor by omega)
  simp only [Nat.mul_assoc] at linear
  unfold projectionDependencyReserve
  omega

theorem firstProjectionDependencyWeight_four_bound
    {env : VEnv} {name : Lean.Name} {info : VProjectionInfo}
    (registered : env.projections name info)
    (parameters : info.nparams = 2) (indices : info.nindices = 0)
    (fieldBound : nextField ≤ 4 * field) (majorBound : nextMajor ≤ 4 * major) :
    2 + nextField + nextMajor +
      (projectionDependencyReserve registered 0 header nextField nextMajor +
        parameterDependencyReserve 2 header equalities nextField nextMajor +
        routedParameterDependencyReserve 2 header equalities nextField nextMajor) ≤
    256 * (2 + field + major +
      (projectionDependencyReserve registered 0 header field major +
        parameterDependencyReserve 2 header equalities field major +
        routedParameterDependencyReserve 2 header equalities field major)) := by
  have projection := projectionDependencyReserve_fields_mono
    (index := 0) (header := header) registered fieldBound majorBound
  have parameter := parameterDependencyReserve_mono (count := 2)
    (Nat.le_refl header) (Nat.le_refl equalities) fieldBound majorBound
  have route := routedParameterDependencyReserve_mono (count := 2)
    (Nat.le_refl header) (Nat.le_refl equalities) fieldBound majorBound
  have scale := firstProjectionDependencyWeight_joint_four
    (header := header) (equalities := equalities) (field := field) (major := major)
    registered parameters indices
  omega

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
