import Lean4Lean.Theory.VExpr

namespace Lean4Lean

structure VConstant where
  uvars : Nat
  type : VExpr

structure VDefEq where
  uvars : Nat
  lhs : VExpr
  rhs : VExpr
  type : VExpr

/-- Kernel data needed to type primitive projections.  Unlike a synthesized
eliminator term, this record contains only declaration data: all projection
types are computed from the constructor telescope below. -/
structure VProjectionInfo where
  uvars : Nat
  nparams : Nat
  nindices : Nat
  resultLevel : VLevel
  ctorName : Name
  ctorType : VExpr

structure VProjectionEntry where
  typeName : Name
  info : VProjectionInfo

namespace VProjectionInfo

def instantiateProjectionParameters : VExpr → List VExpr → Option VExpr
  | type, [] => some type
  | .forallE _ body, arg :: args =>
    instantiateProjectionParameters (body.inst arg) args
  | _, _ :: _ => none

def instantiateProjectionFields
    (typeName : Name) (major : VExpr) (wanted current : Nat) :
    Nat → VExpr → Option VExpr
  | 0, _ => none
  | fuel + 1, .forallE domain body =>
    if wanted = current then some domain
    else instantiateProjectionFields typeName major wanted (current + 1) fuel
      (body.inst (.proj typeName current major))
  | _ + 1, _ => none

/-- Instantiate the parameters and walk to a field, replacing each preceding
field binder by the corresponding primitive projection of the major. -/
def fieldType (info : VProjectionInfo) (typeName : Name) (levels : List VLevel)
    (params : List VExpr) (index : Nat) (major : VExpr) : Option VExpr :=
  if levels.length != info.uvars || params.length != info.nparams then
    none
  else do
    let constructorTail ← instantiateProjectionParameters
      (info.ctorType.instL levels) params
    instantiateProjectionFields typeName major index 0 (index + 1)
      constructorTail

private theorem instantiateProjectionParameters_liftN
    (type : VExpr) (params : List VExpr) :
    instantiateProjectionParameters (type.liftN n k)
        (params.map fun param => param.liftN n k) =
      (instantiateProjectionParameters type params).map
        fun result => result.liftN n k := by
  induction params generalizing type with
  | nil => simp [instantiateProjectionParameters]
  | cons param params ih =>
    cases type <;> simp [instantiateProjectionParameters, VExpr.liftN]
    case forallE domain body =>
      rw [← VExpr.liftN_inst_hi]
      exact ih (body.inst param)

private theorem instantiateProjectionFields_liftN (type : VExpr) :
    instantiateProjectionFields typeName (major.liftN n k) wanted current fuel
        (type.liftN n k) =
      (instantiateProjectionFields typeName major wanted current fuel type).map
        fun result => result.liftN n k := by
  induction fuel generalizing type current with
  | zero => simp [instantiateProjectionFields]
  | succ fuel ih =>
    cases type <;> simp [instantiateProjectionFields, VExpr.liftN]
    case forallE domain body =>
      split <;> rename_i selected
      · simp
      · change instantiateProjectionFields typeName (major.liftN n k) wanted
          (current + 1) fuel
            ((body.liftN n (k + 1)).inst
              ((VExpr.proj typeName current major).liftN n k)) = _
        rw [← VExpr.liftN_inst_hi]
        exact ih (current := current + 1)
          (body.inst (.proj typeName current major))

theorem fieldType_liftN (info : VProjectionInfo) (hctor : info.ctorType.Closed) :
    info.fieldType typeName levels (params.map fun param => param.liftN n k)
        index (major.liftN n k) =
      (info.fieldType typeName levels params index major).map
        fun result => result.liftN n k := by
  simp only [fieldType, List.length_map]
  split <;> rename_i valid
  · rfl
  ·
    have hclosed : (info.ctorType.instL levels).liftN n k =
        info.ctorType.instL levels :=
      hctor.instL.liftN_eq (Nat.zero_le _)
    conv => lhs; rw [← hclosed]
    rw [instantiateProjectionParameters_liftN]
    cases instantiateProjectionParameters (info.ctorType.instL levels) params <;>
      simp [instantiateProjectionFields_liftN]

private theorem instantiateProjectionParameters_instL
    (type : VExpr) (params : List VExpr) :
    instantiateProjectionParameters (type.instL substitution)
        (params.map fun param => param.instL substitution) =
      (instantiateProjectionParameters type params).map
        fun result => result.instL substitution := by
  induction params generalizing type with
  | nil => simp [instantiateProjectionParameters]
  | cons param params ih =>
    cases type <;> simp [instantiateProjectionParameters, VExpr.instL]
    case forallE domain body =>
      rw [← VExpr.instL_instN]
      exact ih (body.inst param)

private theorem instantiateProjectionFields_instL (type : VExpr) :
    instantiateProjectionFields typeName (major.instL substitution) wanted current fuel
        (type.instL substitution) =
      (instantiateProjectionFields typeName major wanted current fuel type).map
        fun result => result.instL substitution := by
  induction fuel generalizing type current with
  | zero => simp [instantiateProjectionFields]
  | succ fuel ih =>
    cases type <;> simp [instantiateProjectionFields, VExpr.instL]
    case forallE domain body =>
      split <;> rename_i selected
      · simp
      · change instantiateProjectionFields typeName (major.instL substitution) wanted
            (current + 1) fuel
            ((body.instL substitution).inst
              ((VExpr.proj typeName current major).instL substitution)) = _
        rw [← VExpr.instL_instN]
        exact ih (current := current + 1)
          (body.inst (.proj typeName current major))

theorem fieldType_instL (info : VProjectionInfo) :
    info.fieldType typeName (levels.map fun level => level.inst substitution)
        (params.map fun param => param.instL substitution) index
        (major.instL substitution) =
      (info.fieldType typeName levels params index major).map
        fun result => result.instL substitution := by
  simp only [fieldType, List.length_map]
  split <;> rename_i valid
  · rfl
  · rw [← VExpr.instL_instL, instantiateProjectionParameters_instL]
    cases instantiateProjectionParameters (info.ctorType.instL levels) params <;>
      simp [instantiateProjectionFields_instL]

private theorem instantiateProjectionParameters_inst_some
    (type : VExpr) (params : List VExpr)
    (H : instantiateProjectionParameters type params = some result) :
    instantiateProjectionParameters (type.inst value k)
        (params.map fun param => param.inst value k) =
      some (result.inst value k) := by
  induction params generalizing type result with
  | nil =>
    simp [instantiateProjectionParameters] at H ⊢
    subst result
    rfl
  | cons param params ih =>
    cases type <;> simp [instantiateProjectionParameters] at H
    case forallE domain body =>
      simp [instantiateProjectionParameters, VExpr.inst]
      rw [← VExpr.inst0_inst_hi]
      exact ih (body.inst param) H

private theorem instantiateProjectionFields_inst_some (type : VExpr)
    (H : instantiateProjectionFields typeName major wanted current fuel type =
      some result) :
    instantiateProjectionFields typeName (major.inst value k) wanted current fuel
        (type.inst value k) = some (result.inst value k) := by
  induction fuel generalizing type current result with
  | zero => simp [instantiateProjectionFields] at H
  | succ fuel ih =>
    cases type <;> simp [instantiateProjectionFields] at H
    case forallE domain body =>
      split at H <;> rename_i selected
      · cases H
        simp [instantiateProjectionFields, VExpr.inst, selected]
      · simp [instantiateProjectionFields, VExpr.inst, selected]
        change instantiateProjectionFields typeName (major.inst value k) wanted
          (current + 1) fuel
          ((body.inst value (k + 1)).inst
            ((VExpr.proj typeName current major).inst value k)) = _
        rw [← VExpr.inst0_inst_hi]
        exact ih (body.inst (.proj typeName current major)) H

theorem fieldType_inst_some (info : VProjectionInfo)
    (hctor : info.ctorType.Closed)
    (H : info.fieldType typeName levels params index major = some result) :
    info.fieldType typeName levels (params.map fun param => param.inst value k)
        index (major.inst value k) = some (result.inst value k) := by
  unfold fieldType at H ⊢
  simp only [List.length_map]
  split <;> rename_i valid
  · rw [if_pos valid] at H
    contradiction
  · rw [if_neg valid] at H
    cases htail : instantiateProjectionParameters
        (info.ctorType.instL levels) params with
    | none => simp [htail] at H
    | some tail =>
      have htail' := instantiateProjectionParameters_inst_some
        (type := info.ctorType.instL levels) (params := params)
        (result := tail) (value := value) (k := k) htail
      have hclosed : (info.ctorType.instL levels).inst value k =
          info.ctorType.instL levels :=
        hctor.instL.instN_eq (Nat.zero_le _)
      rw [hclosed] at htail'
      simp only [htail']
      exact instantiateProjectionFields_inst_some
        (typeName := typeName) (major := major) (wanted := index)
        (current := 0) (fuel := index + 1) (type := tail)
        (result := result) (value := value) (k := k)
        (by simpa [htail] using H)

private theorem instantiateProjectionParameters_subst_some
    (type : VExpr) (params : List VExpr)
    (H : instantiateProjectionParameters type params = some result) :
    instantiateProjectionParameters (type.subst substitution)
        (params.map fun param => param.subst substitution) =
      some (result.subst substitution) := by
  induction params generalizing type result with
  | nil =>
    simp [instantiateProjectionParameters] at H ⊢
    subst result
    rfl
  | cons param params ih =>
    cases type <;> simp [instantiateProjectionParameters] at H
    case forallE domain body =>
      simp [instantiateProjectionParameters, VExpr.subst]
      rw [← VExpr.subst_inst]
      exact ih (body.inst param) H

private theorem instantiateProjectionFields_subst_some (type : VExpr)
    (H : instantiateProjectionFields typeName major wanted current fuel type =
      some result) :
    instantiateProjectionFields typeName (major.subst substitution) wanted current fuel
        (type.subst substitution) = some (result.subst substitution) := by
  induction fuel generalizing type current result with
  | zero => simp [instantiateProjectionFields] at H
  | succ fuel ih =>
    cases type <;> simp [instantiateProjectionFields] at H
    case forallE domain body =>
      split at H <;> rename_i selected
      · cases H
        simp [instantiateProjectionFields, VExpr.subst, selected]
      · simp [instantiateProjectionFields, VExpr.subst, selected]
        change instantiateProjectionFields typeName (major.subst substitution) wanted
          (current + 1) fuel
          ((body.subst substitution.lift).inst
            ((VExpr.proj typeName current major).subst substitution)) = _
        rw [← VExpr.subst_inst]
        exact ih (body.inst (.proj typeName current major)) H

theorem fieldType_subst_some (info : VProjectionInfo)
    (hctor : info.ctorType.Closed)
    (H : info.fieldType typeName levels params index major = some result) :
    info.fieldType typeName levels (params.map fun param => param.subst substitution)
        index (major.subst substitution) = some (result.subst substitution) := by
  unfold fieldType at H ⊢
  simp only [List.length_map]
  split <;> rename_i valid
  · rw [if_pos valid] at H
    contradiction
  · rw [if_neg valid] at H
    cases htail : instantiateProjectionParameters
        (info.ctorType.instL levels) params with
    | none => simp [htail] at H
    | some tail =>
      have htail' := instantiateProjectionParameters_subst_some
        (type := info.ctorType.instL levels) (params := params)
        (result := tail) (substitution := substitution) htail
      have hclosed : (info.ctorType.instL levels).subst substitution =
          info.ctorType.instL levels :=
        hctor.instL.subst_eq .zero
      rw [hclosed] at htail'
      simp only [htail']
      exact instantiateProjectionFields_subst_some
        (typeName := typeName) (major := major) (wanted := index)
        (current := 0) (fuel := index + 1) (type := tail)
        (result := result) (substitution := substitution)
        (by simpa [htail] using H)

end VProjectionInfo

@[ext] structure VEnv where
  constants : Name → Option VConstant
  defeqs : VDefEq → Prop
  projections : Name → VProjectionInfo → Prop := fun _ _ => False

def VEnv.empty : VEnv where
  constants _ := none
  defeqs _ := False
  projections _ _ := False

instance : EmptyCollection VEnv := ⟨.empty⟩

def VEnv.contains (env : VEnv) (name : Name) := ∃ ci, env.constants name = some ci

def VEnv.addConst (env : VEnv) (name : Name) (ci : VConstant) : Option VEnv :=
  match env.constants name with
  | some _ => none
  | none => some { env with constants := fun n => if name = n then some ci else env.constants n }

def VEnv.addDefEq (env : VEnv) (df : VDefEq) : VEnv :=
  { env with defeqs := fun x => x = df ∨ env.defeqs x }

def VEnv.addProjection (env : VEnv) (entry : VProjectionEntry) : VEnv :=
  { env with projections := fun name info =>
      (name = entry.typeName ∧ info = entry.info) ∨ env.projections name info }

def VEnv.addProjections : VEnv → List VProjectionEntry → VEnv
  | env, [] => env
  | env, entry :: entries => (env.addProjection entry).addProjections entries

theorem VEnv.addProjections_iff {env : VEnv} {entries : List VProjectionEntry} :
    (env.addProjections entries).projections name info ↔
      (∃ entry ∈ entries, name = entry.typeName ∧ info = entry.info) ∨
        env.projections name info := by
  induction entries generalizing env with
  | nil => simp [VEnv.addProjections]
  | cons entry entries ih =>
    rw [VEnv.addProjections, ih]
    simp [VEnv.addProjection, or_assoc, or_left_comm]

@[simp] theorem VEnv.addProjection_constants (env : VEnv) (entry : VProjectionEntry) :
    (env.addProjection entry).constants = env.constants := rfl

@[simp] theorem VEnv.addProjection_defeqs (env : VEnv) (entry : VProjectionEntry) :
    (env.addProjection entry).defeqs = env.defeqs := rfl

@[simp] theorem VEnv.addProjections_constants (env : VEnv)
    (entries : List VProjectionEntry) :
    (env.addProjections entries).constants = env.constants := by
  induction entries generalizing env with
  | nil => rfl
  | cons entry entries ih => exact ih (env := env.addProjection entry)

@[simp] theorem VEnv.addProjections_defeqs (env : VEnv)
    (entries : List VProjectionEntry) :
    (env.addProjections entries).defeqs = env.defeqs := by
  induction entries generalizing env with
  | nil => rfl
  | cons entry entries ih => exact ih (env := env.addProjection entry)

structure VEnv.LE (env1 env2 : VEnv) : Prop where
  constants : env1.constants n = some a → env2.constants n = some a
  defeqs : env1.defeqs df → env2.defeqs df
  projections : env1.projections n p → env2.projections n p

instance : LE VEnv := ⟨VEnv.LE⟩

theorem VEnv.LE.rfl {env : VEnv} : env ≤ env := ⟨id, id, id⟩

theorem VEnv.LE.trans {a b c : VEnv} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2, h2.3 ∘ h1.3⟩

theorem VEnv.addConst_le {env env' : VEnv}
    (h : env.addConst n ci = some env') : env ≤ env' := by
  unfold addConst at h; split at h <;> cases h
  exact ⟨fun _ => by simp; split <;> simp_all, by simp [*], id⟩

theorem VEnv.addConst_self {env env' : VEnv}
    (h : env.addConst n ci = some env') :
    env'.constants n = some ci := by
  unfold addConst at h; split at h <;> cases h; simp

theorem VEnv.addConst_constants_of_ne {env env' : VEnv}
    (h : env.addConst n ci = some env') (hne : n ≠ p) :
    env'.constants p = env.constants p := by
  unfold addConst at h
  split at h <;> cases h
  simp [hne]

theorem VEnv.addConst_projections {env env' : VEnv}
    (h : env.addConst n ci = some env') :
    env'.projections = env.projections := by
  unfold addConst at h
  split at h <;> cases h
  rfl

theorem VEnv.addDefEq_le {env : VEnv} : env ≤ env.addDefEq df :=
  ⟨id, .inr, id⟩

theorem VEnv.addDefEq_self {env : VEnv} :
    (env.addDefEq df).defeqs df := .inl rfl

theorem VEnv.addProjection_le {env : VEnv} {entry : VProjectionEntry} :
    env ≤ env.addProjection entry where
  constants := id
  defeqs := id
  projections hinfo := Or.inr hinfo

theorem VEnv.addProjections_le {env : VEnv} {entries : List VProjectionEntry} :
    env ≤ env.addProjections entries := by
  induction entries generalizing env with
  | nil => exact .rfl
  | cons entry entries ih => exact addProjection_le.trans ih

theorem VEnv.addProjection_mono {env₁ env₂ : VEnv} {entry : VProjectionEntry}
    (H : env₁ ≤ env₂) :
    env₁.addProjection entry ≤ env₂.addProjection entry where
  constants := H.constants
  defeqs := H.defeqs
  projections := fun hinfo => hinfo.elim Or.inl (Or.inr ∘ H.projections)

theorem VEnv.addProjections_mono {env₁ env₂ : VEnv}
    {entries : List VProjectionEntry} (H : env₁ ≤ env₂) :
    env₁.addProjections entries ≤ env₂.addProjections entries := by
  induction entries generalizing env₁ env₂ with
  | nil => exact H
  | cons entry entries ih => exact ih (addProjection_mono H)
