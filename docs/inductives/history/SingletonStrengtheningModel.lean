import Lean

/-!
Run with `lake env lean docs/inductives/history/SingletonStrengtheningModel.lean`.

Semantic calculations for STRENGTHENING.md, using Lean as the metatheory.
This verifies the finite group action and constructor origins, recursor beta
and naturality for arbitrary fibers with object transport, and the distinct
outputs of the two recursors. The full groupoid/universe interpretation and
raw-syntax soundness theorem are not implemented by this file. It is not
imported by the checker or theory.
-/
namespace DependentSingletonC3Countermodel

abbrev C3 := Fin 3
abbrev Pair := C3 × C3

def add (x y : C3) : C3 := ⟨(x.val + y.val) % 3, Nat.mod_lt _ (by decide)⟩
def shift (g : C3) (x : Pair) : Pair := (add g x.1, add g x.2)
abbrev P (v : C3) : Prop := v ≠ 2

def mI (v : C3) : C3 := if v == 0 then 0 else 2
def mJ (v : C3) : C3 := if v == 2 then 2 else 1
def iTuple (v : C3) : Pair := (v, mI v)
def jTuple (v : C3) : Pair := (v, mJ v)

-- The regular diagonal action is free, including both supported orbits.
theorem action_free : ∀ g h x y : C3, shift g (x, y) = shift h (x, y) → g = h := by
  decide

-- Each source context is the discrete two-point P subset.
-- Each constructor map hits two different orbits, so is fully faithful.
theorem i_origins_separate :
    ∀ g : C3, shift g (iTuple 0) ≠ iTuple 1 := by decide

theorem j_origins_separate :
    ∀ g : C3, shift g (jTuple 0) ≠ jTuple 1 := by decide

-- Each supported point has exactly one constructor origin and connecting g.
def ISupported (x : Pair) : Prop := ∃ v : C3, P v ∧ ∃ g : C3, shift g (iTuple v) = x
def JSupported (x : Pair) : Prop := ∃ v : C3, P v ∧ ∃ g : C3, shift g (jTuple v) = x

theorem i_unique_origin :
    ∀ v v' g g' : C3,
      P v → P v' → shift g (iTuple v) = shift g' (iTuple v') →
      v = v' ∧ g = g' := by decide

theorem j_unique_origin :
    ∀ v v' g g' : C3,
      P v → P v' → shift g (jTuple v) = shift g' (jTuple v') →
      v = v' ∧ g = g' := by decide

theorem target_i : shift 2 (iTuple 0) = iTuple 2 := by decide
theorem target_j : shift 1 (jTuple 1) = jTuple 2 := by decide
theorem target_common : iTuple 2 = jTuple 2 := by decide

theorem i_at_bad : ISupported (iTuple 2) :=
  ⟨0, by decide, 2, target_i⟩
theorem j_at_bad : JSupported (jTuple 2) :=
  ⟨1, by decide, 1, target_j⟩
theorem source_proof_missing : ¬ P 2 := by decide

-- Distinct branch outputs K(0) and K(1), sampled as bits here; in the
-- groupoid-universe model choose respectively the empty and terminal types.
def k (v : C3) : Bool := v == 1

-- Origin uniqueness forces these outputs at the common target.
theorem target_outputs_distinct : k 0 ≠ k 1 := by decide

-- At every P-admissible input v, the point is the literal constructor point.
-- The origin used by the large eliminator is v in both families.
theorem admissible_beta_i :
    ∀ v : C3, P v → shift 0 (iTuple v) = iTuple v := by decide

theorem admissible_beta_j :
    ∀ v : C3, P v → shift 0 (jTuple v) = jTuple v := by decide

#print axioms action_free
#print axioms i_unique_origin
#print axioms j_unique_origin
#print axioms i_at_bad
#print axioms j_at_bad
#print axioms target_outputs_distinct

/- Explicit origins and coherent connecting shifts. -/

def sub (x y : C3) : C3 := ⟨(x.val + 3 - y.val) % 3, Nat.mod_lt _ (by decide)⟩
def delta (x : Pair) : C3 := sub x.2 x.1
abbrev Supported (x : Pair) : Prop := delta x ≠ 2

def originI (x : Pair) : C3 := if delta x == 0 then 0 else 1
def originJ (x : Pair) : C3 := if delta x == 0 then 1 else 0
def shiftToI (x : Pair) : C3 := sub x.1 (originI x)
def shiftToJ (x : Pair) : C3 := sub x.1 (originJ x)

theorem shift_zero : ∀ x y : C3, shift 0 (x, y) = (x, y) := by decide

theorem shift_comp : ∀ g h x y : C3,
    shift h (shift g (x, y)) = shift (add h g) (x, y) := by decide

theorem delta_shift : ∀ g x y : C3, delta (shift g (x, y)) = delta (x, y) := by decide

theorem support_shift (g : C3) (x : Pair) (hx : Supported x) : Supported (shift g x) := by
  rcases x with ⟨x, y⟩
  change delta (shift g (x, y)) ≠ 2
  rw [delta_shift]
  exact hx

theorem support_i_iff : ∀ x y : C3, ISupported (x, y) ↔ Supported (x, y) := by
  unfold ISupported
  decide

theorem support_j_iff : ∀ x y : C3, JSupported (x, y) ↔ Supported (x, y) := by
  unfold JSupported
  decide

theorem originI_valid : ∀ x y : C3, P (originI (x, y)) := by decide
theorem originJ_valid : ∀ x y : C3, P (originJ (x, y)) := by decide

theorem originI_shift : ∀ g x y : C3, originI (shift g (x, y)) = originI (x, y) := by decide
theorem originJ_shift : ∀ g x y : C3, originJ (shift g (x, y)) = originJ (x, y) := by decide

theorem shiftToI_comp : ∀ g x y : C3, shiftToI (shift g (x, y)) = add g (shiftToI (x, y)) := by decide
theorem shiftToJ_comp : ∀ g x y : C3, shiftToJ (shift g (x, y)) = add g (shiftToJ (x, y)) := by decide

theorem replayI : ∀ x y : C3, Supported (x, y) →
    shift (shiftToI (x, y)) (iTuple (originI (x, y))) = (x, y) := by decide

theorem replayJ : ∀ x y : C3, Supported (x, y) →
    shift (shiftToJ (x, y)) (jTuple (originJ (x, y))) = (x, y) := by decide

theorem ctorI_support : ∀ v : C3, P v → Supported (iTuple v) := by decide
theorem ctorJ_support : ∀ v : C3, P v → Supported (jTuple v) := by decide

theorem originI_beta : ∀ v : C3, P v → originI (iTuple v) = v := by decide
theorem originJ_beta : ∀ v : C3, P v → originJ (jTuple v) = v := by decide

theorem shiftToI_beta : ∀ v : C3, P v → shiftToI (iTuple v) = 0 := by decide
theorem shiftToJ_beta : ∀ v : C3, P v → shiftToJ (jTuple v) = 0 := by decide


/- A bounded transport interface over the six supported index objects.
This checks arbitrary fibers and their object transport, not internal fiber
morphisms, universes, raw syntax, or soundness of the full equality judgment. -/

abbrev Point := {x : Pair // Supported x}
abbrev Origin := {v : C3 // P v}
abbrev Arrow (x y : Point) := {g : C3 // shift g x.val = y.val}

def idArrow (x : Point) : Arrow x x :=
  ⟨0, shift_zero x.val.1 x.val.2⟩

def compArrow {x y z : Point} (a : Arrow x y) (b : Arrow y z) : Arrow x z :=
  ⟨add b.val a.val, by
    calc
      shift (add b.val a.val) x.val = shift b.val (shift a.val x.val) :=
        (shift_comp a.val b.val x.val.1 x.val.2).symm
      _ = shift b.val y.val := congrArg (shift b.val) a.property
      _ = z.val := b.property⟩

universe u

structure TransportFamily where
  obj : Point → Sort u
  map : {x y : Point} → Arrow x y → obj x → obj y
  map_id : ∀ (x : Point) (v : obj x), map (idArrow x) v = v
  map_comp : ∀ {x y z : Point} (a : Arrow x y) (b : Arrow y z) (v : obj x),
    map b (map a v) = map (compArrow a b) v

-- The finite coherence data proved above, for either I or J.
structure Scheme where
  ctor : Origin → Point
  origin : Point → Origin
  connect : (x : Point) → Arrow (ctor (origin x)) x
  origin_ctor : ∀ o : Origin, origin (ctor o) = o
  connect_ctor : ∀ o : Origin, (connect (ctor o)).val = 0
  origin_arrow : ∀ {x y : Point}, Arrow x y → origin x = origin y
  connect_arrow : ∀ {x y : Point} (a : Arrow x y),
    (connect y).val = add a.val (connect x).val

private theorem map_branch_congr (M : TransportFamily) (ctor : Origin → Point)
    (s : (o : Origin) → M.obj (ctor o))
    {o o' : Origin} (ho : o = o') {x : Point}
    (a : Arrow (ctor o) x) (b : Arrow (ctor o') x) (hab : a.val = b.val) :
    M.map a (s o) = M.map b (s o') := by
  cases ho
  have h : a = b := Subtype.ext hab
  cases h
  rfl

def extend (S : Scheme) (M : TransportFamily)
    (s : (o : Origin) → M.obj (S.ctor o)) (x : Point) : M.obj x :=
  M.map (S.connect x) (s (S.origin x))

theorem extend_beta (S : Scheme) (M : TransportFamily)
    (s : (o : Origin) → M.obj (S.ctor o)) (o : Origin) :
    extend S M s (S.ctor o) = s o := by
  exact (map_branch_congr M S.ctor s (S.origin_ctor o)
    (S.connect (S.ctor o)) (idArrow (S.ctor o)) (S.connect_ctor o)).trans
      (M.map_id (S.ctor o) (s o))

theorem extend_natural (S : Scheme) (M : TransportFamily)
    (s : (o : Origin) → M.obj (S.ctor o))
    {x y : Point} (a : Arrow x y) :
    M.map a (extend S M s x) = extend S M s y := by
  unfold extend
  rw [M.map_comp]
  exact map_branch_congr M S.ctor s (S.origin_arrow a)
    (compArrow (S.connect x) a) (S.connect y) (S.connect_arrow a).symm

def schemeI : Scheme where
  ctor o := ⟨iTuple o.val, ctorI_support o.val o.property⟩
  origin x := ⟨originI x.val, originI_valid x.val.1 x.val.2⟩
  connect x := ⟨shiftToI x.val, replayI x.val.1 x.val.2 x.property⟩
  origin_ctor o := Subtype.ext (originI_beta o.val o.property)
  connect_ctor o := shiftToI_beta o.val o.property
  origin_arrow := by
    intro x y a
    apply Subtype.ext
    change originI x.val = originI y.val
    rw [← a.property]
    exact (originI_shift a.val x.val.1 x.val.2).symm
  connect_arrow := by
    intro x y a
    change shiftToI y.val = add a.val (shiftToI x.val)
    exact (congrArg shiftToI a.property).symm.trans
      (shiftToI_comp a.val x.val.1 x.val.2)

def schemeJ : Scheme where
  ctor o := ⟨jTuple o.val, ctorJ_support o.val o.property⟩
  origin x := ⟨originJ x.val, originJ_valid x.val.1 x.val.2⟩
  connect x := ⟨shiftToJ x.val, replayJ x.val.1 x.val.2 x.property⟩
  origin_ctor o := Subtype.ext (originJ_beta o.val o.property)
  connect_ctor o := shiftToJ_beta o.val o.property
  origin_arrow := by
    intro x y a
    apply Subtype.ext
    change originJ x.val = originJ y.val
    rw [← a.property]
    exact (originJ_shift a.val x.val.1 x.val.2).symm
  connect_arrow := by
    intro x y a
    change shiftToJ y.val = add a.val (shiftToJ x.val)
    exact (congrArg shiftToJ a.property).symm.trans
      (shiftToJ_comp a.val x.val.1 x.val.2)

-- Both concrete recursors satisfy beta and naturality for every Sort u fiber
-- family carrying the given strict transport, and for every constructor branch.
example (M : TransportFamily) (s : (o : Origin) → M.obj (schemeI.ctor o))
    (o : Origin) : extend schemeI M s (schemeI.ctor o) = s o :=
  extend_beta schemeI M s o

example (M : TransportFamily) (s : (o : Origin) → M.obj (schemeJ.ctor o))
    {x y : Point} (a : Arrow x y) :
    M.map a (extend schemeJ M s x) = extend schemeJ M s y :=
  extend_natural schemeJ M s a

#print axioms schemeI
#print axioms schemeJ
#print axioms extend_beta
#print axioms extend_natural

def constantFamily (α : Sort u) : TransportFamily where
  obj _ := α
  map _ v := v
  map_id _ _ := rfl
  map_comp _ _ _ := rfl

def separatingPoint : Point := ⟨(2, 2), by decide⟩

def typeBranch (o : Origin) : Type := if o.val == 0 then Empty else Unit

-- These use the actual generic recursor extension, not an independent
-- table of expected outputs. The motive is the constant universe Type.
theorem left_type_at_point :
    extend schemeI (constantFamily Type) typeBranch separatingPoint = Empty := rfl

theorem right_type_at_point :
    extend schemeJ (constantFamily Type) typeBranch separatingPoint = Unit := rfl

theorem recursor_types_differ :
    extend schemeI (constantFamily Type) typeBranch separatingPoint ≠
      extend schemeJ (constantFamily Type) typeBranch separatingPoint := by
  intro h
  have h : Empty = Unit := h
  exact (Eq.mpr h ()).elim

#print axioms recursor_types_differ

end DependentSingletonC3Countermodel
