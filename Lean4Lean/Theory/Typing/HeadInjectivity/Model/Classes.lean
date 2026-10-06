import Lean4Lean.Theory.Typing.TypeChain

/-! # Declarative classes of the glued observation model (milestone M0)

Classes of terms in a fixed *target context* `Δ` (`docs/inductives/PHASE1B_NOTES.md`,
sections 2.1 and 9.1):

* `TyCls Δ A`: the type class of `A`, the terms related to `A` by a chain of sort-typed
  definitional equalities (`TypeChain`), together with `A` itself;
* `ElCls Δ D a`: the element class of `a` at a set `D` of types, the closure of `a` under
  definitional equalities typed at some member of `D`;
* `TypedTyCls`, `TypedElCls`: the classes of typed terms.

The **collapse lemma** (`ElCls.collapse`) turns membership of an element class at a type
class `TyCls Δ X₀` into one definitional equality at `X₀`: every link is transported to
`X₀` along a chain (`TypeChain.defeqDF`) and links at one type compose by `trans`. This is
why classes are typed.

The **anchored class lemma** (`SubstEq.of_mem_cls`, `ElCls.subst_eq_of_mem_cls`,
`TyCls.subst_eq_of_mem_cls`): replacing each value of a typed substitution `σ` by a member
of its class gives a substitution definitionally equal to `σ`, so the classes of every
typed term agree under the two.

Deviation from section 9.1 (recorded in section 10 of the notes): the model built on this
file (`Obs.lean`, `Interp.lean`) uses valuations consisting of an *anchor* substitution
together with observation sets, and computes classes from the anchor, rather than
valuations `List (Set VExpr × Set Ob)` with classes taken as unions over representatives.
The union-over-representatives classes `clsOf`/`tyClsOf` are still defined below, and
`clsOf_anchored`/`tyClsOf_anchored` show that at anchored typed valuations they are the
anchored classes, so the two presentations agree wherever the model is used.

Sets are predicates (`VExpr → Prop`); this development does not use Mathlib. -/

namespace Lean4Lean
namespace VEnv
namespace Model

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- A sort-typed definitional equality in `Δ`. -/
def TyLink (A B : VExpr) : Prop := ∃ u, env.IsDefEq U Δ A B (.sort u)

/-- The type class of `A`: `A` itself and everything chain-related to it. -/
def TyCls (A : VExpr) : VExpr → Prop := fun B => A = B ∨ env.TypeChain U Δ A B

/-- A definitional equality typed at some member of the set of types `D`. -/
def ElLink (D : VExpr → Prop) (a b : VExpr) : Prop := ∃ X, D X ∧ env.IsDefEq U Δ a b X

/-- The element class of `a` at the set of types `D`. -/
def ElCls (D : VExpr → Prop) (a : VExpr) : VExpr → Prop :=
  fun b => a = b ∨ Relation.TransGen (ElLink env U Δ D) a b

/-- `D` is the type class of a type. -/
def TypedTyCls (D : VExpr → Prop) : Prop :=
  ∃ A u, env.HasType U Δ A (.sort u) ∧ D = TyCls env U Δ A

/-- `c` is the element class, at `D`, of a term typed at a member of `D`. -/
def TypedElCls (D c : VExpr → Prop) : Prop :=
  ∃ a X, D X ∧ env.HasType U Δ a X ∧ c = ElCls env U Δ D a

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

/-! ## Type classes -/

theorem TyCls.self : TyCls env U Δ A A := .inl rfl

theorem TyCls.mem_iff : TyCls env U Δ A B ↔ A = B ∨ env.TypeChain U Δ A B := .rfl

/-- For a typed `A`, the type class is exactly the chain-related terms. -/
theorem TyCls.mem_iff_chain (hA : env.HasType U Δ A (.sort u)) :
    TyCls env U Δ A B ↔ env.TypeChain U Δ A B :=
  ⟨fun | .inl h => h ▸ .refl hA | .inr h => h, .inr⟩

theorem TyCls.symm (h : TyCls env U Δ A B) : TyCls env U Δ B A := by
  rcases h with rfl | h
  · exact .self
  · exact .inr h.symm

theorem TyCls.trans (h1 : TyCls env U Δ A B) (h2 : TyCls env U Δ B C) : TyCls env U Δ A C := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact .inr h1
  · exact .inr (h1.trans h2)

/-- Two members of one type class have the same class. -/
theorem TyCls.eq_of_mem (h : TyCls env U Δ A B) : TyCls env U Δ B = TyCls env U Δ A :=
  funext fun _ => propext ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩

/-- A single derivable sort-typed equality identifies the type classes. -/
theorem TyCls.eq_of_defeq (h : env.IsDefEq U Δ A B (.sort u)) :
    TyCls env U Δ A = TyCls env U Δ B :=
  (TyCls.eq_of_mem (.inr (.single h))).symm

/-- Transport a definitional equality from a member of a type class to its base. -/
theorem TyCls.defeq (hX : TyCls env U Δ X₀ X) (h : env.IsDefEq U Δ e₁ e₂ X) :
    env.IsDefEq U Δ e₁ e₂ X₀ := by
  rcases hX with rfl | hX
  · exact h
  · exact hX.symm.defeqDF h

/-- Transport a definitional equality from the base of a type class to a member. -/
theorem TyCls.defeq' (hX : TyCls env U Δ X₀ X) (h : env.IsDefEq U Δ e₁ e₂ X₀) :
    env.IsDefEq U Δ e₁ e₂ X := by
  rcases hX with rfl | hX
  · exact h
  · exact hX.defeqDF h

theorem TypedTyCls.of_hasType (h : env.HasType U Δ A (.sort u)) :
    TypedTyCls env U Δ (TyCls env U Δ A) := ⟨_, _, h, rfl⟩

/-! ## Element classes -/

theorem ElLink.symm (h : ElLink env U Δ D a b) : ElLink env U Δ D b a :=
  let ⟨X, hX, h⟩ := h; ⟨X, hX, h.symm⟩

theorem ElCls.self : ElCls env U Δ D a a := .inl rfl

theorem ElCls.of_link (h : ElLink env U Δ D a b) : ElCls env U Δ D a b := .inr (.single h)

theorem ElCls.symm (h : ElCls env U Δ D a b) : ElCls env U Δ D b a := by
  rcases h with rfl | h
  · exact .self
  · refine .inr ?_
    induction h with
    | single h => exact .single h.symm
    | tail _ h ih => exact (Relation.TransGen.single h.symm).trans ih

theorem ElCls.trans (h1 : ElCls env U Δ D a b) (h2 : ElCls env U Δ D b c) :
    ElCls env U Δ D a c := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact .inr h1
  · exact .inr (h1.trans h2)

/-- Two members of one element class have the same class. -/
theorem ElCls.eq_of_mem (h : ElCls env U Δ D a b) : ElCls env U Δ D b = ElCls env U Δ D a :=
  funext fun _ => propext ⟨fun h' => h.trans h', fun h' => h.symm.trans h'⟩

/-- A single derivable equality at a member of `D` identifies the element classes. -/
theorem ElCls.eq_of_defeq (hX : D X) (h : env.IsDefEq U Δ a b X) :
    ElCls env U Δ D a = ElCls env U Δ D b :=
  (ElCls.eq_of_mem (.of_link ⟨X, hX, h⟩)).symm

/-- **Collapse lemma**: membership of an element class at a type class `TyCls Δ X₀`, from
a term typed at a member of the class, is one definitional equality at `X₀`. -/
theorem ElCls.collapse (ha : env.HasType U Δ a X) (hX : TyCls env U Δ X₀ X)
    (hb : ElCls env U Δ (TyCls env U Δ X₀) a b) : env.IsDefEq U Δ a b X₀ := by
  have ha0 : env.IsDefEq U Δ a a X₀ := hX.defeq ha
  rcases hb with rfl | hb
  · exact ha0
  induction hb with
  | single h => let ⟨_, hX', h⟩ := h; exact hX'.defeq h
  | tail _ h ih => let ⟨_, hX', h⟩ := h; exact ih.trans (hX'.defeq h)

/-- Members of a typed element class at `TyCls Δ X₀` are definitionally equal to its
witness at `X₀`, and the class is the class of each of its members. -/
theorem TypedElCls.mem (hc : TypedElCls env U Δ (TyCls env U Δ X₀) c) (hy : c y) :
    ∃ a, env.IsDefEq U Δ a y X₀ ∧ c = ElCls env U Δ (TyCls env U Δ X₀) a ∧
      c = ElCls env U Δ (TyCls env U Δ X₀) y := by
  obtain ⟨a, X, hX, ha, rfl⟩ := hc
  exact ⟨a, ElCls.collapse ha hX hy, rfl, (ElCls.eq_of_mem hy).symm⟩

theorem TypedElCls.hasType (hc : TypedElCls env U Δ (TyCls env U Δ X₀) c) (hy : c y) :
    env.HasType U Δ y X₀ :=
  let ⟨_, h, _⟩ := hc.mem hy; h.hasType.2

theorem TypedElCls.nonempty (hc : TypedElCls env U Δ D c) : ∃ y, c y :=
  let ⟨a, _, _, _, e⟩ := hc; ⟨a, e ▸ .self⟩

theorem TypedElCls.of_hasType (ha : env.HasType U Δ a X₀) :
    TypedElCls env U Δ (TyCls env U Δ X₀) (ElCls env U Δ (TyCls env U Δ X₀) a) :=
  ⟨a, X₀, .self, ha, rfl⟩

/-- Membership of the class of the anchor `a` at `TyCls X₀`. -/
theorem ElCls.mem_of_defeq (h : env.IsDefEq U Δ a b X₀) :
    ElCls env U Δ (TyCls env U Δ X₀) a b := .of_link ⟨X₀, .self, h⟩

theorem TypedElCls.congr_D (hD : D = D') (h : TypedElCls env U Δ D c) :
    TypedElCls env U Δ D' c := hD ▸ h

/-! ## Substitutions with symmetric data -/

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- A pair of related substitutions is related in the other order. -/
theorem SubstEq.symm (W : Ctx.SubstEq env U Δ σ σ' Γ) : Ctx.SubstEq env U Δ σ' σ Γ := by
  induction W with
  | nil => exact .nil
  | @cons σ σ' Γ A u W hA hhead ih =>
    refine .cons ih hA ?_
    have hAA := hA.substDF henv W.wf hΔ W
    exact .defeqDF hAA hhead.symm

/-- The right substitution of a related pair is typed. -/
theorem SubstEq.right (W : Ctx.SubstEq env U Δ σ σ' Γ) : Ctx.SubstEq env U Δ σ' σ' Γ :=
  (SubstEq.symm henv hΔ W).left

/-- Composition of related pairs along a common middle. -/
theorem SubstEq.trans (W1 : Ctx.SubstEq env U Δ σ₁ σ₂ Γ) (W2 : Ctx.SubstEq env U Δ σ₂ σ₃ Γ) :
    Ctx.SubstEq env U Δ σ₁ σ₃ Γ := by
  induction W1 generalizing σ₃ with
  | nil => exact .nil
  | @cons σ₁ σ₂ Γ A u W1 hA hhead ih =>
    cases W2 with
    | cons W2 _ hhead2 =>
      refine .cons (ih W2) hA (hhead.trans ?_)
      exact .defeqDF (hA.substDF henv W1.wf hΔ W1).symm hhead2

end

/-! ## The anchored class lemma -/

/-- If each value of `σ'` lies in the class of the corresponding value of a typed anchor
`σ` (at the type class of the substituted context entry), the two substitutions are
related. -/
theorem SubstEq.of_mem_cls (W : Ctx.SubstEq env U Δ σ σ Γ)
    (h : ∀ i A, Lookup Γ i A → ElCls env U Δ (TyCls env U Δ (A.subst σ)) (σ i) (σ' i)) :
    Ctx.SubstEq env U Δ σ σ' Γ := by
  induction Γ generalizing σ σ' with
  | nil => exact .nil
  | cons B Γ ih =>
    cases W with
    | cons W hB hhead =>
      refine .cons (ih W fun i A hL => ?_) hB ?_
      · have := h (i+1) A.lift (.succ hL)
        rwa [VExpr.lift_subst] at this
      · have := h 0 B.lift .zero
        rw [VExpr.lift_subst] at this
        exact ElCls.collapse hhead .self this

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- Classes of a typed term agree at an anchor and at any substitution by class members. -/
theorem ElCls.subst_eq_of_mem_cls (W : Ctx.SubstEq env U Δ σ σ Γ)
    (h : ∀ i A, Lookup Γ i A → ElCls env U Δ (TyCls env U Δ (A.subst σ)) (σ i) (σ' i))
    (ht : env.HasType U Γ t T) (hD : D (T.subst σ)) :
    ElCls env U Δ D (t.subst σ) = ElCls env U Δ D (t.subst σ') :=
  ElCls.eq_of_defeq hD (ht.substDF henv W.wf hΔ (SubstEq.of_mem_cls W h))

theorem TyCls.subst_eq_of_mem_cls (W : Ctx.SubstEq env U Δ σ σ Γ)
    (h : ∀ i A, Lookup Γ i A → ElCls env U Δ (TyCls env U Δ (A.subst σ)) (σ i) (σ' i))
    (ht : env.HasType U Γ t (.sort u)) :
    TyCls env U Δ (t.subst σ) = TyCls env U Δ (t.subst σ') :=
  TyCls.eq_of_defeq (ht.substDF henv W.wf hΔ (SubstEq.of_mem_cls W h))

end

/-! ## Union-over-representatives classes

The presentation of section 9.1 of the notes: a valuation assigns a class and a set of
observations to each variable; the class of a term is the union of the classes of its
instances at all representatives. At anchored typed valuations these are the anchored
classes (`clsOf_anchored`, `tyClsOf_anchored`). The observation sets are a parameter `β`
here (instantiated with sets of observations by the model). -/

section
variable (env U Δ)

/-- Representatives of the classes of a valuation. -/
def Reps {β : Type} (ρ : List ((VExpr → Prop) × β)) (σ : VExpr.Subst) : Prop :=
  ∀ i (h : i < ρ.length), (ρ[i]).1 (σ i)

/-- The element class of `t` at `D` under a valuation: the union over representatives. -/
def clsOf {β : Type} (ρ : List ((VExpr → Prop) × β)) (D : VExpr → Prop) (t : VExpr) :
    VExpr → Prop :=
  fun b => ∃ σ, Reps ρ σ ∧ ElCls env U Δ D (t.subst σ) b

/-- The type class of `t` under a valuation: the union over representatives. -/
def tyClsOf {β : Type} (ρ : List ((VExpr → Prop) × β)) (t : VExpr) : VExpr → Prop :=
  fun b => ∃ σ, Reps ρ σ ∧ TyCls env U Δ (t.subst σ) b

/-- A valuation anchored at `σ` for `Γ`: each class is the class of the anchor's value at
the type class of the substituted context entry. -/
def Anchored {β : Type} (Γ : List VExpr) (σ : VExpr.Subst) (ρ : List ((VExpr → Prop) × β)) :
    Prop :=
  ρ.length = Γ.length ∧ ∀ i A (h : i < ρ.length), Lookup Γ i A →
    (ρ[i]).1 = ElCls env U Δ (TyCls env U Δ (A.subst σ)) (σ i)

end

theorem Reps.of_anchored {β : Type} {ρ : List ((VExpr → Prop) × β)}
    (hρ : Anchored env U Δ Γ σ ρ) : Reps ρ σ := by
  intro i h
  have ⟨A, hL⟩ := Lookup.ofLt (hρ.1 ▸ h)
  rw [hρ.2 i A h hL]; exact .self

theorem Reps.mem_cls {β : Type} {ρ : List ((VExpr → Prop) × β)}
    (hρ : Anchored env U Δ Γ σ ρ) (hσ' : Reps ρ σ') :
    ∀ i A, Lookup Γ i A → ElCls env U Δ (TyCls env U Δ (A.subst σ)) (σ i) (σ' i) := by
  intro i A hL
  have h := hρ.1 ▸ hL.lt
  have := hσ' i h; rwa [hρ.2 i A h hL] at this

section
variable (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
include henv hΔ

/-- At an anchored typed valuation, the union-over-representatives element class of a
typed term is the anchored class. -/
theorem clsOf_anchored {β : Type} {ρ : List ((VExpr → Prop) × β)}
    (W : Ctx.SubstEq env U Δ σ σ Γ) (hρ : Anchored env U Δ Γ σ ρ)
    (ht : env.HasType U Γ t T) (hD : D (T.subst σ)) :
    clsOf env U Δ ρ D t = ElCls env U Δ D (t.subst σ) := by
  funext b; apply propext; constructor
  · rintro ⟨σ', hσ', hb⟩
    rwa [ElCls.subst_eq_of_mem_cls henv hΔ W (Reps.mem_cls hρ hσ') ht hD]
  · exact fun hb => ⟨σ, Reps.of_anchored hρ, hb⟩

/-- At an anchored typed valuation, the union-over-representatives type class of a type
is the anchored class. -/
theorem tyClsOf_anchored {β : Type} {ρ : List ((VExpr → Prop) × β)}
    (W : Ctx.SubstEq env U Δ σ σ Γ) (hρ : Anchored env U Δ Γ σ ρ)
    (ht : env.HasType U Γ t (.sort u)) :
    tyClsOf env U Δ ρ t = TyCls env U Δ (t.subst σ) := by
  funext b; apply propext; constructor
  · rintro ⟨σ', hσ', hb⟩
    rwa [TyCls.subst_eq_of_mem_cls henv hΔ W (Reps.mem_cls hρ hσ') ht]
  · exact fun hb => ⟨σ, Reps.of_anchored hρ, hb⟩

end

end Model
end VEnv
end Lean4Lean
