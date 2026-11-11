import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Tower
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Values

/-! # The types the model encodes have at most the cardinality of the continuum

`Nat`, `Fin n`, `Bool`, `Unit`, `Empty` and `Candidate` are `ContinuumSized`. For `Candidate`
(a set of proof values) this needs an injection of `PVal` into `Nat`, built from the pairing
`2 ^ a * (2 * b + 1)`.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

/-- An injective pairing of natural numbers. -/
def npair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

theorem npair_inj : ∀ {a b a' b' : Nat}, npair a b = npair a' b' → a = a' ∧ b = b'
  | 0, b, 0, b', h => by simp only [npair, Nat.pow_zero, Nat.one_mul] at h; exact ⟨rfl, by omega⟩
  | 0, b, a' + 1, b', h => by
    simp only [npair, Nat.pow_zero, Nat.pow_succ, Nat.one_mul] at h
    generalize 2 ^ a' = x at h
    have : x * 2 * (2 * b' + 1) = 2 * (x * (2 * b' + 1)) := by
      rw [Nat.mul_comm x 2, Nat.mul_assoc]
    omega
  | a + 1, b, 0, b', h => by
    simp only [npair, Nat.pow_zero, Nat.pow_succ, Nat.one_mul] at h
    generalize 2 ^ a = x at h
    have : x * 2 * (2 * b + 1) = 2 * (x * (2 * b + 1)) := by
      rw [Nat.mul_comm x 2, Nat.mul_assoc]
    omega
  | a + 1, b, a' + 1, b', h => by
    have h' : npair a b = npair a' b' := by
      simp only [npair, Nat.pow_succ] at h ⊢
      have e1 : 2 ^ a * 2 * (2 * b + 1) = 2 * (2 ^ a * (2 * b + 1)) := by
        rw [Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
      have e2 : 2 ^ a' * 2 * (2 * b' + 1) = 2 * (2 ^ a' * (2 * b' + 1)) := by
        rw [Nat.mul_comm (2 ^ a') 2, Nat.mul_assoc]
      omega
    obtain ⟨rfl, rfl⟩ := npair_inj h'
    exact ⟨rfl, rfl⟩

/-- An injection of the proof values into the natural numbers. -/
def PVal.code : PVal → Nat
  | .var i => npair 0 i
  | .lam b => npair 1 b.code
  | .app f a => npair 2 (npair f.code a.code)
  | .r => npair 3 0
  | .bot => npair 4 0
  | .case s x y => npair 5 (npair s.code (npair x.code y.code))

theorem PVal.code_inj : ∀ {a b : PVal}, a.code = b.code → a = b := by
  intro a
  induction a with
  | var i => intro b h; cases b <;> simp [PVal.code] at h <;> have := npair_inj h <;> simp_all
  | lam x ih =>
    intro b h; cases b <;> simp only [PVal.code] at h <;> have := npair_inj h <;>
      first | omega | (rw [ih this.2])
  | app f x ihf ihx =>
    intro b h; cases b <;> simp only [PVal.code] at h <;> have := npair_inj h <;>
      first | omega | (have h2 := npair_inj this.2; rw [ihf h2.1, ihx h2.2])
  | r => intro b h; cases b <;> first | rfl | (simp only [PVal.code] at h; have := npair_inj h; omega)
  | bot => intro b h; cases b <;> first | rfl | (simp only [PVal.code] at h; have := npair_inj h; omega)
  | case s x y ihs ihx ihy =>
    intro b h; cases b <;> simp only [PVal.code] at h <;> have := npair_inj h <;>
      first
      | omega
      | (have h2 := npair_inj this.2; have h3 := npair_inj h2.2
         rw [ihs h2.1, ihx h3.1, ihy h3.2])

instance (n : Nat) : ContinuumSized (Fin n) :=
  ContinuumSized.of_injective (β := Nat) Fin.val fun _ _ => Fin.ext

instance : ContinuumSized Bool :=
  ContinuumSized.of_injective (β := Nat) (fun b => cond b 1 0) (by decide)

instance : ContinuumSized Unit :=
  ContinuumSized.of_injective (β := Nat) (fun _ => 0) fun _ _ _ => rfl

instance : ContinuumSized Empty :=
  ContinuumSized.of_injective (β := Nat) (fun e => e.elim) fun a => a.elim

instance : ContinuumSized Candidate :=
  ⟨fun c n => ∃ v : PVal, v.code = n ∧ c.mem v, fun a b e => by
    cases a with | mk ma sa => ?_
    cases b with | mk mb sb => ?_
    have : ma = mb := by
      funext v
      have := congrFun e v.code
      simp only at this
      apply propext
      constructor
      · intro h
        obtain ⟨v', hv', h'⟩ := this.mp ⟨v, rfl, h⟩
        rwa [PVal.code_inj hv'] at h'
      · intro h
        obtain ⟨v', hv', h'⟩ := this.mpr ⟨v, rfl, h⟩
        rwa [PVal.code_inj hv'] at h'
    subst this; rfl⟩

end VEnv.Strengthening
end Lean4Lean
