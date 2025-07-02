import Mathlib

namespace Signed
/-New inductive type sign. In Mathlib there is no exact type sign but they defined sign as ℤ -/
inductive sign where
| plus:sign
| minus:sign
| zero:sign

def int_of_sign (s:sign):ℤ :=
match s with
| sign.plus => 1
| sign.minus =>-1
| sign.zero => 0

instance : Coe sign ℤ  where
  coe := int_of_sign


def opp (s:sign):sign :=
match s with
|sign.plus => sign.minus
|sign.minus => sign.plus
|sign.zero => sign.zero

def isSameSigned (s u:sign) :Prop :=
 ( s=sign.plus ∧ u=sign.plus ) ∨ (s=sign.minus ∧ u=sign.minus)

def isOppositeSigned (s u:sign) :Prop :=
 ( s=sign.plus ∧ u=sign.minus ) ∨ (s=sign.minus ∧ u=sign.plus)

structure SignedType (α : Type*) where
sign: α -> sign

def instPosPart {α:Type*} (S:SignedType α) :SignedType α where
sign:=
 fun x:α =>
match (S.sign x) with
|sign.plus =>sign.plus
|_ => sign.zero
-- {x| S.sign x= sign.plus}

def instNegPart {α:Type*} (S:SignedType α) :SignedType α where
sign:=
 fun x:α =>
match (S.sign x) with
|sign.minus =>sign.plus
|_ => sign.zero

def support {α:Type*} (S: SignedType α) :Set α :=
{x| S.sign x= sign.plus ∨ S.sign x= sign.minus}

def SignedType_opp {α:Type*} (S:SignedType α):SignedType α where
sign:=opp ∘ S.sign

instance {α :Type*} : Coe (SignedType α) (Set α)  where
  coe := support

instance {α:Type*} :EmptyCollection (SignedType α) where
emptyCollection:= {sign:= fun _=> sign.zero}

instance {α:Type*} : PosPart (SignedType α) where
posPart:=instPosPart

instance {α:Type*} : NegPart (SignedType α) where
negPart:=instNegPart

instance :Neg sign where
neg:=opp

instance {α:Type*}  : Neg (SignedType α) where
neg:=SignedType_opp

--Obvious Facts
theorem negative_singed_type_is_singed_type_of_negative
  {α:Type*} (X:SignedType α ) (x:α) :(-X).sign x =-(X.sign x) := by
  simp [instNegSignedType]
  simp [SignedType_opp]
  rfl

theorem negative_of_empty_is_empty {α:Type*} : (∅ : SignedType α) = -∅ := by
rfl

theorem negative_of_negative_is_self {α:Type*} (X:SignedType α) :
-(-X)=X :=by
simp [instNegSignedType]
simp [SignedType_opp]
congr
apply funext
intros x
simp
induction (X.sign x)
rfl;rfl;rfl

end Signed

namespace Matroid

section
open Signed

def isOrthogonal {α:Type*} (S U:SignedType α): Prop :=
∃ x:α, isSameSigned (S.sign x) (U.sign x) ↔
 ∃ y:α, isOppositeSigned (S.sign y) (U.sign y)

/- Instead of deprecated version of Circuit, it is right way to define a Circuit -/

class Circuit_type {α:Type u_1} (M:Matroid α) :Type u_1 where
base_set: Set α
isCircuit_axiom :IsCircuit M base_set

class Cocircuit_type {α:Type u_1} (M:Matroid α) :Type u_1 where
base_set: Set α
isCocircuit_axiom :IsCocircuit M base_set


class OrientedMatroid_rough_ver (α : Type*) extends Matroid α where
circuit_assignment (x:Set α): Matroid.IsCircuit _ x-> SignedType α
circuit_support (x:Set α) (p:_): support (circuit_assignment x p) = x
cocircuit_assignment (x:Set α): Matroid.IsCocircuit _ x-> SignedType α
cocircuit_support (x:Set α) (p:_): support (cocircuit_assignment x p) = x
circuit_cocircuit_orthogonality (x y:Set α)
 (p: Matroid.IsCircuit _ x) (q: Matroid.IsCocircuit _ y )
 :isOrthogonal (circuit_assignment x p) (cocircuit_assignment y q)

class OrientedMatroid (α : Type*) extends Matroid α where
circuit_assignment : Circuit_type toMatroid -> SignedType α
cocircuit_assignment : Cocircuit_type toMatroid -> SignedType α
circuit_support (C:Circuit_type toMatroid):
support (circuit_assignment C) = C.base_set
cocircuit_support (U:Cocircuit_type toMatroid):
support (cocircuit_assignment U) = U.base_set
circuit_cocircuit_orthogonality
(C:Circuit_type toMatroid) (U:Cocircuit_type toMatroid)
:isOrthogonal (circuit_assignment C) (cocircuit_assignment U)

/- Wikipedia version Signed Circuit Axiom-/

class Is_Set_of_Signed_Circuit {α:Type*} (M:Matroid α) (𝓒 :Set (SignedType α)):Prop where
nonempty : ¬ (∅ ∈ 𝓒)
symmetric: ∀ (C:SignedType α), C ∈ 𝓒 ↔ -C ∈ 𝓒
incomparable :  ∀ (X Y :SignedType α), X ∈ 𝓒 ∧ Y ∈ 𝓒 ->  support X ⊆ support Y
 -> (X=Y ∨ X=-Y)
weak_elimination : ∀ (X Y :SignedType α), X ∈ 𝓒 ∧ Y ∈ 𝓒 ->  X ≠ -Y ∧ e ∈ (↑(X⁺):Set α) ∩ (↑(Y⁻) :Set α )
 -> ∃ Z ∈ 𝓒, ((↑Z⁺:Set α)  ⊆ ↑X⁺ ∪ ↑Y⁺ \{e} ) ∧ ((↑Z⁻ :Set α)  ⊆ ↑X⁻ ∪ ↑Y⁻ \{e} )

-- set_option pp.fieldNotation false

theorem OrientedMatroidEquivDef {α : Type*} (M : OrientedMatroid α) :
Is_Set_of_Signed_Circuit (M.toMatroid) ({M.circuit_assignment C|C:M.Circuit_type} ∪ {- (M.circuit_assignment C)|C:M.Circuit_type}) := by
constructor
· case nonempty =>
    simp_all only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists]
    apply And.intro
    · intro C hp
      let h1:= (M.circuit_support C)
      let h2:= Matroid.Dep.nonempty (Minimal.prop C.isCircuit_axiom)
      rw [hp] at h1
      rw [← h1] at h2
      simp [support] at h2
    · intro C hp
      have h3: OrientedMatroid.circuit_assignment C = ∅
      let h4:= (congrArg (@Neg.neg _ instNegSignedType) hp)
      rw [negative_of_negative_is_self] at h4
      rw [← negative_of_empty_is_empty] at h4
      exact h4
      let h1:= (M.circuit_support C)
      let h2:= Matroid.Dep.nonempty (Minimal.prop C.isCircuit_axiom)
      rw [h3] at h1
      rw [← h1] at h2
      simp [support] at h2
· case symmetric =>
  intro C
  simp_all only [Set.mem_union, Set.mem_setOf_eq]
  apply Iff.intro
  · intro a
    cases a with
    | inl h =>
      obtain ⟨w, h⟩ := h
      subst h
      simp_all only [exists_apply_eq_apply, or_true]
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      subst h
      sorry --very tedious
  · intro a
    cases a with
    | inl h =>
      obtain ⟨w, h⟩ := h
      sorry
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      sorry
· case incomparable =>
  intro X Y h1 h2
  simp_all only [Set.mem_union, Set.mem_setOf_eq]
  obtain ⟨XinC, YinC⟩ := h1
  cases XinC with
  | inl h3 =>
    cases YinC with
    | inl h4 =>
      obtain ⟨XC, h3⟩ := h3
      obtain ⟨YC, h4⟩ := h4
      let h5:= (XC.isCircuit_axiom )
      let h6:= (YC.isCircuit_axiom )
      let h7:= (M.circuit_support XC)
      let h8:= (M.circuit_support YC)
      rw [h3] at h7
      rw [h4] at h8
      let h9:= (Minimal.le_of_le h6 (Minimal.prop h5))
      rw [← h7] at h9
      rw [← h8] at h9
      let h10 := h9 h2


      sorry
    | inr h_2 =>
      obtain ⟨w, h3⟩ := h3
      obtain ⟨w_1, h_1⟩ := h_2
      subst h_1 h
      sorry
  | inr h_1 =>
    cases YinC with
    | inl h =>
      obtain ⟨w, h_1⟩ := h_1
      obtain ⟨w_1, h⟩ := h
      subst h h_1
      sorry
    | inr h_2 =>
      obtain ⟨w, h⟩ := h_1
      obtain ⟨w_1, h_1⟩ := h_2
      subst h_1 h
      sorry

 sorry

toMatroid.
end

end Matroid
