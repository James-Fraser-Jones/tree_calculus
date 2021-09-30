import tactic --imports extra tactics from mathlib (good to import by default)

------------------------------------------------------------------------------------------
--Check mathlib is working

import topology.basic

#check topological_space

------------------------------------------------------------------------------------------
--Establishing equality of terms inside a match block

--https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/match.20hypothesis

example (b : bool) : {x : bool // x = tt} :=
match b with
| tt := ⟨tt, rfl⟩ --we want to be able to use some "h : b = tt" here, but we can't :(
| ff := ⟨tt, rfl⟩
end

-- "{x : bool // x = tt}" is subtype of bool with values that satisfy predicate "= tt"
-- details on subtype here: https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html

--so we can use tactics
example (b : bool) : {x : bool // x = tt} :=
begin
  cases h : b with x y,
  exact ⟨tt, rfl⟩,
  exact ⟨b, h⟩ --now we can use our "h : b = tt"
end

--or we can use a (clever) explicit motive to "rec.on" for the relevant type
example (b : bool) : {x : bool // x = tt} := --inital
bool.rec_on 
  b
  ⟨tt, rfl⟩
  ⟨tt, rfl⟩

example (b : bool) : {x : bool // x = tt} := --use explicit motive
@bool.rec_on 
  (λ b', {x : bool // x = tt})
  b
  ⟨tt, rfl⟩
  ⟨tt, rfl⟩

example (b : bool) : {x : bool // x = tt} := --add "b = b' →" to beginning of motive and feed "rfl" in at the end
(
  @bool.rec_on 
    (λ b', b = b' → {x : bool // x = tt})
    b
    (λ _, ⟨tt, rfl⟩)
    (λ h, ⟨b, h⟩) --now we can use our "h : b = tt"
) rfl

------------------------------------------------------------------------------------------
--Various dependent pair types

#check @Exists  --produces Prop
#check @psigma  --produces Type*
#check @subtype --psigma with                   Sort u_2 = Prop
#check @sigma   --psigma with Sort u_1 = Type*, Sort u_2 = Type*

universes u v
structure psigma' {α : Sort u} (β : α → Sort v) : Sort (max u v) :=
mk :: (fst : α) (snd : β fst)

--psigma' above is disallowed because lean needs to know statically whether something will
--return a Prop or a Type* (i.e. this cannot depend dynamically on the values passed in)

------------------------------------------------------------------------------------------
--Well founded recursion: https://leanprover-community.github.io/extras/well_founded_recursion.html

--For inductive types, there is a default-implemented function sizeof
--which will return the total number of constructors used in a given value of this type
#check @sizeof --Π {α : Sort u_1} [s : has_sizeof α], α → ℕ

--This is the type used by the well-founded recursion checker

--Essentially, at each recursive call site, Lean needs to establish that
--t'.sizeof < t.sizeof where t' is the term at the recursive site and t is the original term
--If it can't do this, you must explicitly provide this as a hypothesis using "have h : t'.sizeof < t.sizeof := ..." 
--Alternatively, you can produce a different function from your inductive type to the natural numbers
--f : t → ℕ
--and use the following tactic at the very end of your recursive function:
--using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf f⟩]}

------------------------------------------------------------------------------------------
--Various congruence theorems/definitions

--generic congruence of equality with function application
--can be used to specify congr_arg, congr_fun and congr_arg2 etc... 
#check @congr                --f₁ = f₂ → a₁ = a₂ → f₁ a₁ = f₂ a₂

--these two are inverses
#check @congr_fun            --f₁ = f₂ → (∀ (a : α), f₁ a = f₂ a)
#check @funext               --(∀ (a : α), f₁ a = f₂ a) → f₁ = f₂

--these two are inverses (note that injective is only a property of *some* functions)
#check @congr_arg            --a₁ = a₂ → f a₁ = f a₂
#reduce @function.injective  --f a₁ = f a₂ → a₁ = a₂

--congruence of equality with a binary function's arguments
#check @congr_arg2           --a₁ = a₃ → a₂ = a₄ → f a₁ a₂ = f a₃ a₄

------------------------------------------------------------------------------------------
--Axioms: https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html

#print axioms       --asks what axioms are available generally
#print axioms congr --asks what axioms are used in given expression

--Core Axioms:
#check @propext           -- (a ↔ b) → a = b
#check @quot.sound        -- r a b → quot.mk r a = quot.mk r b
#check @classical.choice  -- nonempty α → α

--Derived "Axioms":
#check @funext            -- (∀ (x : α), f₁ x = f₂ x) → f₁ = f₂    --provable via quot.sound
#check @em                -- ∀ (p : Prop), p ∨ ¬p                  --provable via propext, funext and classical.choice

--Quotient Constants:
#check @quot      --quotient type constructor
#check @quot.mk   --quotient data constructor
#check @quot.ind  --essentially states there are no empty equivalence classes in "quot r"
#check @quot.lift --lifts a function (f : α → β) to (f' : quot r → β)

/-
"The four constants, quot, quot.mk, quot.ind, and quot.lift in and of themselves are not very strong.
They are, like inductively defined types and the associated constructors and recursors, 
viewed as part of the logical framework."
-/

------------------------------------------------------------------------------------------
--Inductive Types

--Constructors for Inductive types are injective and their domains are disjoint
--This generates smallest possible equality on Inductive types, by default
--Equality can then be exteneded using quotients

inductive ex
| fromNat : ℕ → ex
| fromBool : bool → ex

#check @ex.fromNat.inj  --ex.fromNat n₁ = ex.fromNat n₂ → n₁ = n₂
#check @ex.fromBool.inj --ex.fromNat b₁ = ex.fromNat b₂ → b₁ = b₂

------------------------------------------------------------------------------------------
--Initial and Terminal types for Prop and Type

#check unit    --Terminal Type
#check ()      --value of unit
#check empty   --Initial Type
#check @empty.elim

#check true    --Terminal Prop
#check true.intro
#check trivial --value of true
#check false   --Initial Prop
#check @false.elim

------------------------------------------------------------------------------------------
--Tactics

--Use "induction" tactic instead of "cases" when you need to recursively call a theorem/function
--or use the "equation compiler" by doing ordinary pattern matching outside of a tactic block

------------------------------------------------------------------------------------------
--Congruence

  --Read: https://en.wikipedia.org/wiki/Congruence_relation
  --      https://en.wikipedia.org/wiki/Equivalence_class