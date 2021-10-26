import tactic

@[derive decidable_eq]
inductive pre 
| node : pre
| app : pre → pre → pre

notation `𝕋'` := pre
notation `▢` := pre.node
infixl `◦`:60 := pre.app

inductive reduces : 𝕋' → 𝕋' → Type
| kernel         (y) {z} : reduces (▢◦   ▢   ◦y◦z) y
|   stem     (x) (y) (z) : reduces (▢◦ (▢◦x) ◦y◦z) (y◦z◦(x◦z))
|   fork (w) (x) {y} (z) : reduces (▢◦(▢◦w◦x)◦y◦z) (z◦w◦x)
|   left {a₁ a₂ b₁} (h : reduces a₁ b₁) : reduces (a₁ ◦ a₂) (b₁ ◦ a₂)
|  right {a₁ a₂ b₂} (h : reduces a₂ b₂) : reduces (a₁ ◦ a₂) (a₁ ◦ b₂)
infixr ` ↦ `:60 := reduces

def reduceable (t₁ t₂) := nonempty (t₁ ↦ t₂)
infixr ` ⇢ `:60 := reduceable

def reduce_kernel : ∀ (t₁ t₂), option (t₁ ↦ t₂)
| (▢◦▢◦y◦z) y₂ := if h : y = y₂ then some (by {rw ←h, apply reduces.kernel}) else none
| _ _ := none

#check id_rhs
#check @dite --dite : Π {α : Sort u_1} (c : Prop) [h : decidable c], (c → α) → (¬c → α) → α
#check @ite  -- ite : Π {α : Sort u_1} (c : Prop) [h : decidable c],      α  →       α  → α
#print reduce_kernel._main

example {n} : nat.zero ≠ nat.succ n := begin
  intro h, 
  injection h,
end

example {n} : nat.succ n ≠ nat.zero := begin
  intro h, 
  injection h,
end

example {m n} : nat.succ n = nat.succ m → n = m := begin
  intro h,
  injection h,
end

#check @bool.ff.inj

lemma kernel_complete (t₁ t₂) : (∃ r, reduce_kernel t₁ t₂ = some r) ↔ ∃ y z, (▢◦▢◦y◦z) ↦ y ∧ t₁ = (▢◦▢◦y◦z) ∧ t₂ = y :=

def list_reductions (t₁ t₂) : list (t₁ ↦ t₂) := sorry

--if I can define this I can define anything
--still need to figure out how "no confusion" works tbf
def reductions (t₁ t₂) : fintype (t₁ ↦ t₂) := begin
  split,
    show finset _,
    split,
      show multiset _,
      apply quotient.mk,

      --produce a list of reductions
      --show that the multiset (quotient of this list) has no duplicates
      --prove that every possible reduction is in this multiset
end

example {α} (l : list α) : multiset α := by refine multiset.zero

#check @reduces.rec_on

#print reduces.no_confusion
#print pre.app.inj

/-
reduces.cases_on:

This function takes a reduction 'n' from an arbitrary tree 'a' to an arbitrary tree 'b' and uses it
to produce a dependent Proposition (proving something about reduction) or Type (some kind of data).

{motive : Π (a b : 𝕋'), a ↦ b → Sort u}
{a b : 𝕋'} 
(n : a ↦ b)

If 'a' reduces to 'b' via the kernel rule, show P
(Π (y : 𝕋') {z : 𝕋'}, motive (▢◦▢◦y◦z) y (reduces.kernel y))

If 'a' reduces to 'b' via the stem rule, show P 
(Π (x y z : 𝕋'), motive (▢◦(▢◦x)◦y◦z) (y◦z◦(x◦z)) (reduces.stem x y z))

If 'a' reduces to 'b' via the fork rule, show P
(Π (w x : 𝕋') {y : 𝕋'} (z : 𝕋'), motive (▢◦(▢◦w◦x)◦y◦z) (z◦w◦x) (reduces.fork w x z))

If 'a' reduces to 'b' via the left rule, show P
(Π {a₁ a₂ b₁ : 𝕋'} (h : a₁ ↦ b₁), motive (a₁◦a₂) (b₁◦a₂) h.left)

If 'a' reduces to 'b' via the right rule, show P
(Π {a₁ a₂ b₂ : 𝕋'} (h : a₂ ↦ b₂), motive (a₁◦a₂) (a₁◦b₂) h.right)

Hence P is true
motive a b n

--------------------------------------------------------------------------
reduces.rec_on:

This function differs only in the case of the recursive left/right rules which build a reduction
'a ↦ b' from another reduction 'x ↦ y'

(Π {a₁ a₂ b₁ : 𝕋'} (h : a₁ ↦ b₁), motive a₁ b₁ h → motive (a₁◦a₂) (b₁◦a₂) h.left)
(Π {a₁ a₂ b₂ : 𝕋'} (h : a₂ ↦ b₂), motive a₂ b₂ h → motive (a₁◦a₂) (a₁◦b₂) h.right)

Previously we had:
Using (h : a₁ ↦ b₁), show that P holds of (a₁◦a₂) ↦ (b₁◦a₂).
Now we have:
Using (h : a₁ ↦ b₁), and that P holds of a₁ ↦ b₁, show that P holds of (a₁◦a₂) ↦ (b₁◦a₂).
-/

---------------------------------------------------------------------

inductive and' : Prop → Prop → Prop
| mk {p q} (h₁ : p) (h₂ : q) : and' p q

def left {p q} (h : and' p q) : p := h.rec_on (λ _ _ h₁ _, h₁)

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

namespace weekday
def next (d : weekday) : weekday :=
weekday.cases_on d monday tuesday wednesday thursday friday
  saturday sunday

def previous (d : weekday) : weekday :=
weekday.cases_on d saturday sunday monday tuesday wednesday
  thursday friday

#reduce next (next tuesday)
#reduce next (previous tuesday)

example : next (previous tuesday) = tuesday := rfl

theorem next_previous (d: weekday) :
  next (previous d) = d :=
weekday.cases_on d rfl rfl rfl rfl rfl rfl rfl

theorem next_previous' (d: weekday) : next (previous d) = d := by cases d; refl

end weekday

#check @false.rec_on
#check @false.elim

#check @true.rec_on

#check @bool.rec_on
#check @bool.cases_on

def band' (b1 b2 : bool) : bool := bool.cases_on b1 ff b2
#reduce band' tt tt
#reduce band' tt ff
#reduce band' ff tt
#reduce band' ff ff

def bor' (b1 b2 : bool) : bool := bool.cases_on b1 b2 tt
#reduce bor' tt tt
#reduce bor' tt ff
#reduce bor' ff tt
#reduce bor' ff ff

def bnot' (b1 : bool) : bool := bool.cases_on b1 tt ff
#reduce bnot' tt
#reduce bnot' ff

universes u v
inductive prod' (α : Type*) (β : Type*) --what?? :s
| mk : α → β → prod'

#check @prod'.mk

def fst {α β : Type*} (p : α × β) : α := prod.rec_on p (λ a _, a)

#check @prod.rec_on

inductive sum' (α : Type u) (β : Type v)
| inl {} (a : α) : sum'
| inr {} (b : β) : sum'

#check @sum'.inl
#check @sum'.inr

inductive option' (α : Type*)
| none {} : option'
| some    : α → option'

#check @option'.none --option'.none : Π {α : Type u_1}, option' α

#check @nat.cases_on 
--Π {motive : ℕ → Sort u_1} (n : ℕ), motive 0 → (Π (n : ℕ), motive n.succ) → motive n
--If our motive maps into Prop, we have: "If p when n = 0, and p when n = n'+1 then p for all n"
#check @nat.rec_on
--Π {motive : ℕ → Sort u_1} (n : ℕ), motive 0 → (Π (n : ℕ), motive n → motive n.succ) → motive n
--This time it's inductive reasoning:    "If p when n = 0, and (if p when n = n' then p when n = n'+1) then p for all n"

def add' (m n : nat) : nat := nat.rec_on m n (λ k kaddn, nat.succ kaddn)

inductive foo : Type
| bar1 : ℕ → ℕ → foo
| bar2 : ℕ → ℕ → ℕ → foo

open foo

def silly (x : foo) : ℕ :=
begin
  cases x,
    case bar1 : a b
      { exact b },
    case bar2 : c d e
      { exact e }
end

open nat
variable p : ℕ → Prop

example (hz : p 0) (hs : ∀ n, p (succ n)) (m k : ℕ) :
  p (m + 3 * k) :=
begin
  cases (m + 3 * k),
  { exact hz },  -- goal is p 0
  apply hs       -- goal is a : ℕ ⊢ p (succ a)
end

lemma injection_example (h : 7 = 4) : false := begin
  injection h with h',
  injection h' with h'',
  injection h'' with h''',
  injection h''' with h'''',
  injection h'''' with h''''',
end

#print injection_example
#print nat.succ.inj_arrow

inductive eq' {α : Sort u} (a : α) : α → Prop
| refl [] : eq' a

#check @eq'
#check @eq'.refl --eq'.refl : ∀ {α : Sort u_1} (a : α), eq' a a

inductive bool'
| tt' : bool' 
| ff' : bool'
open bool'

def bool'_equal (b₁ b₂ : bool') : Prop :=
bool'.cases_on b₁ 
( bool'.cases_on b₂
  true
  false --explicitly returns false when the two values aren't equal
)
( bool'.cases_on b₂
  false
  true
)

def bool_equal (b₁ b₂ : bool) : Prop := begin
  cases b₁,
    cases b₂,
      exact true,
    exact false,
  cases b₂,
    exact false,
  exact true
end

lemma bool_no_confusion {b₁ b₂} : (b₁ = b₂) → bool_equal b₁ b₂ := begin
  intro h,
  rw h,
  cases b₂,
    trivial,
  trivial,
end

theorem true_not_eq_false : tt ≠ ff := bool_no_confusion

theorem true_not_eq_false' : tt ≠ ff := by {intro h, cases h}

theorem true_not_eq_false'' : tt ≠ ff :=
id (λ (h : tt = ff), h.cases_on (λ (H_1 : ff = tt), bool.no_confusion H_1) (eq.refl ff) (heq.refl h))

#print bool.no_confusion_type
#reduce bool.no_confusion_type false tt tt
#reduce bool.no_confusion_type false tt ff
#reduce bool.no_confusion_type false ff tt
#reduce bool.no_confusion_type false tt tt
#reduce bool.no_confusion_type (tt = ff) tt tt
#reduce bool.no_confusion_type (tt = ff) tt ff

#check @bool.no_confusion

#reduce bool'_equal tt' tt'
#reduce bool'_equal tt' ff'
#reduce bool'_equal ff' tt'
#reduce bool'_equal ff' ff'

#print nat.no_confusion_type
#reduce nat.no_confusion_type false
#print bool.rec

def bool'_no_confusion {b₁ b₂ : bool'} : (b₁ = b₂) → bool'_equal b₁ b₂ :=
λ h, 
eq.cases_on h 
(bool'.cases_on b₁ trivial trivial) --bool'_equal b₁ b₁
--produces bool'_equal b₁ b₂

--our no_confusion function is actually logically equivalent to equality
def bool'_no_confusion' {b₁ b₂ : bool'} : (b₁ = b₂) ↔ bool'_equal b₁ b₂ := begin
  split,
    intro h,
    rw h,
    rw bool'_equal,
    cases b₂,
      trivial,
    trivial,
  intro h,
  cases b₁,
    cases b₂,
      refl,
    exfalso,
    assumption,
  cases b₂,
    exfalso,
    assumption,
  refl,
end

--b₁ = b₂ implies that trivial is a proof of bool'_equal b₁ b₂ since bool'_equal b₁ b₂ reduces to true
--don't forget that (tt' ≠ ff') := (tt' = ff' → false)
theorem unconfused : tt' ≠ ff' := bool'_no_confusion

#print bool'.no_confusion_type

-------------------------------------------------------------------------------

inductive xnat
| zero : xnat
| succ : xnat → xnat 
open xnat

def xnat_equal' (n₁ n₂ : xnat) : Prop :=
@xnat.rec_on (λ x, Prop) n₁ (
  --n₁ = 0
  @xnat.rec_on (λ x, Prop) n₂
    --n₂ = 0
    true
    --n₂ = succ n₂'
    (λ n₂' p₂, false)
)(
  --n₁ = succ n₁'
  λ n₁' p₁,
  @xnat.rec_on (λ x, Prop) n₂
    --n₂ = 0
    false
    --n₂ = succ n₂'
    (λ n₂' p₂, _)
)

--unwrap outer layer only, no recursion necessary
def xnat_equal (n₁ n₂ : xnat) : Prop := begin
  cases n₁ with n₁',
    cases n₂ with n₂',
      exact true,
    exact false,
  cases n₂ with n₂',
    exact false,
  exact n₁' = n₂' --no recursion necessary here
end

def xnat_no_confusion {s t : xnat} (h : s = t) : xnat_equal s t := begin
  rw h,
  cases t,
    trivial,
  show t = t,
  refl,
end

#print xnat_no_confusion

--how do these theorems work?
theorem wat (n : xnat) : succ n ≠ xnat.zero := xnat_no_confusion --disjoint ranges
theorem wat' (n : xnat) : xnat.zero ≠ succ n := xnat_no_confusion
theorem succ_injective (m n : xnat) : succ m = succ n → m = n := xnat_no_confusion --injective

def bool_equal' : bool → bool → Prop
| tt tt := true
| tt ff := false
| ff tt := false
| ff ff := true

section
  example (m n : ℕ) : ∃ (p : ℕ), m + n = p := begin
    induction h : m generalizing m,
    case nat.succ : m' h₂ {
      --need to use "∃ (p : ℕ), m' + n = p" here but can't
      --why is "m = m' →" added to the beginning of h₂?
    }
  end
end
