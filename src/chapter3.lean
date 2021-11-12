import tactic natree.natree

namespace chapter3

  --equational "axioms"
  @[simp] def kernel {y z} : △⬝△⬝y⬝z = y := natree.kernel
  @[simp] def stem {x y z} : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z) := natree.stem
  @[simp] def fork {w x y z} : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x := natree.fork

  --------------------------------------------------------------------

  --Definitions introduced in this chapter:

  --Fundamental Combinators
  def K := △⬝△
  def I := △⬝K⬝K
  def D := △⬝K⬝(K⬝△)
  def d (x) := △⬝(△⬝x)
  def S := (d (K⬝D))⬝((d K)⬝(K⬝D))

  --Programs
  inductive is_program : 𝕋 → Prop
  | kernel : is_program △
  | stem {a} (h : is_program a) : is_program (△⬝a)
  | fork {a b} (h₁ : is_program a) (h₂ : is_program b) : is_program (△⬝a⬝b)

  def program := {t : 𝕋 // is_program t}

  --Propositional Logic
  def true := K
  def false := K⬝I

  def and := d (K⬝(K⬝I))
  def or := (d (K⬝K))⬝I
  def implies := d (K⬝K)
  def not := (d (K⬝K))⬝((d (K⬝(K⬝I)))⬝I)
  def iff := △⬝(△⬝I⬝not)⬝△

  --Pairs
  def Pair := △

  def first (p) := △⬝p⬝△⬝K
  def second (p) := △⬝p⬝△⬝(K⬝I)

  --Iterated Application
  def iterate : ℕ → 𝕋 → 𝕋 → 𝕋
  | 0 a b := b
  | (n+1) a b := a⬝(iterate n a b)

  notation a ^ n ⬝ b := iterate n a b

  --Natural Numbers
  def nat_to_natree (n) := K^n⬝△

  def zero := △
  def successor := K
  def isZero := (d (K^4⬝I))⬝((d (K⬝K))⬝△)
  def predecessor := (d (K^2⬝I))⬝((d (K⬝△))⬝△)

  --Fundamental Queries
  def query (is0 is1 is2) := (d (K⬝is1))⬝((d (K^2⬝I))⬝((d (K^5⬝is2))⬝((d (K^3⬝is0))⬝△)))
  def isLeaf := query K (K⬝I) (K⬝I)
  def isStem := query (K⬝I) K (K⬝I)
  def isFork := query (K⬝I) (K⬝I) K

  --------------------------------------------------------------------

  --Exercise 1
  lemma K_prop {x y} : K⬝x⬝y = x := by simp [K]
  lemma S_prop {x y z} : S⬝x⬝y⬝z = x⬝z⬝(y⬝z) := by simp [S, d, D, K]

  def D'_deriv : {D' // ∀ x y z, D'⬝x⬝y⬝z = y⬝z⬝(x⬝z)} := begin
    split,
    intros x y z,

    rw ←S_prop,

    apply congr,
    apply congr,
    refl,

    symmetry,
    transitivity,
    apply congr,
    refl,
    symmetry,
    apply K_prop,
    exact y,
    symmetry,

    rw ←S_prop,

    apply congr,
    apply congr,
    refl,

    symmetry,
    transitivity,
    apply congr,
    apply congr,
    refl,
    symmetry,
    apply K_prop,
    exact x,
    refl,
    symmetry,

    symmetry,
    transitivity,
    symmetry,
    apply S_prop,
    symmetry,

    apply congr,
    apply congr,
    refl,

    repeat {refl},
  end
  def D' := S⬝(K⬝(S⬝S))⬝K
  example : D'_deriv.val = D' := rfl

  --Exercise 2
  example {y} : and⬝false⬝y = false := by simp [and, d, D, false, I, K]

  --Exercise 3
  example : or⬝true⬝true = true := by simp [or, d, D, true, false, I, K]
  example : or⬝true⬝false = true := by simp [or, d, D, true, false, I, K]
  example : or⬝false⬝true = true := by simp [or, d, D, true, false, I, K]
  example : or⬝false⬝false = false := by simp [or, d, D, true, false, I, K]

  example : implies⬝true⬝true = true := by simp [implies, d, D, true, false, I, K]
  example : implies⬝true⬝false = false := by simp [implies, d, D, true, false, I, K]
  example : implies⬝false⬝true = true := by simp [implies, d, D, true, false, I, K]
  example : implies⬝false⬝false = true := by simp [implies, d, D, true, false, I, K]

  example : not⬝true = false := by simp [not, d, D, true, false, I, K]
  example : not⬝false = true := by simp [not, d, D, true, false, I, K]

  example : iff⬝true⬝true = true := by simp [iff, not, d, D, true, false, I, K]
  example : iff⬝true⬝false = false := by simp [iff, not, d, D, true, false, I, K]
  example : iff⬝false⬝true = false := by simp [iff, not, d, D, true, false, I, K]
  example : iff⬝false⬝false = true := by simp [iff, not, d, D, true, false, I, K]

  --Exercise 4
  def fst_deriv : {fst // ∀ p, fst⬝p = first p} := begin
    split,
    intro p,
    rw first,

    symmetry,
    transitivity,
    symmetry,
    apply fork,
    exact △,
    symmetry,

    rw ←K,

    symmetry,
    transitivity,
    apply congr,
    apply congr,
    refl,
    symmetry,
    apply K_prop,
    exact p,
    refl,
    symmetry,

    symmetry,
    transitivity,
    symmetry,
    apply S_prop,
    symmetry,

    apply congr,
    apply congr,
    refl,

    repeat {refl},
  end
  def fst := S⬝(K⬝(△⬝(K⬝K)⬝△))⬝△
  example : fst_deriv.val = fst := rfl
  lemma fst_prop {x y} : fst⬝(Pair⬝x⬝y) = x := by simp [fst, Pair, S, d, D, K]

  def snd := S⬝(K⬝(△⬝(K⬝(K⬝I))⬝△))⬝△
  lemma snd_prop {x y} : snd⬝(Pair⬝x⬝y) = y := by simp [snd, Pair, S, d, D, I, K]

  --Exercise 5
  lemma predecessor_prop_1 : predecessor⬝zero = zero := by simp [predecessor, zero, d, iterate, I, K]
  lemma predecessor_prop_2 {n} : predecessor⬝(successor⬝n) = n := by simp [predecessor, successor, d, iterate, I, K]

  --Exercise 6
  def nat_to_natree' (n) := △^n⬝△

  def zero' := △
  example : nat_to_natree' 0 = zero := rfl

  def successor' := △
  example {n} : successor'⬝(nat_to_natree' n) = nat_to_natree' n.succ := rfl

  def isZero' := S⬝(S⬝△⬝(K⬝K))⬝(K⬝(K⬝I))
  example : isZero'⬝zero' = true := by simp [isZero', zero', true, S, d, D, I, K]
  example {n} : isZero'⬝(successor'⬝n) = false := by simp [isZero', successor', false, S, d, D, I, K]

  def predecessor' := S⬝(K⬝(△⬝(K⬝K)⬝△))⬝(S⬝(K⬝△)⬝(S⬝(S⬝isZero'⬝I)⬝(S⬝I⬝(K⬝△))))
  example : predecessor'⬝zero' = zero' := by simp [predecessor', zero', isZero', S, d, D, I, K]
  example {n} : predecessor'⬝(successor'⬝n) = n := by simp [predecessor', successor', isZero', S, d, D, I, K]

  --Exercise 7
  #reduce isLeaf
  def isLeafVal := (△⬝(△⬝(△⬝△⬝(△⬝△⬝(△⬝(△⬝△)⬝(△⬝△)))))⬝(△⬝(△⬝(△⬝△⬝(△⬝△⬝(△⬝(△⬝△)⬝(△⬝△)))))⬝(△⬝(△⬝(△⬝△⬝(△⬝△⬝(△⬝△⬝(△⬝△⬝(△⬝△⬝(△⬝△⬝(△⬝(△⬝△)⬝(△⬝△)))))))))⬝(△⬝(△⬝(△⬝△⬝(△⬝△⬝(△⬝△⬝(△⬝△)))))⬝△))))
  example : isLeafVal = isLeaf := rfl

  example : isLeafVal⬝△ = true := by simp [isLeafVal, true, K]
  example : isLeafVal⬝K = false := by simp [isLeafVal, false, K, I]
  example : isLeafVal⬝(K⬝△) = false := by simp [isLeafVal, false, K, I]

  --Exercise 8
  /-
  a(n) gives number of binary trees where depth <= n
  a(0) = 1
  a(n) = a(n-1) + a(n-1)^2 + 1

  b(n) gives number of binary trees where depth = n
  b(0) = 1
  b(n) = a(n-1)^2 + 1
  -/

end chapter3