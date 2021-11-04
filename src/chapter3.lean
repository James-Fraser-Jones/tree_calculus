import tactic natree.natree

namespace chapter3

  --equational "axioms"
  @[simp] def kernel {y z} : △⬝△⬝y⬝z = y := natree.kernel
  @[simp] def stem {x y z} : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z) := natree.stem
  @[simp] def fork {w x y z} : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x := natree.fork

  --K combinator (similar to Kernel rule)
  def derive_K : {K : 𝕋 // ∀ x y, K⬝x⬝y = x} := begin
    --metavariable ?m_1 introduced for K
    split,
    intros x y, 

    --use kernel rule
    symmetry,
    transitivity,
    symmetry,
    apply kernel,
    exact y,
    symmetry,

    --remove trailing ys
    apply congr,
    apply congr,
    refl,

    --remove trailing xs
    apply congr,
    apply congr,
    refl,

    --?m_1 = △⬝△
    
    --finish proof
    repeat {refl},
  end

  def K : 𝕋 := △⬝△

  --I combinator (Identity combinator)
  def derive_I : {I : 𝕋 // ∀ x, I⬝x = x} := begin
    --metavariable ?m_1 introduced for I
    split,
    intro x, 

    --use kernel rule
    symmetry,
    transitivity,
    symmetry,
    apply kernel,
    exact △⬝x,
    symmetry,

    --use stem rule
    symmetry,
    transitivity,
    symmetry,
    apply stem,
    symmetry,

    --remove trailing xs
    apply congr,
    apply congr,
    refl,

    --?m_1 = △⬝(△⬝△)⬝(△⬝△)

    --finish proof
    repeat {refl},
  end

  def I : 𝕋 := △⬝(△⬝△)⬝(△⬝△)

  --D combinator (flipped S combinator, similar to Stem rule)
  def derive_D : {D : 𝕋 // ∀ x y z, D⬝x⬝y⬝z = y⬝z⬝(x⬝z)} := begin
    --metavariable ?m_1 introduced for D
    split,
    intros x y z,

    --use stem rule
    symmetry,
    transitivity,
    symmetry,
    apply stem,
    symmetry,

    --remove trailing zs
    apply congr,
    apply congr,
    refl,

    --remove trailing ys
    apply congr,
    apply congr,
    refl,

    --replace △ with K⬝△⬝x
    symmetry,
    transitivity,
    apply congr,
    apply congr,
    refl,
    symmetry,
    show K⬝△⬝x = △,
    apply derive_K.property,
    refl,
    symmetry,

    --use stem rule
    symmetry,
    transitivity,
    symmetry,
    apply stem,
    symmetry,

    --remove trailing xs
    apply congr,
    apply congr,
    refl,

    --unfold definition of K
    symmetry,
    transitivity,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,
    show K = △⬝△, 
    refl,
    refl,
    symmetry,

    --?m_1 = △⬝(△⬝△)⬝(△⬝△⬝△)

    --finish proof
    repeat {refl},
  end

  def D : 𝕋 := △⬝(△⬝△)⬝(△⬝△⬝△)

  --d function (shorter version of D)
  def d (x : 𝕋) : 𝕋 := △⬝(△⬝x)
  lemma d_equiv_D {x} : D⬝x = d x := by simp [d, D]

  --iterated application
  def iterate : ℕ → 𝕋 → 𝕋 → 𝕋
  | 0 a b := b
  | (n+1) a b := a⬝(iterate n a b)
  notation a ^ n ⬝ b := iterate n a b

  --derivation of the fundamental queries
  def derive_q {a b c e} : {q : 𝕋 // ∀ x, q⬝x = △⬝x⬝a⬝b⬝c⬝e} := begin
    --metavariable ?m_1 introduced for q
    split,
    intro x,

    --replace △⬝x⬝a with D⬝(K⬝a)⬝△⬝x (utilizing Stem rule)
    symmetry,
    transitivity,
    apply congr,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,
    show △⬝x⬝a = D⬝(K⬝a)⬝△⬝x,
    symmetry,
    have h : D = derive_D.val := rfl,
    rw h,
    transitivity,
    apply derive_D.property,
    apply congr,
    refl,
    have h₂ : K = derive_K.val := rfl,
    rw h₂,
    apply derive_K.property,
    refl,
    refl,
    refl,
    symmetry,

    --replace (D⬝(K⬝a)⬝△)⬝x⬝b with D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△)⬝x (utilizing Stem rule)
    symmetry,
    transitivity,
    apply congr,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,
    show (D⬝(K⬝a)⬝△)⬝x⬝b = D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△)⬝x,
    symmetry,
    have h : D = derive_D.val := rfl,
    rw h,
    transitivity,
    apply derive_D.property,
    apply congr,
    refl,
    have h₂ : K = derive_K.val := rfl,
    rw h₂,
    apply derive_K.property,
    refl,
    refl,
    symmetry,

    --replace D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△)⬝x⬝c with D⬝(K⬝c)⬝(D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△))⬝x (utilizing Stem rule)
    symmetry,
    transitivity,
    apply congr,
    apply congr,
    refl,
    show D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△)⬝x⬝c = D⬝(K⬝c)⬝(D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△))⬝x,
    symmetry,
    have h : D = derive_D.val := rfl,
    rw h,
    transitivity,
    apply derive_D.property,
    apply congr,
    refl,
    have h₂ : K = derive_K.val := rfl,
    rw h₂,
    apply derive_K.property,
    refl,
    symmetry,

    --replace D⬝(K⬝c)⬝(D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△))⬝x⬝d with D⬝(K⬝d)⬝(D⬝(K⬝c)⬝(D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△)))⬝x (utilizing Stem rule)
    symmetry,
    transitivity,
    show D⬝(K⬝c)⬝(D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△))⬝x⬝e = D⬝(K⬝e)⬝(D⬝(K⬝c)⬝(D⬝(K⬝b)⬝(D⬝(K⬝a)⬝△)))⬝x,
    symmetry,
    have h : D = derive_D.val := rfl,
    rw h,
    transitivity,
    apply derive_D.property,
    apply congr,
    refl,
    have h₂ : K = derive_K.val := rfl,
    rw h₂,
    apply derive_K.property,
    symmetry,

    --remove xs
    apply congr,
    apply congr,
    refl,
    
    --replace with ds
    symmetry,
    repeat {
      transitivity,
      rw d_equiv_D,
    },
    symmetry,

    --?m_1 = d (K⬝e)⬝(d (K⬝c)⬝(d (K⬝b)⬝(d (K⬝a)⬝△)))

    --finish proof
    repeat {refl},
  end

  def bool_to_natree : bool → 𝕋
  | tt := K
  | ff := K⬝I

  structure solution_property (f g h k : 𝕋) (is0 is1 is2 : bool) : Prop :=
  (eq0 : △⬝△⬝f⬝g⬝h⬝k = bool_to_natree is0)
  (eq1 : ∀ x, △⬝(△⬝x)⬝f⬝g⬝h⬝k = bool_to_natree is1)
  (eq2 : ∀ x y, △⬝(△⬝x⬝y)⬝f⬝g⬝h⬝k = bool_to_natree is2)

  lemma k2 {a b c} : (K^2⬝a)⬝b⬝c = a := begin
    --rewrite in terms of derive_K.val
    repeat {rw iterate},
    have h : K = derive_K.val := rfl,
    rw h,

    --remove c
    transitivity,
    apply congr,
    apply congr,
    refl,

    --simplify using K-rule
    apply derive_K.property,
    refl,

    --simplify using K-rule again
    apply derive_K.property,
  end

  lemma k4 {a b c d e} : (K^4⬝a)⬝b⬝c⬝d⬝e = a := begin
    --rewrite in terms of derive_K.val
    repeat {rw iterate},
    have h : K = derive_K.val := rfl,
    rw h,

    --remove c, d and e
    transitivity,
    apply congr,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,

    --simplify using K-rule
    apply derive_K.property,
    refl,
    refl,
    refl,

    --remove d and e
    transitivity,
    apply congr,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,

    --simplify using K-rule
    apply derive_K.property,
    refl,
    refl,

    --remove e
    transitivity,
    apply congr,
    apply congr,
    refl,

    --simplify using K-rule
    apply derive_K.property,
    refl,

    --simplify using K-rule again
    apply derive_K.property,
  end

  lemma kI {a b} : K⬝I⬝a⬝b = b := begin
    transitivity,
    apply congr,
    apply congr,
    refl,
    have h : K = derive_K.val := rfl,
    show K⬝I⬝a = I,
    rw h,
    apply derive_K.property,
    refl,
    have h₂ : I = derive_I.val := rfl,
    rw h₂,
    apply derive_I.property,
  end

  def prove_query {is0 is1 is2} : Σ' f g h k, solution_property f g h k is0 is1 is2 := begin
    --apply naive solution for f (K^2⬝(bool_to_natree is0))
    split,
    show 𝕋,
    exact K^2⬝(bool_to_natree is0), 

    --apply naive solution for g (K^4⬝(bool_to_natree is2))
    split,
    show 𝕋,
    exact K^4⬝(bool_to_natree is2),

    --apply derived solution for h (bool_to_natree is1)
    split,
    show 𝕋,
    exact bool_to_natree is1,

    --apply derived solution for k (bool_to_natree is1)
    split,
    show 𝕋,
    exact bool_to_natree is1,

    split,

    ---------------------------------------------
    
    --remove h and k
    transitivity,
    apply congr,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,

    --use kernel rule
    apply kernel,
    refl,
    refl,

    --use k2
    apply k2,

    ---------------------------------------------

    intro x,

    --remove h and k
    transitivity,
    apply congr,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,

    --use stem rule and k2
    transitivity,
    apply stem,
    apply k2,
    refl,
    refl,

    --split on cases
    cases is0,

    --case false
    rw bool_to_natree,
    apply kI,

    --case true
    rw bool_to_natree,
    have h : K = derive_K.val := rfl,
    rw h,
    apply derive_K.property,

    ---------------------------------------------

    intros x y,

    --remove h and k
    transitivity,
    apply congr,
    apply congr,
    refl,
    apply congr,
    apply congr,
    refl,

    --use fork rule and k4
    transitivity,
    apply fork,
    refl,
    refl,
    refl,
    apply k4,
  end

  --D in terms of K and S
  def S : 𝕋 := (d (K⬝D))⬝((d K)⬝(K⬝D))
  lemma S_prop {x y z} : S⬝x⬝y⬝z = x⬝z⬝(y⬝z) := by simp [S, d, D, K]
  
  def D' : 𝕋 := S⬝(K⬝(S⬝S))⬝K
  example {x y z} : D'⬝x⬝y⬝z = y⬝z⬝(x⬝z) := by simp [D', S, d, D, K]

  --Defining fst and snd
  def fst : 𝕋 := S⬝(K⬝(△⬝(K⬝K)⬝△))⬝△
  example {x y} : fst⬝(△⬝x⬝y) = x := by simp [fst, S, d, D, K]

  def snd : 𝕋 := S⬝(K⬝(△⬝(K⬝(K⬝I))⬝△))⬝△
  example {x y} : snd⬝(△⬝x⬝y) = y := by simp [snd, S, d, D, K, I]

  def unseat : 𝕋 := S⬝(K⬝(S⬝I))⬝K
  example {x y} : unseat⬝x⬝y = y⬝x := by simp [unseat, S, d, D, K, I]
  --flip⬝(b⬝x⬝y) = b⬝y⬝x

end chapter3