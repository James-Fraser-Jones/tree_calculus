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

  def d (x : 𝕋) : 𝕋 := △⬝(△⬝x)
  lemma d_equiv_D {x} : D⬝x = d x := by simp [d, D]

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

  -- --structure to hold solution to query contraints using 4 arguments: f g h k
  -- structure query_contraints

  -- def bool_to_natree : bool → 𝕋
  -- | tt := K
  -- | ff := K⬝I

  -- def derive_query : 
  -- {
  --   query : bool → bool → bool → 𝕋 // 
  --   ∀ is0 is1 is2, ∀ x y, 
  --     (query is0 is1 is2)⬝x = bool_to_natree is0
  --   ∧ (query is0 is1 is2)⬝(△⬝x) = bool_to_natree is1
  --   ∧ (query is0 is1 is2)⬝(△⬝x⬝y) = bool_to_natree is2
  -- } := begin
  --   split,
  --   intros is0 is1 is2 x y,
  --   split,

  -- end

  def query (ker ste for x : 𝕋) : 𝕋 := △⬝x⬝(K⬝(K⬝ker))⬝(K⬝(K⬝(K⬝(K⬝for))))⬝ste⬝ste
  example {x y : 𝕋} : query (K⬝I) (K⬝I) (K) (△) = K⬝I := by simp [K, I, query]
  example {x y : 𝕋} : query (K⬝I) (K⬝I) (K) (△⬝x) = K⬝I := by simp [K, I, query]
  example {x y : 𝕋} : query (K⬝I) (K⬝I) (K) (△⬝x⬝y) = K := by simp [K, I, query]
end chapter3