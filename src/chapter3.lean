import tactic natree.natree

namespace chapter3

  --equational "axioms"
  @[simp] def kernel {y z} : △⬝△⬝y⬝z = y := natree.kernel
  @[simp] def stem {x y z} : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z) := natree.stem
  @[simp] def fork {w x y z} : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x := natree.fork

  --K combinator (combinator for Kernel rule)
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

  --I combinator (identity combinator)
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

  --D combinator (flipped S combinator, combinator for Stem rule)
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
    show K⬝△⬝x = △, by apply derive_K.property,
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
    have h : K = △⬝△ := rfl, 
    exact h,
    refl,
    symmetry,

    --?m_1 = △⬝(△⬝△)⬝(△⬝△⬝△)

    --finish proof
    repeat {refl},
  end
  def D : 𝕋 := △⬝(△⬝△)⬝(△⬝△⬝△)

  def d (x : 𝕋) : 𝕋 := △⬝(△⬝x)
  lemma d_equiv_D {x} : (d x) = D⬝x := by simp [d, D]

end chapter3