import tactic natree.natree

namespace chapter3

  --equational "axioms"
  @[simp] def kernel {y z} : △⬝△⬝y⬝z = y := natree.kernel
  @[simp] def stem {x y z} : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z) := natree.stem
  @[simp] def fork {w x y z} : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x := natree.fork

  def deriv_K : {K : 𝕋 // ∀ x y, K⬝x⬝y = x} := begin
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

    --remove trailing y
    apply congr,
    apply congr,
    refl,

    --remove trailing x
    apply congr,
    apply congr,
    refl,

    --?m_1 = △⬝△
    
    --finish proof
    repeat {refl},
  end

  def K : 𝕋 := deriv_K.val

end chapter3