import tactic natree.natree

namespace chapter3

    --equational "axioms"
    @[simp] def kernel {y z} : △⬝△⬝y⬝z = y := natree.kernel
    @[simp] def stem {x y z} : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z) := natree.stem
    @[simp] def fork {w x y z} : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x := natree.fork

end chapter3