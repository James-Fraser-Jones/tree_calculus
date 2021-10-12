import tactic natree.natree

namespace chapter3

  variables {w x y z : 𝕋}

  ----------------------------3.3 Tree Calculus---------------------------------

  --equational axioms
  @[simp] def kernel : △⬝△⬝y⬝z = y := natree.kernel
  @[simp] def stem : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z) := natree.stem
  @[simp] def fork : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x := natree.fork

  --define primitive combinators
  def K := △⬝△
  @[simp] theorem r_K : K⬝y⬝z = y := by simp [K]

  def I := △⬝(△⬝△)⬝(△⬝△)
  @[simp] theorem r_I : I⬝x = x := by simp [I]

  def D := △⬝(△⬝△)⬝(△⬝△⬝△)
  @[simp] theorem r_D : D⬝x⬝y⬝z = y⬝z⬝(x⬝z) := by simp [D]

  @[simp] def d (x : 𝕋) := △⬝(△⬝x)
  theorem d_eq_r_D : d x = D⬝x := by simp [D]

  --can't do derivation of S combinator because it requires injectivity of (⬝)
  --this proof can only be done with natree.pre, using injectivity of (◦)

  def S := d(K⬝D) ⬝ (d K ⬝ (K⬝D))
  @[simp] theorem r_S : S⬝x⬝y⬝z = x⬝z⬝(y⬝z) := by simp [S]

  ----------------------------3.4 Programs---------------------------------

  --programs are natural trees which never have more than 2 branches anywhere in their structure

  --is_program is an inductive predicate on natural trees
  inductive is_program : 𝕋 → Prop
  | node : is_program △
  | stem {p} (h : is_program p) : is_program (△⬝p)
  | fork {p q} (h₁ : is_program p) (h₂ : is_program q) : is_program (△⬝p⬝q)

  --program is the type of trees that are programs
  def program := {t : 𝕋 // is_program t}

  ----------------------------3.5 Propositional Logic---------------------------------

  def true' := K
  @[simp] theorem r_true' : true'⬝x⬝y = x := by simp[true']

  def false' := K⬝I
  @[simp] theorem r_false' : false'⬝x⬝y = y := by simp[false']

  def and' := d(K⬝(K⬝I))
  example : and'⬝x⬝y = x⬝y⬝(K⬝I) := by simp[and']
  @[simp] theorem r_and'_tt : and'⬝true'⬝true' = true' := by simp[and']
  @[simp] theorem r_and'_tf : and'⬝true'⬝false' = false' := by simp[and']
  @[simp] theorem r_and'_ft : and'⬝false'⬝true' = false' := by simp[and', false']
  @[simp] theorem r_and'_ff : and'⬝false'⬝false' = false' := by simp[and', false']

  def or' := d(K⬝K)⬝I
  def implies' := d(K⬝K)
  def not' := d(K⬝K)⬝(d(K⬝(K⬝I))⬝I)
  def iff' := △⬝(△⬝I⬝not')⬝△

  ----------------------------3.6 Pairs---------------------------------

  --...

end chapter3