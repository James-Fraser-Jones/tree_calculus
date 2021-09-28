axioms (𝕋 : Type) (D K : 𝕋) (app : 𝕋 → 𝕋 → 𝕋)
infixl `⬝`:60 := app
variables {x y z : 𝕋}
axioms (r_D : D⬝x⬝y⬝z = y⬝z⬝(x⬝z)) (r_K : K⬝y⬝z = y)

example : D⬝y⬝x = D⬝(K⬝x)⬝D⬝y :=
  begin
    calc D⬝y⬝x = D⬝y⬝x       : rfl
           ... = D⬝y⬝(K⬝x⬝y) : by conv {to_lhs, rw ←@r_K x y} --why is the "conv to_lhs" necessary?
           ... = D⬝(K⬝x)⬝D⬝y : by rw ←r_D
    ,
  end

example : D⬝y⬝x = D⬝y⬝(K⬝x⬝y) :=
  begin
    conv {to_lhs, rw ←@r_K x y},
  end