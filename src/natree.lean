import tactic

inductive natree_b 
  | node : natree_b
  | app : natree_b → natree_b → natree_b

namespace natree_b
  notation `𝕋!` := natree_b
  notation `▢` := natree_b.node
  infixl `◦`:60 := natree_b.app

  --reduction rules of tree calculus, specified as an inductive proposition
  inductive reduce : 𝕋! → 𝕋! → Prop
  | kernel         (y) {z} : reduce (▢◦   ▢   ◦y◦z) y
  |   stem     (x) (y) (z) : reduce (▢◦ (▢◦x) ◦y◦z) (y◦z◦(x◦z))
  |   fork (w) (x) {y} (z) : reduce (▢◦(▢◦w◦x)◦y◦z) (z◦w◦x)
  |   left {a₁ a₂ b₁} (h : reduce a₁ b₁) : reduce (a₁ ◦ a₂) (b₁ ◦ a₂)
  |  right {a₁ a₂ b₂} (h : reduce a₂ b₂) : reduce (a₁ ◦ a₂) (a₁ ◦ b₂)
  infixr ` ↦ `:60 := reduce

  ---------------------------------------------------------------------------

  instance setoid : setoid 𝕋! := eqv_gen.setoid (↦)

  lemma reduce_to_equiv {a b} : a ↦ b → a ≈ b :=
  begin
    intro h,
    apply eqv_gen.rel,
    assumption,
  end

  theorem kernel {y z} : (▢◦▢◦y◦z) ≈ y :=
  begin
    apply reduce_to_equiv,
    apply reduce.kernel,
  end

  theorem stem {x y z} : (▢◦(▢◦x)◦y◦z) ≈ (y◦z◦(x◦z)) :=
  begin
    apply reduce_to_equiv,
    apply reduce.stem,
  end

  theorem fork {w x y z} : (▢◦(▢◦w◦x)◦y◦z) ≈ (z◦w◦x) :=
  begin
    apply reduce_to_equiv,
    apply reduce.fork,
  end

  lemma congr_equiv_left {a₁ a₂ b₁} : a₁ ≈ b₁ → a₁◦a₂ ≈ b₁◦a₂ :=
  begin
    intro h,
    induction h with x y h _ x y h₁ h₂ x y z h₁ h₂ h₃ h₄,
          apply eqv_gen.rel,
          apply reduce.left,
          assumption,
        apply eqv_gen.refl,
      apply eqv_gen.symm,
      assumption,
    apply eqv_gen.trans,
        assumption,
    assumption,
  end

  lemma congr_equiv_right {a₁ a₂ b₂} : a₂ ≈ b₂ → a₁◦a₂ ≈ a₁◦b₂ :=
  begin
    intro h,
    induction h with x y h _ x y h₁ h₂ x y z h₁ h₂ h₃ h₄,
          apply eqv_gen.rel,
          apply reduce.right,
          assumption,
        apply eqv_gen.refl,
      apply eqv_gen.symm,
      assumption,
    apply eqv_gen.trans,
        assumption,
    assumption,
  end

  theorem congr_equiv {a₁ a₂ b₁ b₂} : a₁ ≈ b₁ → a₂ ≈ b₂ → a₁◦a₂ ≈ b₁◦b₂ :=
  begin
    intros h₁ h₂,
    apply eqv_gen.trans,
        apply congr_equiv_left,
        assumption,
    apply congr_equiv_right,
    assumption,
  end

end natree_b

---------------------------------------------------------------------------

def natree := quotient natree_b.setoid

namespace natree
  notation `𝕋` := natree

  def node : 𝕋 := ⟦▢⟧
  notation `△` := node

  def app' (t₁ t₂) := ⟦t₁ ◦ t₂⟧
  lemma app'_liftable {a₁ a₂ b₁ b₂} (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : app' a₁ a₂ = app' b₁ b₂ :=
  begin
    repeat {rw wrapp},
    apply quotient.sound,
    apply natree_b.congr_equiv,
    repeat {assumption}
  end 

  def app : 𝕋 → 𝕋 → 𝕋 := quotient.lift₂ app' @app'_liftable
  infixl `⬝`:60 := app

  theorem quot_dist_app {a b} : ⟦a ◦ b⟧ = ⟦a⟧ ⬝ ⟦b⟧ := rfl --!!!

  ---------------------------------------------------------------------------

  @[simp] theorem kernel {y z} : △⬝△⬝y⬝z = y :=
  begin
    have h₁ := quotient.exists_rep y, cases h₁ with y' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep z, cases h₂ with z' h₂, rw ←h₂,
    rw node,
    repeat {rw ←quot_dist_app},
    apply quotient.sound,
    apply natree_b.kernel,
  end

  @[simp] theorem stem {x y z} : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z) :=
  begin
    have h₁ := quotient.exists_rep x, cases h₁ with x' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep y, cases h₂ with y' h₂, rw ←h₂,
    have h₃ := quotient.exists_rep z, cases h₃ with z' h₃, rw ←h₃,
    rw node,
    repeat {rw ←quot_dist_app},
    apply quotient.sound,
    apply natree_b.stem,
  end

  @[simp] theorem fork {w x y z} : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x :=
  begin
    have h₁ := quotient.exists_rep w, cases h₁ with w' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep x, cases h₂ with x' h₂, rw ←h₂,
    have h₃ := quotient.exists_rep y, cases h₃ with y' h₃, rw ←h₃,
    have h₄ := quotient.exists_rep z, cases h₄ with z' h₄, rw ←h₄,
    rw node,
    repeat {rw ←quot_dist_app},
    apply quotient.sound,
    apply natree_b.fork,
  end

end natree

def K := △⬝△
@[simp] theorem r_K {y z} : K⬝y⬝z = y := by simp [K] --SUCCESS!