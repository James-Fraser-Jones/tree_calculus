import tactic

---------------------------------------------------------------------------

inductive natree_b 
  | node_b : natree_b
  | app_b : natree_b → natree_b → natree_b

namespace natree_b
  notation `𝕋!` := natree_b
  notation `▢` := natree_b.node_b
  infixl `◦`:60 := natree_b.app_b

  --reduction rules of tree calculus, specified as an inductive proposition
  inductive reduce : 𝕋! → 𝕋! → Prop
  | kernel         (y) {z} : reduce (▢◦   ▢   ◦y◦z) y
  |   stem     (x) (y) (z) : reduce (▢◦ (▢◦x) ◦y◦z) (y◦z◦(x◦z))
  |   fork (w) (x) {y} (z) : reduce (▢◦(▢◦w◦x)◦y◦z) (z◦w◦x)
  |   left {a₁ a₂} (b₁) (h : reduce a₁ b₁) : reduce (a₁ ◦ a₂) (b₁ ◦ a₂) --are these necessary?
  |  right {a₁ a₂} (b₂) (h : reduce a₂ b₂) : reduce (a₁ ◦ a₂) (a₁ ◦ b₂)
  infixr ` ↦ `:60 := reduce

  lemma reduce_both {a₁ a₂ b₁ b₂} (h₁ : a₁ ↦ b₁) (h₂ : a₂ ↦ b₂) : a₁◦a₂ ↦ b₁◦b₂ :=
  begin
    --? not currently possible unfortunately :(
  end

  instance setoid : setoid 𝕋! := eqv_gen.setoid (↦)

  lemma congr_equiv {a₁ a₂ b₁ b₂} (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : a₁◦a₂ ≈ b₁◦b₂ :=
  begin
    cases h₁ with _ _ h₁ _ _ _ h₁ _ c _ h₁l h₁r,
          cases h₂ with _ _ h₂ _ _ _ h₂ _ d _ h₂l h₂r,
                apply eqv_gen.rel,
                --?
  end

end natree_b

---------------------------------------------------------------------------

def natree := quotient natree_b.setoid

namespace natree
  notation `𝕋` := natree

  def node : 𝕋 := ⟦▢⟧
  notation `△` := node

  def wrapp (t₁ t₂ : 𝕋!) : 𝕋 := ⟦t₁ ◦ t₂⟧
  lemma wrapp_well_behaved {a₁ a₂ b₁ b₂} (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : wrapp a₁ a₂ = wrapp b₁ b₂ :=
  begin
    repeat {rw wrapp},
    apply quotient.sound,
    exact natree_b.congr_equiv h₁ h₂,
  end 

  def app : 𝕋 → 𝕋 → 𝕋 := quotient.lift₂ wrapp @wrapp_well_behaved
  infixl `⬝`:60 := app
end natree

---------------------------------------------------------------------------