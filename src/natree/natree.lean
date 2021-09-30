import tactic natree.pre

--natural trees are pre-trees quotiented by pre-tree equivalence
def natree := quotient natree.pre.equiv

namespace natree

  notation `𝕋` := natree

  def node : 𝕋 := ⟦▢⟧
  notation `△` := node

  def app' (t₁ t₂) := ⟦t₁ ◦ t₂⟧
  lemma app'_liftable {a₁ a₂ b₁ b₂} (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂) : app' a₁ a₂ = app' b₁ b₂ :=
  begin
    repeat {rw wrapp},
    apply quotient.sound,
    apply pre.equiv.congr,
    repeat {assumption}
  end 

  def app : 𝕋 → 𝕋 → 𝕋 := quotient.lift₂ app' @app'_liftable
  infixl `⬝`:60 := app

  theorem quot_dist_app {a b} : ⟦a ◦ b⟧ = ⟦a⟧ ⬝ ⟦b⟧ := rfl

  theorem kernel {y z} : △⬝△⬝y⬝z = y :=
  begin
    have h₁ := quotient.exists_rep y, cases h₁ with y' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep z, cases h₂ with z' h₂, rw ←h₂,
    rw node,
    repeat {rw ←quot_dist_app},
    apply quotient.sound,
    apply pre.equiv.kernel,
  end

  theorem stem {x y z} : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z) :=
  begin
    have h₁ := quotient.exists_rep x, cases h₁ with x' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep y, cases h₂ with y' h₂, rw ←h₂,
    have h₃ := quotient.exists_rep z, cases h₃ with z' h₃, rw ←h₃,
    rw node,
    repeat {rw ←quot_dist_app},
    apply quotient.sound,
    apply pre.equiv.stem,
  end

  theorem fork {w x y z} : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x :=
  begin
    have h₁ := quotient.exists_rep w, cases h₁ with w' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep x, cases h₂ with x' h₂, rw ←h₂,
    have h₃ := quotient.exists_rep y, cases h₃ with y' h₃, rw ←h₃,
    have h₄ := quotient.exists_rep z, cases h₄ with z' h₄, rw ←h₄,
    rw node,
    repeat {rw ←quot_dist_app},
    apply quotient.sound,
    apply pre.equiv.fork,
  end
  
  #check @pre.equiv.not_inj
  --(⬝) is not injective
  theorem not_inj {a₁ a₂ b₁ b₂} : a₁⬝a₂ = b₁⬝b₂ → ¬ (a₁ = b₁ ∧ a₂ = b₂) :=
  begin
    -- intro h,
    -- have h₁ := quotient.exists_rep a₁, cases h₁ with a₁' h₁, rw ←h₁, rw ←h₁ at h,
    -- have h₂ := quotient.exists_rep a₂, cases h₂ with a₂' h₂, rw ←h₂, rw ←h₂ at h,
    -- have h₃ := quotient.exists_rep b₁, cases h₃ with b₁' h₃, rw ←h₃, rw ←h₃ at h,
    -- have h₄ := quotient.exists_rep b₂, cases h₄ with b₂' h₄, rw ←h₄, rw ←h₄ at h,
    -- repeat {rw ←quot_dist_app at h},
    sorry --use pre.equiv.not_inj somehow
  end

end natree