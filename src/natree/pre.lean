import tactic

namespace natree

  --inductive structure of pre-trees (natural trees pre-quotienting)
  @[derive decidable_eq]
  inductive pre 
  | node : pre
  | app : pre → pre → pre

  namespace pre

    notation `𝕋'` := pre
    notation `▢` := pre.node
    infixl `◦`:60 := pre.app

    --reduction rules of tree calculus, specified as an inductive binary relation on pre-trees
    inductive reduces : 𝕋' → 𝕋' → Prop
    | kernel         (y) {z} : reduces (▢◦   ▢   ◦y◦z) y
    |   stem     (x) (y) (z) : reduces (▢◦ (▢◦x) ◦y◦z) (y◦z◦(x◦z))
    |   fork (w) (x) {y} (z) : reduces (▢◦(▢◦w◦x)◦y◦z) (z◦w◦x)
    |   left {a₁ a₂ b₁} (h : reduces a₁ b₁) : reduces (a₁◦a₂) (b₁◦a₂)
    |  right {a₁ a₂ b₂} (h : reduces a₂ b₂) : reduces (a₁◦a₂) (a₁◦b₂)
    infixr ` ↦ `:60 := reduces

    #check fintype --use instead of decidable for Types
    #check nonempty --use to collapse a Type into a Prop

    example {a b} : a ↦ b := begin
      mapply reduces.stem,
    end

    -----------------------------------------------------------------------------------

    def decide_reduces : decidable_rel (↦)
    | (▢◦▢◦y◦z) y₂ := begin
      sorry
    end
    | (▢◦(▢◦x)◦y◦z) (y₂◦z₂◦(x₂◦z₃)) := begin
      sorry
    end
    | (▢◦(▢◦w◦x)◦y◦z) (z₂◦w₂◦x₂) := begin
      sorry --works when w = w₂ ...
    end
    | (a₁◦a₂) (b₁◦b₂) := 
    if h : a₁ = b₁ then 
    begin 
      rw ←h,
      cases decide_reduces a₂ b₂ with h₂ h₂,
        left,
        intro h₃,
        sorry,
      sorry,
    end 
    else if a₂ = b₂ then 
    sorry 
    else 
    sorry
    | a ▢ :=
    begin
      cases a with a a₄,
        left, intro h, cases h,
      cases a with a a₃,
        left, intro h, cases h,
      cases a with a₁ a₂,
        left, intro h, cases h,
      by_cases h₁ : a₁ = ▢,
        by_cases h₂ : a₂ = ▢,
          by_cases h₃ : a₃ = ▢,
            right, rw [h₁, h₂, h₃], apply reduces.kernel,
          left, intro h, apply h₃, cases h, refl,
        left, intro h, apply h₂, cases h, refl,
      left, intro h, apply h₁, cases h, refl,
    end
    | ▢ b := begin
      left,
      intro h,
      cases h,
    end

    example {a₁ a₂ b₁ b₂} : a₁◦a₂ ↦ b₁◦b₂ ↔ a₁ ↦ b₁ ∧ a₂ = b₂ ∨ a₁ = b₁ ∧ a₂ ↦ b₂ := begin
      split,
        intro h,
        cases h,
    end

    -----------------------------------------------------------------------------------

    --equivalence relation on pre-trees generated by reflexive, symmetric, transitive closure of (↦)
    instance equiv : setoid 𝕋' := eqv_gen.setoid (↦)

    namespace equiv

      lemma lift_reduces_to {a b} : a ↦ b → a ≈ b :=
      begin
        intro h,
        apply eqv_gen.rel,
        assumption,
      end

      theorem kernel {y z} : (▢◦▢◦y◦z) ≈ y :=
      begin
        apply lift_reduces_to,
        apply reduces.kernel,
      end

      theorem stem {x y z} : (▢◦(▢◦x)◦y◦z) ≈ (y◦z◦(x◦z)) :=
      begin
        apply lift_reduces_to,
        apply reduces.stem,
      end

      theorem fork {w x y z} : (▢◦(▢◦w◦x)◦y◦z) ≈ (z◦w◦x) :=
      begin
        apply lift_reduces_to,
        apply reduces.fork,
      end

      lemma congr_left {a₁ a₂ b₁} : a₁ ≈ b₁ → a₁◦a₂ ≈ b₁◦a₂ :=
      begin
        intro h,
        induction h with x y h _ x y h₁ h₂ x y z h₁ h₂ h₃ h₄,
              apply eqv_gen.rel,
              apply reduces.left,
              assumption,
            apply eqv_gen.refl,
          apply eqv_gen.symm,
          assumption,
        apply eqv_gen.trans,
            assumption,
        assumption,
      end

      lemma congr_right {a₁ a₂ b₂} : a₂ ≈ b₂ → a₁◦a₂ ≈ a₁◦b₂ :=
      begin
        intro h,
        induction h with x y h _ x y h₁ h₂ x y z h₁ h₂ h₃ h₄,
              apply eqv_gen.rel,
              apply reduces.right,
              assumption,
            apply eqv_gen.refl,
          apply eqv_gen.symm,
          assumption,
        apply eqv_gen.trans,
            assumption,
        assumption,
      end

      theorem congr {a₁ a₂ b₁ b₂} : a₁ ≈ b₁ → a₂ ≈ b₂ → a₁◦a₂ ≈ b₁◦b₂ :=
      begin
        intros h₁ h₂,
        apply eqv_gen.trans,
            apply congr_left,
            assumption,
        apply congr_right,
        assumption,
      end

      -----------------------------------------------------------------------------------

      --I believe this requires confluence to prove in the transitive case
      lemma hmm : ¬ ▢ ≈ ▢◦▢ := begin
        sorry
      end

      --(◦) is *not* injective modulo equivalence
      theorem not_inj : ¬ (∀ {a₁ a₂ b₁ b₂}, a₁◦a₂ ≈ b₁◦b₂ → a₁ ≈ b₁ ∧ a₂ ≈ b₂) :=
      begin
        intro h₁,
        have h₂ := @stem ▢ ▢ ▢,
        have h₃ := @h₁ (▢◦(▢◦▢)◦▢) ▢ (▢◦▢) (▢◦▢),
        have h₄ := h₃ h₂,
        cases h₄,
        apply hmm,
        assumption,
      end

      -----------------------------------------------------------------------------------

    end equiv

  end pre

end natree