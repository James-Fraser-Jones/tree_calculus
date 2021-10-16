namespace chapter2

  --Exercise 1
  /-
  2047 =  11111111111
  1205 =  10010110101
   sum = 110010110100
  
  110010110100 = 2048 + 1024 + 128 + 32 + 16 + 4 = 3252
  -/

  --Exercise 2
  /-
  ---------------------
  |  + |  0 |  1 |  2 |
  ---------------------
  |  0 |  0 |  1 |  2 |
  ---------------------
  |  1 |  1 |  2 | 10 |
  ---------------------
  |  2 |  2 | 10 | 11 |
  ---------------------
  -/

  --Exercise 3
  /-
  ---- ----
  ⊢ C  ⊢ C
  --------- ----
    ⊢ CC    ⊢ L  
  -------------- ----
      ⊢ CCL      ⊢ X
  -------------------
        ⊢ CCLX
  -/

  --Definitions introduced in this chapter:
  
  inductive roman 
  | I | V | X | L | C | D | M
  | add : roman → roman → roman

  namespace roman

    instance : has_one roman := ⟨I⟩
    instance : has_add roman := ⟨add⟩
    infixl `⬝`:60 := (+)
    
    inductive eq_r : roman → roman → Prop
    --equivalence relation
    | refl (r) : eq_r r r
    | symm {r₁ r₂} (h : eq_r r₁ r₂) : eq_r r₂ r₁
    | trans {r₁ r₂ r₃} (h₁ : eq_r r₁ r₂) (h₂ : eq_r r₂ r₃) : eq_r r₁ r₃
    --congruence
    | congr {r₁ r₂ r₃ r₄} (h₁ : eq_r r₁ r₃) (h₂ : eq_r r₂ r₄) : eq_r (r₁⬝r₂) (r₃⬝r₄)
    --collecting like-terms
    | assoc (r₁ r₂ r₃) : eq_r ((r₁⬝r₂)⬝r₃) (r₁⬝(r₂⬝r₃))
    | comm (r₁ r₂) : eq_r (r₁⬝r₂) (r₂⬝r₁)
    --rules for operators
    | opV : eq_r (V) (I⬝I⬝I⬝I⬝I)
    | opX : eq_r (X) (V⬝V)
    | opL : eq_r (L) (X⬝X⬝X⬝X⬝X)
    | opC : eq_r (C) (L⬝L)
    | opD : eq_r (D) (C⬝C⬝C⬝C⬝C)
    | opM : eq_r (M) (D⬝D)

    namespace eq_r

      infixl ` =ᵣ `:50 := eq_r

      @[refl]
      lemma has_refl (r) : r =ᵣ r := 
      by apply refl

      @[symm]
      lemma has_symm {r₁ r₂} (h : r₁ =ᵣ r₂) : r₂ =ᵣ r₁ := 
      by {apply symm, assumption}

      @[trans]
      lemma has_trans {r₁ r₂ r₃} (h₁ : r₁ =ᵣ r₂) (h₂ : r₂ =ᵣ r₃) : r₁ =ᵣ r₃ := 
      by {apply trans, exact h₁, assumption}

    end eq_r

  end roman

  open roman

  inductive arith
  | zero
  | succ : arith → arith
  | add : arith → arith → arith

  namespace arith

    instance : has_zero arith := ⟨zero⟩
    instance : has_add arith := ⟨add⟩
    infixl ` + `:60 := add

    inductive eq_a : arith → arith → Prop
    --equivalence relation
    | refl (a) : eq_a a a
    | symm {a₁ a₂} (h : eq_a a₁ a₂) : eq_a a₂ a₁
    | trans {a₁ a₂ a₃} (h₁ : eq_a a₁ a₂) (h₂ : eq_a a₂ a₃) : eq_a a₁ a₃
    --congruence
    | congr_succ {a₁ a₂} (h : eq_a a₁ a₂) : eq_a (succ a₁) (succ a₂)
    | congr_add {a₁ a₂ a₃ a₄} (h₁ : eq_a a₁ a₃) (h₂ : eq_a a₂ a₄) : eq_a (a₁ + a₂) (a₃ + a₄)
    --characterization of addition
    | add_zero (a) : eq_a (zero + a) a
    | add_succ (a₁ a₂) : eq_a (succ a₁ + a₂) (succ (a₁ + a₂))

    namespace eq_a
      infixl ` =ₐ `:50 := eq_a

      @[refl]
      lemma has_refl (a : arith) : a =ₐ a := --why do we need to specify type here?
      by apply refl

      @[symm]
      lemma has_symm {a₁ a₂ : arith} (h : a₁ =ₐ a₂) : a₂ =ₐ a₁ := 
      by {apply symm, assumption}

      @[trans]
      lemma has_trans {a₁ a₂ a₃ : arith} (h₁ : a₁ =ₐ a₂) (h₂ : a₂ =ₐ a₃) : a₁ =ₐ a₃ := 
      by {apply trans, exact h₁, assumption}

    end eq_a

  end arith

  open arith

  inductive is_numeral : arith → Prop
  | zero : is_numeral zero
  | succ {a} (h : is_numeral a) : is_numeral (succ a)

  def numeral := {a : arith // is_numeral a}

  --Theorems introduced in this chapter:

  theorem thm1 (m n : numeral) : ∃ (p : numeral), m.val + n.val =ₐ p.val := begin
    cases m with m hₘ,
    induction hₘ,
    case is_numeral.zero {
      split,
        apply arith.eq_a.add_zero,
    },
    case is_numeral.succ : m' hₘ' h {
      cases h with p' hₚ,
      split,
        show numeral,
        split,
          show arith,
          exact p'.val.succ,
        apply is_numeral.succ,
        exact p'.property,
      apply arith.eq_a.trans,
          apply arith.eq_a.add_succ,
      apply arith.eq_a.congr_succ,
      assumption,
    },
  end

  theorem thm2 (a : arith) : ∃ (n : numeral), a =ₐ n.val := begin
    induction a,
    case zero {
      split,
        show numeral,
        split,
          apply is_numeral.zero,
      apply eq_a.refl,
    },
    case succ : a h {
      cases h with n h,
      split,
        show numeral,
        split,
          apply is_numeral.succ,
          exact n.property,
      dsimp only,
      apply arith.eq_a.congr_succ,
      assumption,
    },
    case add : a₁ a₂ h₁ h₂ {
      cases h₁ with n₁ h₁,
      cases h₂ with n₂ h₂,
      have h₃ := thm1 n₁ n₂,
      cases h₃ with p h,
      split,
        transitivity,
          apply arith.eq_a.congr_add,
                assumption,
              assumption,
          assumption,
    },
  end

  theorem thm3 (m n : numeral) : succ m.val + n.val =ₐ succ (m.val + n.val) := begin
    cases m with m hₘ,
    induction hₘ,
    case zero {
      dsimp only,
      apply arith.eq_a.add_succ,
    },
    case succ : m' hₘ' h {
      dsimp only at *,
      apply arith.eq_a.add_succ,
    }
  end

end chapter2
