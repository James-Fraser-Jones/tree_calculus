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
  --- ---
  ⊢ C ⊢ C
  --------  ---
    ⊢ CC    ⊢ L  
  -------------- ----
      ⊢ CCL      ⊢ X
  -------------------
        ⊢ CCLX
  -/

  --Definitions introduced in this chapter:
  
  inductive roman 
  | I | V | X | L | C | D | M
  | app : roman → roman → roman

  open roman
  infixl `⬝`:60 := app

  inductive romanEq : roman → roman → Prop
  --equivalence relation
  | refl (r) : romanEq r r
  | symm {r₁ r₂} (h : romanEq r₁ r₂) : romanEq r₂ r₁
  | trans {r₁ r₂ r₃} (h₁ : romanEq r₁ r₂) (h₂ : romanEq r₂ r₃) : romanEq r₁ r₃
  --congruence
  | congr {r₁ r₂ r₃ r₄} (h₁ : romanEq r₁ r₃) (h₂ : romanEq r₂ r₄) : romanEq (r₁⬝r₂) (r₃⬝r₄)
  --collecting like-terms
  | assoc (r₁ r₂ r₃) : romanEq ((r₁⬝r₂)⬝r₃) (r₁⬝(r₂⬝r₃))
  | comm (r₁ r₂) : romanEq (r₁⬝r₂) (r₂⬝r₁)
  --rules for operators
  | opV : romanEq (V) (I⬝I⬝I⬝I⬝I)
  | opX : romanEq (X) (V⬝V)
  | opL : romanEq (L) (X⬝X⬝X⬝X⬝X)
  | opC : romanEq (C) (L⬝L)
  | opD : romanEq (D) (C⬝C⬝C⬝C⬝C)
  | opM : romanEq (M) (D⬝D)

  infixl ` =ᵣ `:50 := romanEq

  -- inductive numeral
  -- | zero
  -- | succ : numeral → numeral

  inductive arith
  | zero
  | succ : arith → arith
  | add : arith → arith → arith

  open arith
  infixl ` + `:60 := add

  inductive is_numeral : arith → Prop
  | zero : is_numeral zero
  | succ {a} (h : is_numeral a) : is_numeral (succ a)

  --a numeral is a pair containing an arith 'a' and a proof of "is_numeral a"
  def numeral := {a : arith // is_numeral a}

  inductive arithEq : arith → arith → Prop
  --equivalence relation
  | refl (a) : arithEq a a
  | symm {a₁ a₂} (h : arithEq a₁ a₂) : arithEq a₂ a₁
  | trans {a₁ a₂ a₃} (h₁ : arithEq a₁ a₂) (h₂ : arithEq a₂ a₃) : arithEq a₁ a₃
  --congruence
  | congr_succ {a₁ a₂} (h : arithEq a₁ a₂) : arithEq (succ a₁) (succ a₂)
  | congr_add {a₁ a₂ a₃ a₄} (h₁ : arithEq a₁ a₃) (h₂ : arithEq a₂ a₄) : arithEq (a₁ + a₂) (a₃ + a₄)
  --characterization of addition
  | add_zero (a) : arithEq (zero + a) a
  | add_succ (a₁ a₂) : arithEq (succ a₁ + a₂) (succ (a₁ + a₂))

  infixl ` =ₐ `:50 := arithEq

  --Theorems introduced in this chapter:

  example (m n : numeral) : ∃ (p : numeral), m.val + n.val =ₐ p.val := begin
    induction h : m.val,
    case arith.zero {
      split,
      apply arithEq.add_zero,
    },
    case arith.add : m₁ m₂ { --requires "induction h : m.val"
      sorry
      -- exfalso,
      -- have h₂ := m.property,
      -- have h₃ : is_numeral (m₁ + m₂) := h ▸ h₂,
      -- cases h₃,
    },
    case arith.succ : m' h₁ { --requires "induction m.val"
      --h₁ : ∃ (p : numeral), m' + n.val =ₐ p.val
      cases h₁ with p' h₁,
      split,
        show numeral,
        apply subtype.mk,
          show arith,
          exact p'.val.succ,
        apply is_numeral.succ,
        exact p'.property,
      show m'.succ + n.val =ₐ p'.val.succ,
      have h₂ : (m' + n.val).succ =ₐ p'.val.succ,
        apply arithEq.congr_succ,
        assumption,
      apply arithEq.symm,
      apply arithEq.trans,
          apply arithEq.symm,
          assumption,
      apply arithEq.symm,
      apply arithEq.add_succ,
    },
  end

  example (m n : numeral) : ∃ (p : numeral), m.val + n.val =ₐ p.val :=
  arith.rec_on m.val 
  ( exists.intro --m = zero
    n
    (arithEq.add_zero n.val)
  ) 
  ( λ m' h, --m = succ m'
    exists.intro 
    ( exists.elim 
      h 
      ( λ p' h₂, 
        subtype.mk 
        (p'.val.succ) 
        (is_numeral.succ (p'.property))
      )
    ) 
    (_)
  ) 
  (_ --m = m₁ + m₂
  )

end chapter2
