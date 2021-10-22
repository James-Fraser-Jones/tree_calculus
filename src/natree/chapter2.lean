namespace chapter2

  --Exercise 1
  /-
  2047 = 2^10 + 2^9 + 2^8 + 2^7 + 2^6 + 2^5 + 2^4 + 2^3 + 2^2 + 2^1 + 2^0 
       = 0b011111111111

  1205 = 2^10 + 2^7 + 2^5 + 2^4 + 2^2 + 2^0
       = 0b010010110101

   sum = 0b110010110100
       = 2^11 + 2^10 + 2^7 + 2^5 + 2^4 + 2^2 = 3252
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

  --------------------------------------------------------------------

  --Definitions introduced in this chapter:
  
  inductive roman 
  | I | V | X | L | C | D | M
  | append : roman → roman → roman

  namespace roman

    instance : has_one roman := ⟨I⟩
    instance : has_add roman := ⟨append⟩
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
    instance : has_one arith := ⟨succ zero⟩
    instance : has_add arith := ⟨add⟩

    inductive eq_a : arith → arith → Prop
    --equivalence relation
    | refl (a) : eq_a a a
    | symm {a₁ a₂} (h : eq_a a₁ a₂) : eq_a a₂ a₁
    | trans {a₁ a₂ a₃} (h₁ : eq_a a₁ a₂) (h₂ : eq_a a₂ a₃) : eq_a a₁ a₃
    --congruence
    | congr_succ {a₁ a₂} (h : eq_a a₁ a₂) : eq_a (succ a₁) (succ a₂)
    | congr_add {a₁ a₂ a₃ a₄} (h₁ : eq_a a₁ a₃) (h₂ : eq_a a₂ a₄) : eq_a (a₁ + a₂) (a₃ + a₄)
    --characterization of addition
    | zero_add (a) : eq_a (0 + a) a
    | succ_add (a₁ a₂) : eq_a (succ a₁ + a₂) (succ (a₁ + a₂))

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
  | zero : is_numeral 0
  | succ {a} (h : is_numeral a) : is_numeral (succ a)

  def numeral := {a : arith // is_numeral a}

  --Theorems introduced in this chapter:

  --1
  theorem numeral_add_closure (m n : numeral) : ∃ (p : numeral), m.val + n.val =ₐ p.val := begin
    cases m with m hₘ,
    induction hₘ,
    case is_numeral.zero {
      split,
        apply arith.eq_a.zero_add,
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
          apply arith.eq_a.succ_add,
      apply arith.eq_a.congr_succ,
      assumption,
    },
  end

  --2
  theorem arith_to_numeral (a : arith) : ∃ (n : numeral), a =ₐ n.val := begin
    induction a,
    case zero {
      split,
        show numeral,
        split,
          apply is_numeral.zero,
      apply arith.eq_a.refl,
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
      have h₃ := numeral_add_closure n₁ n₂,
      cases h₃ with p h,
      split,
        transitivity,
          apply arith.eq_a.congr_add,
                assumption,
              assumption,
          assumption,
    },
  end

  --3
  theorem numeral_add_succ (m n : numeral) : m.val + succ n.val =ₐ succ (m.val + n.val) := begin
    cases m with m hₘ,
    induction hₘ,
    case zero {
      dsimp only,
      transitivity,
        apply arith.eq_a.zero_add,
      apply arith.eq_a.congr_succ,
      symmetry,
      apply arith.eq_a.zero_add,
    },
    case succ : m' hₘ' h {
      dsimp only at *,
      transitivity,
        apply arith.eq_a.succ_add,
      apply arith.eq_a.congr_succ,
      symmetry,
      transitivity,
        apply arith.eq_a.succ_add,
      symmetry,
      assumption,
    }
  end

  --4
  theorem numeral_zero_unit (n : numeral) : 0 + n.val =ₐ n.val ∧ n.val + 0 =ₐ n.val := begin
    split,
      apply arith.eq_a.zero_add,
    cases n with n hₙ,
    dsimp only,
    induction hₙ,
    case zero {
      apply arith.eq_a.zero_add,
    },
    case succ : n' hₙ' h {
      transitivity,
        apply arith.eq_a.succ_add,
      apply arith.eq_a.congr_succ,
      assumption,
    },
  end

  lemma numeral_add_comm (n₁ n₂ : numeral) : n₁.val + n₂.val =ₐ n₂.val + n₁.val := begin
    cases n₁ with n₁ hn₁,
    dsimp only at *,
    induction hn₁,
    case zero {
      symmetry,
      transitivity,
        exact (numeral_zero_unit n₂).2,
      symmetry,
      apply arith.eq_a.zero_add,
    },
    case succ : n₁' hn₁' h {
      transitivity,
        apply arith.eq_a.succ_add,
      transitivity,
        apply arith.eq_a.congr_succ,
          assumption,
      symmetry,
      exact numeral_add_succ n₂ ⟨n₁', hn₁'⟩,
    } 
  end

  --5
  theorem add_comm (a₁ a₂ : arith) : a₁ + a₂ =ₐ a₂ + a₁ := begin
    have h₁ := arith_to_numeral a₁,
    cases h₁ with n₁ h₁,
    have h₂ := arith_to_numeral a₂,
    cases h₂ with n₂ h₂,
    transitivity,
      apply arith.eq_a.congr_add,
            assumption,
        assumption,
    symmetry,
    transitivity,
      apply arith.eq_a.congr_add,
            assumption,
        assumption,
    symmetry,
    apply numeral_add_comm,
  end

  lemma numeral_add_assoc (n₁ n₂ n₃ : numeral) : (n₁.val + n₂.val) + n₃.val =ₐ n₁.val + (n₂.val + n₃.val) := begin
    cases n₁ with n₁ hn₁,
    dsimp only at *,
    induction hn₁,
    case zero {
      transitivity,
        apply arith.eq_a.congr_add,
              apply arith.eq_a.zero_add,
          refl,
      symmetry,
      transitivity,
        apply arith.eq_a.zero_add,
      refl,
    },
    case succ : n₁' hn₁' h {
      transitivity,
        apply arith.eq_a.congr_add,
              apply arith.eq_a.succ_add,
          refl,
      transitivity,
        apply arith.eq_a.succ_add,
      transitivity,
        apply arith.eq_a.congr_succ,
          assumption,
      symmetry,
      transitivity,
        apply arith.eq_a.succ_add,
      refl,
    },
  end

  --6
  theorem add_assoc (a₁ a₂ a₃ : arith) : (a₁ + a₂) + a₃ =ₐ a₁ + (a₂ + a₃) := begin
    have h₁ := arith_to_numeral a₁,
    cases h₁ with n₁ h₁,
    have h₂ := arith_to_numeral a₂,
    cases h₂ with n₂ h₂,
    have h₃ := arith_to_numeral a₃,
    cases h₃ with n₃ h₃,
    transitivity,
      apply arith.eq_a.congr_add,
            apply arith.eq_a.congr_add,
                assumption,
            assumption,
        assumption,
    symmetry,
    transitivity,
      apply arith.eq_a.congr_add,
            assumption,
        apply arith.eq_a.congr_add, 
            assumption,
        assumption,
    symmetry,
    apply numeral_add_assoc,
  end

  --Conversion from roman numerals to arithmetic expressions
  def c : roman → arith := begin
    let c1 := (1 : arith),
    let cV := c1 + c1 + c1 + c1 + c1,
    let cX := cV + cV,
    let cL := cX + cX + cX + cX + cX,
    let cC := cL + cL,
    let cD := cC + cC + cC + cC + cC,
    let cM := cD + cD,
    intro r,
    induction r,
    exact c1,
    exact cV,
    exact cX,
    exact cL,
    exact cC,
    exact cD,
    exact cM,
    case roman.append : r s cr cs {
      exact cr + cs,
    },
  end

  --7
  theorem congr_conversion {r s : roman} (h : r =ᵣ s) : c r =ₐ c s := begin
    induction h,
    case eq_r.refl {
      refl,
    },
    case eq_r.symm : s r h h' {
      symmetry,
      assumption,
    },
    case eq_r.trans : r t s h₁ h₂ h₁' h₂' {
      transitivity,
      assumption,
      assumption,
    },
    case eq_r.congr : r s r' s' h₁ h₂ h₁' h₂' {
      transitivity,
      apply arith.eq_a.congr_add,
      assumption,
      assumption,
      refl,
    },
    case eq_r.assoc : r s t {
      apply add_assoc,
    },
    case eq_r.comm : r s {
      apply add_comm,
    },
    repeat {refl},
  end

  --------------------------------------------------------------------

  --Exercise 4

  example : (M⬝M⬝X⬝X⬝X⬝X⬝V⬝I⬝I) + (M⬝C⬝C⬝V) =ᵣ M⬝M⬝M⬝C⬝C⬝L⬝I⬝I := begin
    have h₁ : (M⬝M⬝X⬝X⬝X⬝X⬝V⬝I⬝I) + (M⬝C⬝C⬝V) =ᵣ M⬝M⬝M⬝C⬝C⬝X⬝X⬝X⬝X⬝V⬝V⬝I⬝I,
    sorry,
    have h₂ : M⬝M⬝M⬝C⬝C⬝X⬝X⬝X⬝X⬝V⬝V⬝I⬝I =ᵣ M⬝M⬝M⬝C⬝C⬝X⬝X⬝X⬝X⬝X⬝I⬝I,
    sorry,
    have h₃ : M⬝M⬝M⬝C⬝C⬝X⬝X⬝X⬝X⬝X⬝I⬝I =ᵣ M⬝M⬝M⬝C⬝C⬝L⬝I⬝I,
    sorry,
    repeat {
      transitivity,
      assumption,
    },
    refl,
  end

end chapter2
