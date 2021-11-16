import tactic chapter3

open chapter3

namespace chapter4

  #check natree.pre.index

  def subst' : char → 𝕋' → 𝕋' → 𝕋'
  | x u (£ y) := if y = natree.pre.index x then u else £ y
  | x u ▢ := ▢
  | x u (s◦t) := (subst' x u s) ◦ (subst' x u t)

  lemma subst_red_t {x} {u t₁ t₂} (h : t₁ ↦ t₂) : subst' x u t₁ ≈ subst' x u t₂ := begin
    apply eqv_gen.rel,
    induction h,
    case kernel : y' z' {
      repeat {
        rw subst'
      },
      apply natree.pre.reduces.kernel,
    },
    case stem : x' y' z' {
      repeat {
        rw subst'
      },
      apply natree.pre.reduces.stem,
    },
    case fork : w' x' y' z' {
      repeat {
        rw subst'
      },
      apply natree.pre.reduces.fork,
    },
    case left {
        repeat {
        rw subst'
      },
      apply natree.pre.reduces.left,
      assumption,
    },
    case right {
        repeat {
        rw subst'
      },
      apply natree.pre.reduces.right,
      assumption,
    },
  end

  lemma subst_red_u {x} {u₁ u₂ t} (h : u₁ ↦ u₂) : subst' x u₁ t ≈ subst' x u₂ t := begin
    induction t,
    case node {
      reflexivity,
    },
    case app : t₁ t₂ h₁ h₂ {
      apply natree.pre.equiv.congr,
      assumption,
      assumption,
    },
    case ref {
      repeat {
        rw subst',
      },
      split_ifs,
      apply eqv_gen.rel,
      assumption,
      reflexivity,
    }
  end
  
  def subst1 : char → 𝕋' → 𝕋 → 𝕋 := λ x u, quotient.lift (λ t, ⟦subst' x u t⟧) 
  ( begin
      intros a b h,
      simp,
      induction h,
      case refl {
        refl,
      },
      case symm {
        symmetry,
        assumption,
      },
      case trans {
        transitivity,
        assumption,
        assumption,
      },
      case rel {
        apply subst_red_t,
        assumption,
      },
    end
  )

  def subst : char → 𝕋 → 𝕋 → 𝕋 := λ x, quotient.lift (λ u, subst1 x u) 
  ( begin
      intros a b h,
      simp,
      apply funext,
      intro t,
      induction h,
      case refl {
        refl,
      },
      case symm {
        symmetry,
        assumption,
      },
      case trans {
        transitivity,
        assumption,
        assumption,
      },
      case rel : u₁ u₂ h {
        rw subst1,
        simp,
        have h₁ := quotient.exists_rep t, cases h₁ with t' h₁, rw ←h₁,
        simp,
        apply subst_red_u,
        assumption,
      }
    end
  )

  -- #reduce 'a'.val
  -- #reduce to_bool ('a' = 'b')

  -- inductive LamTree : ℕ → Type
  -- | tree (t : 𝕋) : LamTree 0
  -- | lam {n} (f : 𝕋 → LamTree n) : LamTree (n.succ)

  -- def extract : LamTree 0 → 𝕋 := begin
  --   intro t,
  --   cases t,
  --   assumption,
  -- end

  -- notation λ* x, b := LamTree.lam (λ x, b)

  inductive Lambda (α : Sort*) : ℕ → Sort*
  | const (a : α) : Lambda 0
  | lam {n} (f : α → Lambda n) : Lambda (n.succ)

  def beta {α} {n : ℕ} : Lambda α (n.succ) → α → Lambda α n := begin
    intros l a,
    cases l,
    apply l_f,
    assumption,
  end

  def id_l {α} : Lambda α 1 := begin
    constructor,
    intro a,
    constructor,
    assumption,
  end

  def extract {α} {n : ℕ} : Lambda α 0 → α := begin
    intro l,
    cases l,
    assumption,
  end

end chapter4