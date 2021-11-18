import tactic chapter3

open chapter3

namespace chapter4

  def subst' : char → 𝕋' → 𝕋' → 𝕋'
  | x u (&n y) := if y = natree.pre.index x then u else &n y
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
    case nat_ref {
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

  @[simp] def kernel' {y z} : ▢◦▢◦y◦z ≈ y := natree.pre.equiv.kernel
  @[simp] def stem' {x y z} : ▢◦(▢◦x)◦y◦z ≈ y◦z◦(x◦z) := natree.pre.equiv.stem
  @[simp] def fork' {w x y z} : ▢◦(▢◦w◦x)◦y◦z ≈ z◦w◦x := natree.pre.equiv.fork

  def K' := ▢◦▢
  lemma K'_prop {a b} : K'◦a◦b ≈ a := by simp [K']

  def I' := ▢◦K'◦K'
  lemma I'_prop {a} : I'◦a ≈ a := 
  begin
    rw I',
    rw K',
    transitivity,
    apply stem',
    apply kernel',
  end

  def d' (x) := ▢◦(▢◦x)
  lemma d'_prop {x y z} : (d' x)◦y◦z ≈ y◦z◦(x◦z) := by simp [d']

  --bracket is not liftable because it "does not preserve the equality induced by the evaluation rules" (as covered in the book)
  def bracket : char → 𝕋' → 𝕋'
  | x (&n y) := if y = natree.pre.index x then I' else K'◦(&n y)
  | x ▢ := K'◦▢
  | x (u◦v) := (d' (bracket x v))◦(bracket x u)
  lemma bracket_prop {x} {t} : (bracket x t)◦(&' x) ≈ t := begin
    induction t,
    case node {
      rw bracket,
      apply K'_prop,
    },
    case app : t₁ t₂ h₁ h₂ {
      rw bracket,
      transitivity,
      apply d'_prop,
      apply natree.pre.equiv.congr,
      assumption,
      assumption,
    },
    case nat_ref {
      rw bracket,
      split_ifs,
      transitivity,
      apply I'_prop,
      rw [natree.pre.ref, h],
      apply K'_prop,
    },
  end

  theorem bracket_beta {x} {t u} : (bracket x t)◦u ≈ subst' x u t := begin
    induction t,
    case node {
      rw [bracket, subst'],
      apply K'_prop,  
    },
    case app : t₁ t₂ h₁ h₂ {
      rw [bracket, subst', d'],
      transitivity,
      apply stem',
      apply natree.pre.equiv.congr,
      assumption,
      assumption,
    },
    case nat_ref {
      rw [bracket, subst'],
      split_ifs,
      apply I'_prop,
      apply K'_prop,
    },
  end

  def elem : char → 𝕋' → Prop
  | x (&n y) := y = natree.pre.index x
  | x ▢ := false
  | x (t◦u) := elem x t ∨ elem x u

  instance elem_decidable {x} {t} : decidable (elem x t) := begin
    induction t,
    case node {
      left,
      intro h,
      cases h,
    },
    case app : t₁ t₂ h₁ h₂ {
      cases h₁,
        cases h₂,
          left,
          intro h,
          cases h,
          apply h₁,
          assumption,
          apply h₂,
          assumption,
        right,
        right,
        assumption,
      cases h₂,
        right,
        left,
        assumption,
      right,
      right,
      assumption,
    },
    case nat_ref {
      rw elem,
      exact eq.decidable t (natree.pre.index x),
    },
  end

  --star abs similarly not liftable
  def star_abs : char → 𝕋' → 𝕋'
  | x ▢ := K'◦▢
  | x (&n y) := if elem x (&n y) then I' else K'◦(&n y)
  --| x (t◦(&n y)) := if elem x (&n y) then t else (d' (star_abs x (&n y)))◦(star_abs x t) --this eta-rule case makes proof much more difficult
  | x (t◦u) := (d' (star_abs x u))◦(star_abs x t)

  notation `λ*` := star_abs

  theorem star_beta {x} {t u} : (λ* x t)◦u ≈ subst' x u t := begin
    induction t,
    case node {
      rw [star_abs, subst'],
      apply K'_prop,
    },
    case nat_ref {
      rw [star_abs, subst'],
      split_ifs,
      apply I'_prop,
      apply K'_prop,
    },
    case app : t₁ t₂ h₁ h₂ {
      rw subst',
      symmetry,
      transitivity,
      apply natree.pre.equiv.congr,
      symmetry,
      assumption,
      symmetry,
      assumption,
      symmetry,

      rw star_abs,
      transitivity,
      apply d'_prop,
      refl,
    },
  end

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

  -- inductive Lambda (α : Sort*) : ℕ → Sort*
  -- | const (a : α) : Lambda 0
  -- | lam {n} (f : α → Lambda n) : Lambda (n.succ)

  -- def beta {α} {n : ℕ} : Lambda α (n.succ) → α → Lambda α n := begin
  --   intros l a,
  --   cases l,
  --   apply l_f,
  --   assumption,
  -- end

  -- def id_l {α} : Lambda α 1 := begin
  --   constructor,
  --   intro a,
  --   constructor,
  --   assumption,
  -- end

  -- def extract {α} {n : ℕ} : Lambda α 0 → α := begin
  --   intro l,
  --   cases l,
  --   assumption,
  -- end

end chapter4