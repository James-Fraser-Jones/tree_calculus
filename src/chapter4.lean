import tactic chapter3

open chapter3

namespace chapter4

  def subst' : char → 𝕋' → 𝕋' → 𝕋'
  | x u (#n y) := if y = natree.pre.index x then u else #n y
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

  lemma subst'_var_match {x} {u} : subst' x u #x = u := begin
    rw natree.pre.ref,
    rw subst',
    split_ifs,
    refl,
    refl,
  end

  @[simp] def kernel' {y z} : ▢◦▢◦y◦z ≈ y := natree.pre.equiv.kernel
  @[simp] def stem' {x y z} : ▢◦(▢◦x)◦y◦z ≈ y◦z◦(x◦z) := natree.pre.equiv.stem
  @[simp] def fork' {w x y z} : ▢◦(▢◦w◦x)◦y◦z ≈ z◦w◦x := natree.pre.equiv.fork
      
  def K' := ▢◦▢
  lemma K'_prop {a b} : K'◦a◦b ≈ a := by simp [K']

  def I' := ▢◦K'◦K'
  lemma I'_prop {a} : I'◦a ≈ a := begin
    rw I',
    transitivity,
    apply stem',
    apply K'_prop,
  end

  def d' (x) := ▢◦(▢◦x)
  lemma d'_prop {x y z} : (d' x)◦y◦z ≈ y◦z◦(x◦z) := by simp [d']

  def D' := ▢◦K'◦(K'◦▢)
  lemma D'_prop {x y z} : D'◦x◦y◦z ≈ y◦z◦(x◦z) := begin
    rw D',
    transitivity,
    apply natree.pre.equiv.congr_left,
    apply natree.pre.equiv.congr_left,
    transitivity,
    apply stem',
    apply natree.pre.equiv.congr_left,
    apply K'_prop,
    apply stem',
  end

  def S' := (d' (K'◦D'))◦((d' K')◦(K'◦D'))
  lemma S'_prop {x y z} : S'◦x◦y◦z ≈ x◦z◦(y◦z) := begin
    rw S',
    transitivity,
    apply natree.pre.equiv.congr_left,
    apply natree.pre.equiv.congr_left,
    transitivity,
    apply d'_prop,
    apply natree.pre.equiv.congr_left,
    transitivity,
    apply d'_prop,
    apply natree.pre.equiv.congr_left,
    apply K'_prop,
    transitivity,
    apply natree.pre.equiv.congr_left,
    transitivity,
    apply D'_prop,
    apply natree.pre.equiv.congr_left,
    apply natree.pre.equiv.congr_left,
    apply K'_prop,
    transitivity,
    apply natree.pre.equiv.congr_left,
    apply natree.pre.equiv.congr_right,
    apply K'_prop,
    apply D'_prop,
  end

  --bracket is not liftable because it "does not preserve the equality induced by the evaluation rules" (as covered in the book)
  def bracket : char → 𝕋' → 𝕋'
  | x (#n y) := if y = natree.pre.index x then I' else K'◦(#n y)
  | x ▢ := K'◦▢
  | x (u◦v) := (d' (bracket x v))◦(bracket x u)
  lemma bracket_prop {x} {t} : (bracket x t)◦(# x) ≈ t := begin
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

  def is_elem : char → 𝕋' → Prop
  | x (#n y) := y = natree.pre.index x
  | x ▢ := false
  | x (t◦u) := is_elem x t ∨ is_elem x u

  instance elem_decidable {x} {t} : decidable (is_elem x t) := begin
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
      rw is_elem,
      exact eq.decidable t (natree.pre.index x),
    },
  end

  lemma is_elem_id {x} : is_elem x (# x) := by rw [natree.pre.ref, is_elem]

  --star abs similarly not liftable
  def star_abs : char → 𝕋' → 𝕋'
  | x ▢ := K'◦▢
  | x (#n y) := if is_elem x (#n y) then I' else K'◦(#n y)
  | x (t◦(#n y)) := if is_elem x (#n y) ∧ ¬ is_elem x t then t else (d' (star_abs x (#n y)))◦(star_abs x t) --special case for eta-reduction
  | x (t◦u) := (d' (star_abs x u))◦(star_abs x t)

  notation `λ* ` x `, ` t := star_abs x t

  lemma star_eta {x} {t} (h : ¬ is_elem x t) : (λ* x, t◦#x) ≈ t := begin
    rw [natree.pre.ref, star_abs],
    split_ifs,
    refl,
    exfalso,
    cases not_and_distrib.mp h_1,

    apply h_2,
    rw is_elem,

    apply h_2,
    assumption,
  end

  lemma star_unchanged {x} {t u} (h : ¬ is_elem x t) : (λ* x, t)◦u ≈ t := begin
    induction t,
    case node {
      rw star_abs,
      apply K'_prop,
    },
    case app : t₁ t₂ h₁ h₂ {
      induction t₂,
      case node {
        rw star_abs,
        transitivity,
        apply d'_prop,
        apply natree.pre.equiv.congr,

        apply h₁,
        intro p,
        apply h,
        rw is_elem,
        left,
        assumption,

        rw star_abs,
        apply K'_prop,
      },
      case app : t₃ t₄ h₃ h₄ {
        rw star_abs,
        transitivity,
        apply d'_prop,
        apply natree.pre.equiv.congr,

        apply h₁,
        intro p,
        apply h,
        rw is_elem,
        left,
        assumption,

        apply h₂,
        intro p,
        apply h,
        rw is_elem,
        right,
        assumption,
      },
      case nat_ref {
        symmetry,
        transitivity,
        apply natree.pre.equiv.congr,

        symmetry,
        apply h₁,
        intro p,
        apply h,
        rw is_elem,
        left,
        assumption,

        symmetry,
        apply h₂,
        intro p,
        apply h,
        rw is_elem,
        right,
        assumption,

        symmetry,

        repeat {rw star_abs},
        split_ifs,

        exfalso,
        apply h,
        rw is_elem,
        right,
        assumption,

        exfalso,
        apply h_2,
        apply and.left,
        assumption,

        transitivity,
        apply d'_prop,
        refl,

        transitivity,
        apply d'_prop,
        refl,
      },
    },
    case nat_ref {
      rw star_abs,
      split_ifs,
      apply K'_prop,
    },
  end

  theorem star_beta {x} {t u} : (λ* x, t)◦u ≈ subst' x u t := begin
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

      induction t₂,
      case node {
        rw star_abs,
        transitivity,
        apply d'_prop,
        refl,
      },
      case app {
        rw star_abs,
        transitivity,
        apply d'_prop,
        refl,
      },
      case nat_ref {
        repeat {
          rw star_abs,
        },
        symmetry,
        split_ifs,

        apply natree.pre.equiv.congr,
        apply star_unchanged,
        exact h_1.2,
        apply I'_prop,

        symmetry,
        apply d'_prop,

        exfalso,
        apply h,
        apply and.left,
        assumption,

        symmetry,
        apply d'_prop,
      },
    },
  end

  def ω : 𝕋 := ⟦λ* 'z', λ* 'f', #'f'◦(#'z'◦#'z'◦#'f')⟧
  example : ω = △⬝(△⬝(I⬝I⬝I)) := sorry

  def Y (f) := ω⬝ω⬝f
  lemma Y_prop {f} : Y f = f⬝(Y f) := begin
    rw Y,
    
    transitivity,
    apply congr, apply congr, refl,
    apply congr, apply congr, refl,
    rw ω,
    refl, refl,

    have h₁ := quotient.exists_rep ω, cases h₁ with ω' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep f, cases h₂ with f' h₂, rw ←h₂,
    repeat {rw ←natree.quot_dist_app},
    apply quotient.sound,

    transitivity,
    apply natree.pre.equiv.congr,
    apply star_beta,
    refl,

    transitivity,
    rw star_abs,
    rw subst',

    transitivity,
    apply natree.pre.equiv.congr_left,
    apply natree.pre.equiv.congr,

    show subst' 'z' ω' (d' (λ* 'f', #'z'◦#'z'◦#'f')) ≈ d' (ω'◦ω'),
    refl,
    show subst' 'z' ω' (λ* 'f', #'f') ≈ I',
    refl,

    transitivity,
    apply d'_prop,

    apply natree.pre.equiv.congr_left,
    apply I'_prop,
  end

<<<<<<< HEAD
  def wait (x y) := (d I)⬝((d (K⬝y))⬝(K⬝x))
  lemma wait_prop {x y z} : (wait x y)⬝z = x⬝y⬝z := by simp [wait, d, I, K]

  def wait1 (x) := (d ((d (K⬝(K⬝x)))⬝((d ((d △)⬝(K⬝△)))⬝(K⬝△))))⬝(K⬝(d (△⬝K⬝K)))
  lemma wait1_prop {x y z} : (wait1 x)⬝y⬝z = x⬝y⬝z := begin
    rw wait1,
    simp [d, I, K],
  end

  def wait2 (x y) := (d ((d (K⬝((d (K⬝y))⬝(K⬝x))))⬝(d ((d K)⬝(K⬝△)))⬝(K⬝△)))⬝(K⬝(d I))

  -- lemma d'_S'_equiv {x y} : S'◦x◦y ≈ (d' y)◦x := begin
=======
    -- lemma d'_S'_equiv {x y} : S'◦x◦y ≈ (d' y)◦x := begin
>>>>>>> 778c83166932e5da4f2a8f42aed421105f02e5a0
  --   rw S',
  --   transitivity,
  --   apply natree.pre.equiv.congr_left,
  --   transitivity,
  --   apply d'_prop,
  --   apply natree.pre.equiv.congr_left,
  --   transitivity,
  --   apply d'_prop,
  --   apply natree.pre.equiv.congr_left,
  --   apply K'_prop,
  --   transitivity,
  --   apply D'_prop,
  --   transitivity,
  --   apply natree.pre.equiv.congr,
  --   apply natree.pre.equiv.congr_left,
  --   apply K'_prop,
  --   apply K'_prop,
  --   apply natree.pre.equiv.congr_left,
  --   rw D',
  --   rw d',
  --   transitivity,
  --   apply stem',
  --   transitivity,
  --   apply natree.pre.equiv.congr_left,
  --   apply K'_prop,
  --   refl,
  -- end

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