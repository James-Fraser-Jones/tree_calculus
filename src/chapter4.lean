import tactic chapter3

open chapter3

namespace chapter4

  def subst' : char → 𝕋' → 𝕋' → 𝕋'
  | x u (#y) := if y = x then u else #y
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

  lemma subst_ref {x y} {u} : subst x u &y = if x = y then u else &y := begin
    have h₁ := quotient.exists_rep (u), cases h₁ with u' h₁, rw ←h₁,
    rw natree.ref,

    split_ifs,

    rw [subst, h],
    simp,
    rw subst1,
    simp,
    rw subst',
    split_ifs,
    refl,
    refl,

    rw [subst],
    simp,
    rw subst1,
    simp,
    rw subst',
    split_ifs,
    
    exfalso,
    apply h,
    symmetry,
    assumption,
    refl,
  end

  lemma subst_node {x} {u} : subst x u △ = △ := begin
    have h₁ := quotient.exists_rep (u), cases h₁ with u' h₁, rw ←h₁,
    rw natree.node,
    rw subst,
    simp,
    rw subst1,
    simp,
    refl,
  end

  lemma subst_app {x} {u s t} : subst x u (s⬝t) = (subst x u s)⬝(subst x u t) := begin
    have h₁ := quotient.exists_rep (u), cases h₁ with u' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep (s), cases h₂ with s' h₂, rw ←h₂,
    have h₃ := quotient.exists_rep (t), cases h₃ with t' h₃, rw ←h₃,
    rw subst,
    simp,
    rw subst1,
    simp,
    refl,
  end

  --lemma which knows that substituting into a term with no free variables of a specific character is pointless

  --lemma which know that there *will* be no free 'x' variables in a term which starts with "λ* x, ..."

  -----------------------------------------------------------------------------------

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

  -----------------------------------------------------------------------------------

  --bracket is not liftable because it "does not preserve the equality induced by the evaluation rules" (as covered in the book)
  def bracket : char → 𝕋' → 𝕋'
  | x (#y) := if y =  x then I' else K'◦(#y)
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
    case ref {
      rw bracket,
      split_ifs,
      transitivity,
      apply I'_prop,
      rw h,
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
    case ref {
      rw [bracket, subst'],
      split_ifs,
      apply I'_prop,
      apply K'_prop,
    },
  end

  -----------------------------------------------------------------------------------

  def is_elem : char → 𝕋' → Prop
  | x (#y) := y =  x
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
    case ref {
      rw is_elem,
      exact eq.decidable t ( x),
    },
  end

  lemma is_elem_id {x} : is_elem x (# x) := by rw is_elem

  -----------------------------------------------------------------------------------

  --star abs similarly not liftable
  def star_abs' : char → 𝕋' → 𝕋'
  | x ▢ := K'◦▢
  | x (#y) := if is_elem x (#y) then I' else K'◦(#y)
  | x (t◦(#y)) := if is_elem x (#y) ∧ ¬ is_elem x t then t else (d' (star_abs' x (#y)))◦(star_abs' x t) --special case for eta-reduction
  | x (t◦u) := (d' (star_abs' x u))◦(star_abs' x t)

  notation `λ** ` x `, ` t := star_abs' x t

  def star_abs (x) (t) := ⟦λ** x, t⟧ -- <-- is this actually useful??
  
  notation `λ* ` x `, ` t := star_abs x t

  lemma star_eta' {x} {t} (h : ¬ is_elem x t) : (λ** x, t◦#x) ≈ t := begin
    rw star_abs',
    split_ifs,
    refl,
    exfalso,
    cases not_and_distrib.mp h_1,

    apply h_2,
    rw is_elem,

    apply h_2,
    assumption,
  end

  lemma star_unchanged' {x} {t u} (h : ¬ is_elem x t) : (λ** x, t)◦u ≈ t := begin
    induction t,
    case node {
      rw star_abs',
      apply K'_prop,
    },
    case app : t₁ t₂ h₁ h₂ {
      induction t₂,
      case node {
        rw star_abs',
        transitivity,
        apply d'_prop,
        apply natree.pre.equiv.congr,

        apply h₁,
        intro p,
        apply h,
        rw is_elem,
        left,
        assumption,

        rw star_abs',
        apply K'_prop,
      },
      case app : t₃ t₄ h₃ h₄ {
        rw star_abs',
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
      case ref {
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

        repeat {rw star_abs'},
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
    case ref {
      rw star_abs',
      split_ifs,
      apply K'_prop,
    },
  end

  theorem star_beta' {x} {t u} : (λ** x, t)◦u ≈ subst' x u t := begin
    induction t,
    case node {
      rw [star_abs', subst'],
      apply K'_prop,
    },
    case ref {
      rw [star_abs', subst'],
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
        rw star_abs',
        transitivity,
        apply d'_prop,
        refl,
      },
      case app {
        rw star_abs',
        transitivity,
        apply d'_prop,
        refl,
      },
      case ref {
        repeat {
          rw star_abs',
        },
        symmetry,
        split_ifs,

        apply natree.pre.equiv.congr,
        apply star_unchanged',
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

  theorem star_beta {x} {t} {u} : (λ* x, t)⬝u = subst x u ⟦t⟧ := begin
    have h₁ := quotient.exists_rep y, cases h₁ with y' h₁, rw ←h₁,
  end

  -----------------------------------------------------------------------------------

  def ω : 𝕋 := ⟦λ** 'z', λ** 'f', #'f'◦(#'z'◦#'z'◦#'f')⟧

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
    apply star_beta',
    refl,

    transitivity,
    rw star_abs',
    rw subst',

    transitivity,
    apply natree.pre.equiv.congr_left,
    apply natree.pre.equiv.congr,

    show subst' 'z' ω' (d' (λ** 'f', #'z'◦#'z'◦#'f')) ≈ d' (ω'◦ω'),
    refl,
    show subst' 'z' ω' (λ** 'f', #'f') ≈ I',
    refl,

    transitivity,
    apply d'_prop,

    apply natree.pre.equiv.congr_left,
    apply I'_prop,
  end

  def wait (x y) := (d I)⬝((d (K⬝y))⬝(K⬝x))
  lemma wait_prop {x y z} : (wait x y)⬝z = x⬝y⬝z := by simp [wait, d, I, K]

  def wait1 (x) := d (d (K⬝(K⬝x))⬝(d ((d K)⬝(K⬝△))⬝(K⬝△)))⬝(K⬝(d (△⬝K⬝K)))
  lemma wait1_prop {x y z} : (wait1 x)⬝y⬝z = x⬝y⬝z := by simp [wait1, d, I, K]

  def self_apply := (d I)⬝I
  lemma self_apply_prop {x} : self_apply⬝x = x⬝x := by simp [self_apply, d, I, K]

  def Z (f) := (wait1 self_apply)⬝((d (wait1 self_apply)) ⬝ (K⬝f))
  lemma Z_prop {f x} : (Z f)⬝x = f⬝(Z f)⬝x := by simp [Z, wait1, self_apply, d, I, K]

  def swap (f) := (d K)⬝(K⬝(((d (K⬝f))⬝D)))
  lemma swap_prop {f x y} : (swap f)⬝x⬝y = f⬝y⬝x := by simp [swap, d, D, I, K]

  def Y₂ (f) := Z (swap f)

  theorem fixpoint_function {f x} : (Y₂ f)⬝x = f⬝x⬝(Y₂ f) := by simp [Y₂, Z, swap, wait1, self_apply, d, D, I, K]
  lemma Y₂_prop {f x} : (Y₂ f)⬝x = f⬝x⬝(Y₂ f) := fixpoint_function

  def plus : 𝕋 := Y₂ ⟦λ** 'm', λ** 'p', ▢◦#'m'◦I'◦(K'◦(λ** 'x', λ** 'n', K'◦(#'p'◦#'x'◦#'n')))⟧

  def t_nil := △
  def t_cons (h t) := △⬝h⬝t

  def t_head := ⟦λ** 'x', (((▢◦#'x')◦(K'◦I'))◦K')⟧
  lemma head_prop {h t} : t_head⬝(t_cons h t) = h := begin
    rw [t_head, t_cons],
    have h₁ := quotient.exists_rep h, cases h₁ with h' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep t, cases h₂ with t' h₂, rw ←h₂,
    rw natree.node,
    repeat {rw ←quot_dist_app},
    apply quotient.sound,
    transitivity,
    apply star_beta',
    repeat {rw subst'},
    show (▢◦(▢◦h'◦t')◦(K'◦I')◦K') ≈ h',
    transitivity,
    apply natree.pre.equiv.lift_reduces_to,
    apply natree.pre.reduces.fork,
    apply K'_prop,
  end

  def t_tail := ⟦λ** 'x', (((▢◦#'x')◦(K'◦I'))◦(K'◦I'))⟧
  lemma tail_prop {h t} : t_tail⬝(t_cons h t) = t := begin
    rw [t_tail, t_cons],
    have h₁ := quotient.exists_rep h, cases h₁ with h' h₁, rw ←h₁,
    have h₂ := quotient.exists_rep t, cases h₂ with t' h₂, rw ←h₂,
    rw natree.node,
    repeat {rw ←quot_dist_app},
    apply quotient.sound,
    transitivity,
    apply star_beta',
    repeat {rw subst'},
    transitivity,
    apply natree.pre.equiv.congr,
    apply natree.pre.equiv.congr,
    apply natree.pre.equiv.congr,
    refl,
    show subst' 'x' (▢◦h'◦t') (#'x') ≈ (▢◦h'◦t'),
    refl,
    show subst' 'x' (▢◦h'◦t') K'◦subst' 'x' (▢◦h'◦t') I' ≈ K'◦I',
    refl,
    show subst' 'x' (▢◦h'◦t') K'◦subst' 'x' (▢◦h'◦t') I' ≈ K'◦I',
    refl,
    transitivity,
    apply natree.pre.equiv.lift_reduces_to,
    apply natree.pre.reduces.fork,
    transitivity,
    apply natree.pre.equiv.congr_left,
    apply K'_prop,
    apply I'_prop,
  end

  def t_nil' := ▢
  def t_cons' (h t) := ▢◦h◦t

  def list_map_swap := ⟦(λ** 'x', ▢◦#'x'◦(K'◦(K'◦t_nil')))◦(λ** 'h', λ** 't', λ** 'm', λ** 'f', t_cons' (#'f'◦#'h') (#'m'◦#'f'◦#'t'))⟧
  def list_map := swap (Y₂ list_map_swap)
  lemma list_map_prop_nil {f} : list_map⬝f⬝t_nil = t_nil := begin
    --??? (we need to stop having to delve under the quotient whenever something is defined using star_abs')
    --if a 𝕋' has no free variables, it is a combinator, and can be turned into an expression with no variables at all, which can then be simped
    rw [list_map, list_map_swap],

  end
  lemma list_map_prop_cons {f h t} : list_map⬝f⬝(t_cons h t) = t_cons (f⬝h) (list_map⬝f⬝t) := begin
    --???
    sorry
  end

end chapter4