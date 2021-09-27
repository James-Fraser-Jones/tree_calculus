import tactic

namespace chapter3

  open string
  open nat
  open option
  open function

  --define natural trees
  inductive natree 
  | node : natree
  | ref : string → natree
  | app : natree → natree → natree
  open natree

  --introduce notation
  notation `𝕋` := natree
  notation `△` := natree.node
  infixl `⬝`:60 := natree.app

  variables {α β γ : Type*}
  variables {w x y z : 𝕋}

  --equational axioms
  @[simp] axiom kernel : △⬝△⬝y⬝z = y
  @[simp] axiom stem : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z)
  @[simp] axiom fork : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x

  --congruence axioms?

  --define primitive combinators
  def K := △⬝△
  @[simp] theorem r_K : K⬝y⬝z = y := by simp [K]

  def I := △⬝(△⬝△)⬝(△⬝△)
  @[simp] theorem r_I : I⬝x = x := by simp [I]

  def D := △⬝(△⬝△)⬝(△⬝△⬝△)
  @[simp] theorem r_D : D⬝x⬝y⬝z = y⬝z⬝(x⬝z) := by simp [D]

  @[simp] def d (x : 𝕋) := △⬝(△⬝x)
  theorem d_eq_r_D : d x = D⬝x := by simp [D]

  --derivation of S combinator
  theorem S_exists : ∃ s : 𝕋, s⬝x⬝y⬝z = x⬝z⬝(y⬝z) :=
  begin
    split,
      rw ←r_D,
      apply congr,
        apply congr,
          refl,
        show z = z,
        refl,
      conv
        begin
          to_rhs,
          congr,
          skip,
          rw ←@r_K x y,
        end,
      conv
        begin
          to_rhs,
          rw ←r_D,
        end,
      apply congr,
        apply congr,
          refl,
        show y = y,
        refl,
      conv
        begin
          to_rhs,
          congr,
          congr,
          rw ←@r_K D x,
          skip, 
          skip,
          rw ←@r_K D x,
        end,
      conv
        begin
          to_rhs,
          congr,
          rw ←r_D,
        end,
      conv
        begin
          to_rhs,
          rw ←r_D,
        end,
  end

  def S := d(K⬝D) ⬝ (d K ⬝ (K⬝D))
  @[simp] theorem r_S : S⬝x⬝y⬝z = x⬝z⬝(y⬝z) := by simp [S]

  --define associated functions
  namespace natree

    def iterate : 𝕋 → 𝕋 → ℕ → 𝕋
    | t₁ t₂ 0 := t₂
    | t₁ t₂ (n+1) := t₁ ⬝ iterate t₁ t₂ n

    def from_nat : ℕ → 𝕋
    | n := iterate △ △ n

    def reduce : 𝕋 → option 𝕋
    | (△⬝△⬝y⬝z) := some y
    | (△⬝(△⬝x)⬝y⬝z) := some ((y⬝z)⬝x⬝z)
    | (△⬝(△⬝w⬝x)⬝y⬝z) := some (z⬝w⬝x)
    | _ := none

    def depth : 𝕋 → ℕ
    | (t₁ ⬝ t₂) := max t₁.depth t₂.depth + 1
    | _ := 0

    lemma depth_well_founded (h : z = x ⬝ y) : x.depth < z.depth ∧ y.depth < z.depth :=
    begin
      split;
      conv
      begin
        to_rhs,
        rw [h, depth],
      end;
      apply lt_of_le_of_lt,
        exact le_max_left x.depth y.depth,
        apply lt_add_one,
      exact le_max_right x.depth y.depth,
      apply lt_add_one,
    end

    def step : 𝕋 → option 𝕋
    | t := 
      match reduce t with
      | some t' := some t'
      | none :=
        begin
          cases h₁ : t with _ t₁ t₂,
          exact none, exact none, --no reduction in "node" and "ref" cases
          have h₂ := depth_well_founded h₁, cases h₂, --establish safe recursion hypotheses
          exact (
            match step t₁ with
            | some t₁' := some (t₁' ⬝ t₂)
            | none :=
              match step t₂ with
              | some t₂' := some (t₁ ⬝ t₂')
              | none := none
              end
            end
          ),
        end
      end
    --use "depth" function in well-founded recursion checking
    using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf depth⟩]}

    def normalize : ℕ → 𝕋 → 𝕋
    | 0 t := t
    | (n+1) t := 
      match step t with
      | some t' := normalize n t'
      | none := t
      end

  end natree

end chapter3