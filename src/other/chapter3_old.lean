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

  variables {w x y z : 𝕋}

  --equational axioms (should these just be defined as a relation, seperate from equality?)
  @[simp] axiom kernel : △⬝△⬝y⬝z = y
  @[simp] axiom stem : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z)
  @[simp] axiom fork : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x

  /- 
  congruence "axioms"
  cong_node comes for free from rfl,
  cong_app comes for free from congurence of function application with equality (congr_arg2) and the fact that inductive type constructors are injective (app.inj)
  -/
  def cong_node : △ = △ := rfl
  def cong_app : w = y ∧ x = z ↔ w ⬝ x = y ⬝ z := --this is only really a "congruence" in one direction
  begin                                           --also the left direction is actually *false* which means the axioms above introduce inconsistency
    split,
      intro h,
      cases h,
      exact congr_arg2 app h_left h_right,
    intro h,
    exact app.inj h,
  end

  def uhoh : false :=
  begin
    sorry --implement
  end

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
  theorem S_exists : ∀ S : 𝕋, S⬝x⬝y⬝z = x⬝z⬝(y⬝z) → S = d (K⬝D) ⬝ (d K ⬝ (K⬝D)) :=
  begin
    intros S h₁,
    have h₂ : S⬝x⬝y⬝z = D⬝y⬝x⬝z, 
    calc S⬝x⬝y⬝z = x⬝z⬝(y⬝z) : h₁
             ... = D⬝y⬝x⬝z   : by rw ←r_D
    ,
    have h₃ := h₂,
    rw ←cong_app at h₃, cases h₃ with h₃ r,                    --how can we remove r?
    have h₄ : S⬝x⬝y = D⬝(K⬝x)⬝D⬝y,
    calc S⬝x⬝y = D⬝y⬝x        : h₃
           ... = D⬝y⬝(K⬝x⬝y)  : by conv {to_lhs, rw ←@r_K x y} --why is the "conv to_lhs" necessary?
           ... = D⬝(K⬝x)⬝D⬝y  : by rw ←r_D
    ,
    have h₅ := h₄,
    rw ←cong_app at h₅, cases h₅ with h₅ r,
    have h₆ : S⬝x = D⬝(K⬝D)⬝(D⬝K⬝(K⬝D))⬝x,
    calc S⬝x = D⬝(K⬝x)⬝D             : h₅
         ... = (K⬝D⬝x)⬝(K⬝x)⬝(K⬝D⬝x) : by conv {to_lhs, rw ←@r_K D x}
         ... = D⬝K⬝(K⬝D)⬝x⬝(K⬝D⬝x)   : by rw ←r_D
         ... = D⬝(K⬝D)⬝(D⬝K⬝(K⬝D))⬝x : by rw ←r_D
    ,
    have h₇ := h₆,
    rw ←cong_app at h₇, cases h₇ with h₇ r,
    calc   S = D⬝(K⬝D)⬝(D⬝K⬝(K⬝D)) : h₇
         ... = d (K⬝D)⬝(d K⬝(K⬝D)) : by repeat {rw ←d_eq_r_D}
    ,
  end

  def S := d (K⬝D) ⬝ (d K ⬝ (K⬝D))
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