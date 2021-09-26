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

  --definition of injective binary functions
  def binary_injective (f : α → β → γ) : Prop :=
    (injective f) ∧ (∀ a : α, injective (f a))
  theorem uncurry_binary_injective (f : α → β → γ) : 
    binary_injective f ↔ injective (uncurry f) := 
    begin
      split,
        rw [uncurry, injective, binary_injective, injective],
        intros h p₁ p₂ h₂,
        cases h,
        have h₃ : f p₁.fst p₁.snd = f p₂.fst p₂.snd := h₂, --any way to avoid this???
        have h₄ := h_right p₁.fst,
        rw injective at h₄,
        have h₅ := h_right p₂.fst,
        rw injective at h₅,

    end

  example (a c : α) (b d : β) (h : a = c) (h₂ : b = d) : (a × b) = (c × d) := sorry

  --equational axioms
  @[simp] axiom kernel : △⬝△⬝y⬝z = y
  @[simp] axiom stem : △⬝(△⬝x)⬝y⬝z = y⬝z⬝(x⬝z)
  @[simp] axiom fork : △⬝(△⬝w⬝x)⬝y⬝z = z⬝w⬝x

  --congruence axioms
  def cong_node : node = node := rfl
  axiom cong_app : binary_injective (⬝)

  --define primitive combinators
  @[simp] def K := △⬝△
  theorem r_K : K⬝y⬝z = y := by simp

  @[simp] def I := △⬝(△⬝△)⬝(△⬝△)
  theorem r_I : I⬝x = x := by simp

  @[simp] def D := △⬝(△⬝△)⬝(△⬝△⬝△)
  theorem r_D : D⬝x⬝y⬝z = y⬝z⬝(x⬝z) := by simp

  @[simp] def d (x : 𝕋) := △⬝(△⬝x)
  theorem d_eq_r_D : d x = D⬝x := by simp

  --derivation of S combinator
  theorem S_exists : ∃ s : 𝕋, (s⬝x⬝y⬝z = x⬝z⬝(y⬝z)) :=
  begin
    split,
    rw ←r_D,
    apply congr_fun,
    sorry,
    sorry,
  end

  #check @injective

  #check @congr_fun
  example (α β : Type*) (f g : α → β) : (∀ z : α, f z = g z) → f = g := by exact funext
  example (α β : Type*) (f g : α → β) : f = g → (∀ z : α, f z = g z) := by exact congr_fun

  @[simp] def S := d(K⬝D) ⬝ (d K ⬝ (K⬝D))
  theorem r_S : S⬝x⬝y⬝z = x⬝z⬝(y⬝z) := by simp

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