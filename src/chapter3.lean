import tactic --imports extra tactics from mathlib

namespace chapter3

  open string
  open nat
  open option

  inductive tree 
  | node : tree
  | ref : string → tree
  | app : tree → tree → tree
  
  namespace tree
    notation `𝕋` := tree --"\te" --(added to "lean.input.customTranslations" in vscode settings)
    notation `△` := node --"\nd"
    infixl `⬝`:60 := app --"\ap"

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

    lemma depth_well_founded {t t₁ t₂ : 𝕋} (h : t = t₁ ⬝ t₂) : t₁.depth < t.depth ∧ t₂.depth < t.depth :=
    begin
      split;
      conv
      begin
        to_rhs,
        rw [h, depth],
      end;
      apply lt_of_le_of_lt,
        exact le_max_left t₁.depth t₂.depth,
        apply lt_add_one,
      exact le_max_right t₁.depth t₂.depth,
      apply lt_add_one,
    end

    def step : 𝕋 → option 𝕋
    | t := 
      match reduce t with
      | some t' := some t'
      | none := 
        match t with
        | △ := none
        | ref _ := none
        | (t₁ ⬝ t₂) :=
          have t₁.depth < t.depth, from (depth_well_founded (eq.refl t)).1,
          match step t₁ with
          | some t₁' := some (t₁' ⬝ t₂)
          | none := 
            have t₂.depth < t.depth, from (depth_well_founded (eq.refl t)).2,
            match step t₂ with
            | some t₂' := some (t₁ ⬝ t₂')
            | none := none
            end
          end
        end
      end
    using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf depth⟩]} --use "depth" function in well-founded recursion checking

    def normalize : ℕ → 𝕋 → 𝕋
    | 0 t := t
    | (n+1) t := 
      match step t with
      | some t' := normalize n t'
      | none := t
      end

  end tree

  #check is_true

  open tree

  def K := △⬝△
  def I := △⬝(△⬝△)⬝(△⬝△)
  def D := △⬝(△⬝△)⬝(△⬝△⬝△)

end chapter3

-- So I have the following circumstance:
-- ```
-- match t with
--   | (t₁ ⬝ t₂) := ... --need to obtain (h : t = t₁ ⬝ t₂)
--   ...
-- end
-- ```
-- how can I do this?