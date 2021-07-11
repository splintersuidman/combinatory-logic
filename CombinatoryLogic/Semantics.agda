module CombinatoryLogic.Semantics where

open import Relation.Binary using (Rel)

open import CombinatoryLogic.Syntax

-- Kapitel 1, Abschnitt C, §5 (Axiome)
data Axiom : Combinator → Set where
  Q : Axiom (Π ∙ (W ∙ (C ∙ Q)))
  B : Axiom (C ∙ (B ∙ B ∙ (B ∙ B ∙ B)) ∙ B == B ∙ (B ∙ B) ∙ B)
  C : Axiom (C ∙ (B ∙ B ∙ (B ∙ B ∙ B)) ∙ W ∙ C == B ∙ (B ∙ C) ∙ (B ∙ B ∙ B))
  W : Axiom (C ∙ (B ∙ B ∙ B) ∙ W == B ∙ (B ∙ W) ∙ (B ∙ B ∙ B))
  -- NOTE (Curry): this axiom can be proved from the others.
  I₁ : Axiom (C ∙ (B ∙ B ∙ B) ∙ K == B ∙ (B ∙ K) ∙ I)
  BC : Axiom (B ∙ B ∙ C == B ∙ (B ∙ (B ∙ C) ∙ C) ∙ (B ∙ B))
  BW : Axiom (B ∙ B ∙ W == B ∙ (B ∙ (B ∙ (B ∙ (B ∙ W) ∙ W) ∙ (B ∙ C)) ∙ B ∙ (B ∙ B)) ∙ B)
  BK : Axiom (B ∙ B ∙ K == B ∙ K ∙ K)
  CC₁ : Axiom (B ∙ C ∙ C ∙ B ∙ (B ∙ I))
  CC₂ : Axiom (B ∙ (B ∙ (B ∙ C) ∙ C) ∙ (B ∙ C) == B ∙ (B ∙ C ∙ (B ∙ C)) ∙ C)
  CW : Axiom (B ∙ C ∙ W == B ∙ (B ∙ (B ∙ W) ∙ C) ∙ (B ∙ C))
  CK : Axiom (B ∙ C ∙ K == B ∙ K)
  WC : Axiom (B ∙ W ∙ C == W)
  WW : Axiom (B ∙ W ∙ W == B ∙ W ∙ (B ∙ W))
  WK : Axiom (B ∙ W ∙ K == B ∙ I)
  I₂ : Axiom (B ∙ I == I)

-- TODO: fixity definition
infix 4 ⊢_

-- Kapitel 1, Abschnitt C, §4 (Symbolische Festsetzungen), Festsetzung 1
data ⊢_ : Combinator → Set where
  ax : ∀ {X} → Axiom X → ⊢ X

  -- Kapitel 1, Abschnitt C, §6 (Regeln)
  Q₁ : ∀ {X Y} → ⊢ X → ⊢ X == Y → ⊢ Y
  Q₂ : ∀ {X Y Z} → ⊢ X == Y → ⊢ Z ∙ X == Z ∙ Y
  Π : ∀ {X Y} → ⊢ Π ∙ X → ⊢ X ∙ Y
  B : ∀ {X Y Z} → ⊢ B ∙ X ∙ Y ∙ Z == X ∙ (Y ∙ Z)
  C : ∀ {X Y Z} → ⊢ C ∙ X ∙ Y ∙ Z == X ∙ Z ∙ Y
  W : ∀ {X Y} → ⊢ W ∙ X ∙ Y == X ∙ Y ∙ Y
  K : ∀ {X Y} → ⊢ K ∙ X ∙ Y == X
  P : ∀ {X Y} → ⊢ X → ⊢ P ∙ X ∙ Y → ⊢ Y
  ∧ : ∀ {X Y} → ⊢ X → ⊢ Y → ⊢ ∧ ∙ X ∙ Y

-- We introduce convenience notation for the equality defined in Kapitel 1,
-- Abschnitt C, §4 (Symbolische Festsetzungen), Festsetzung 3 (Gleichheit).
_≈_ : Rel Combinator _
X ≈ Y = ⊢ X == Y

infix 0 _[_]

-- An operator that helps write proofs in the style of Curry. Where Curry writes
--   ⟨statement⟩ (⟨rule⟩)
-- we write
--   ⟨statement⟩ [ ⟨rule⟩ ]
--
-- Later, we can also use the Agda standard library's reasoning combinators
-- (e.g. _≈⟨_⟩_) for proving equalities, but not before it is shown that the
-- equality _≈_ is an equivalence relation, which Curry does in propositions 1,
-- 2 and 3 of Kapitel 1, Abschnitt D (Die Eigenschaften der Gleichheit).
_[_] : ∀ {a} (A : Set a) (x : A) → A
_ [ x ] = x
