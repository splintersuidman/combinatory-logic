open import Mockingbird.Forest using (Forest)

-- The Forest Without a Name
module Mockingbird.Problems.Chapter16 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; _⇔_; Equivalence)
open import Relation.Binary using (_Respects_)
open import Relation.Nullary using (¬_)

open Forest forest
import Mockingbird.Problems.Chapter14 forest as Chapter₁₄
open import Mockingbird.Problems.Chapter15 forest using (⇔-¬)

module _ {d} {Day : Set d} (_SingsOn_ : Bird → Day → Set d)
         (respects : ∀ {d} → (_SingsOn d) Respects _≈_)
         (LEM : ∀ x d → (x SingsOn d) ⊎ (¬ x SingsOn d))
         (e : Bird)
         (law₁ : ∀ {x y d} → (e ∙ x ∙ y) SingsOn d → y SingsOn d)
         (law₂ : ∀ {x y d} → (e ∙ x ∙ y) SingsOn d ⇔ (¬ x SingsOn d))
         (law₃ : ∀ {x y d} → (e ∙ x ∙ y) SingsOn d ⇔ (¬ x SingsOn d × y SingsOn d))
         (law₄ : ∀ x → ∃[ y ] (∀ {d} → y SingsOn d ⇔ (e ∙ y ∙ x) SingsOn d)) where

  _SilentOn_ : Bird → Day → Set d
  x SilentOn d = ¬ x SingsOn d

  private
    respects′ : ∀ {d} → (_SilentOn d) Respects _≈_
    respects′ x≈y ¬x-sings y-sings = ¬x-sings $ respects (sym x≈y) y-sings

    LEM′ : ∀ x d → (x SilentOn d) ⊎ (¬ x SilentOn d)
    LEM′ x d with LEM x d
    ... | inj₁ x-sings = inj₂ λ ¬x-sings → ¬x-sings x-sings
    ... | inj₂ ¬x-sings = inj₁ ¬x-sings

    law₁′ : ∀ {x y d} → y SilentOn d → (e ∙ x ∙ y) SilentOn d
    law₁′ ¬y-sings exy-sings = ¬y-sings $ law₁ exy-sings

    law₂′ : ∀ {x y d} → ¬ (x SilentOn d) → (e ∙ x ∙ y) SilentOn d
    law₂′ = Equivalence.g $ ⇔-¬ law₂

    law₃′ : ∀ {x y d} → x SilentOn d → (e ∙ x ∙ y) SilentOn d → y SilentOn d
    law₃′ {x} {y} {d} ¬x-sings ¬exy-sings y-sings = Equivalence.f (⇔-¬ law₃) ¬exy-sings (¬x-sings , y-sings)

    law₄′ : ∀ x → ∃[ y ] (∀ {d} → y SilentOn d ⇔ (e ∙ y ∙ x) SilentOn d)
    law₄′ x =
      let (y , y-sings⇔eyx-sings) = law₄ x
      in (y , ⇔-¬ y-sings⇔eyx-sings)

  problem : ∀ x {d} → ¬ x SingsOn d
  problem = Chapter₁₄.problem₁ _SilentOn_ respects′ LEM′ e law₁′ law₂′ law₃′ law₄′
