open import Mockingbird.Forest using (Forest)

-- Curry’s Lively Bird Forest
module Mockingbird.Problems.Chapter14 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; _⇔_; Equivalence; mk⇔)
open import Level using (_⊔_)
open import Relation.Binary using (_Respects_)
open import Relation.Nullary using (¬_)

open import Mockingbird.Forest.Birds forest
import Mockingbird.Problems.Chapter09 forest as Chapter₉

open Forest forest

module _ {d} {Day : Set d} (_SingsOn_ : Bird → Day → Set d)
         (respects : ∀ {d} → (_SingsOn d) Respects _≈_)
         (P : Bird)
         -- This law of excluded middle is not stated in the problem as one of
         -- the laws, but in the solution given in the book, it is used.
         (LEM : ∀ x d → (x SingsOn d) ⊎ (¬ (x SingsOn d))) where

  module _ (law₁ : ∀ {x y d} → y SingsOn d → (P ∙ x ∙ y) SingsOn d)
           (law₂ : ∀ {x y d} → ¬ (x SingsOn d) → (P ∙ x ∙ y) SingsOn d)
           (law₃ : ∀ {x y d} → x SingsOn d → (P ∙ x ∙ y) SingsOn d → y SingsOn d)
           (law₄ : ∀ x → ∃[ y ] (∀ d → y SingsOn d ⇔ (P ∙ y ∙ x) SingsOn d)) where

    problem₁ : ∀ x d → x SingsOn d
    problem₁ x d = law₃ (proj₂ (law₄-⇐ x) d Pyx-sings) Pyx-sings
      where
        -- If y sings on all days on which x sings, then Pxy sings on all days.
        lemma-Pxy : ∀ y x → (y SingsOn d → x SingsOn d) → (P ∙ y ∙ x) SingsOn d
        lemma-Pxy y x y-sings⇒x-sings with LEM y d
        ... | inj₁ y-sings = law₁ (y-sings⇒x-sings y-sings)
        ... | inj₂ ¬y-sings = law₂ ¬y-sings

        law₄-⇒ : ∀ x → ∃[ y ] (∀ d → y SingsOn d → (P ∙ y ∙ x) SingsOn d)
        law₄-⇒ x =
          let (y , p) = law₄ x
          in (y , λ d → Equivalence.f (p d))

        law₄-⇐ : ∀ x → ∃[ y ] (∀ d → (P ∙ y ∙ x) SingsOn d → y SingsOn d)
        law₄-⇐ x =
          let (y , p) = law₄ x
          in (y , λ d → Equivalence.g (p d))

        y = proj₁ $ law₄ x

        y-sings⇒x-sings : y SingsOn d → x SingsOn d
        y-sings⇒x-sings y-sings = law₃ y-sings $ proj₂ (law₄-⇒ x) d y-sings

        Pyx-sings : (P ∙ y ∙ x) SingsOn d
        Pyx-sings = lemma-Pxy y x y-sings⇒x-sings

  module _ (law₁ : ∀ {x y d} → y SingsOn d → (P ∙ x ∙ y) SingsOn d)
           (law₂ : ∀ {x y d} → ¬ (x SingsOn d) → (P ∙ x ∙ y) SingsOn d)
           (law₃ : ∀ {x y d} → x SingsOn d → (P ∙ x ∙ y) SingsOn d → y SingsOn d)
           ⦃ _ : HasCardinal ⦄ ⦃ _ : HasLark ⦄ where

    problem₂ : ∀ x d → x SingsOn d
    problem₂ = problem₁ law₁ law₂ law₃ $ λ x →
      let -- There exists a bird of which CPx is fond.
          (y , isFond) = Chapter₉.problem₂₅ (C ∙ P ∙ x)

          Pyx≈y : P ∙ y ∙ x ≈ y
          Pyx≈y = begin
            P ∙ y ∙ x      ≈˘⟨ isCardinal P x y ⟩
            C ∙ P ∙ x ∙ y  ≈⟨ isFond ⟩
            y              ∎

          law₄ : ∀ d → y SingsOn d ⇔ (P ∙ y ∙ x) SingsOn d
          law₄ d = mk⇔ (respects (sym Pyx≈y)) (respects Pyx≈y)
      in (y , law₄)

  module _ (law₁ : ∀ {x y d} → y SingsOn d → (P ∙ x ∙ y) SingsOn d)
           (law₂ : ∀ {x y d} → ¬ (x SingsOn d) → (P ∙ x ∙ y) SingsOn d)
           (law₃ : ∀ {x y d} → x SingsOn d → (P ∙ x ∙ y) SingsOn d → y SingsOn d) where

    problem₃ : ∃[ A ] (∀ x y z → A ∙ x ∙ y ∙ z ≈ x ∙ (z ∙ z) ∙ y) → ∀ x d → x SingsOn d
    problem₃ (A , Axyz≈x[zz]y) = problem₁ law₁ law₂ law₃ $ λ x →
      let y = A ∙ P ∙ x ∙ (A ∙ P ∙ x)

          y≈Pyx : y ≈ P ∙ y ∙ x
          y≈Pyx = begin
            y                                  ≈⟨⟩
            A ∙ P ∙ x ∙ (A ∙ P ∙ x)            ≈⟨ Axyz≈x[zz]y P x (A ∙ P ∙ x) ⟩
            P ∙ (A ∙ P ∙ x ∙ (A ∙ P ∙ x)) ∙ x  ≈⟨⟩
            (P ∙ y ∙ x                         ∎)

          law₄ : ∀ d → y SingsOn d ⇔ (P ∙ y ∙ x) SingsOn d
          law₄ d = mk⇔ (respects y≈Pyx) (respects (sym y≈Pyx))
      in (y , law₄)

-- TODO: bonus exercises
