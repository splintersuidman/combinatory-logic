open import Mockingbird.Forest using (Forest)

-- Curry’s Lively Bird Forest
module Mockingbird.Problems.Chapter14 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; _⇔_; Equivalence; mk⇔)
open import Level using (_⊔_)
open import Relation.Binary using (_Respects_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

open import Mockingbird.Forest.Birds forest
import Mockingbird.Problems.Chapter09 forest as Chapter₉

open Forest forest

module _ {s} (Sings : Pred Bird s)
         (respects : Sings Respects _≈_)
         -- This law of excluded middle is not stated in the problem as one of
         -- the laws, but in the solution given in the book, it is used.
         (LEM : ∀ x → Sings x ⊎ ¬ Sings x)
         (P : Bird) where

  module _ (law₁ : ∀ {x y} → Sings y → Sings (P ∙ x ∙ y))
           (law₂ : ∀ {x y} → ¬ (Sings x) → Sings (P ∙ x ∙ y))
           (law₃ : ∀ {x y} → Sings x → Sings (P ∙ x ∙ y) → Sings y)
           (law₄ : ∀ x → ∃[ y ] Sings y ⇔ Sings (P ∙ y ∙ x)) where

    problem₁ : ∀ x → Sings x
    problem₁ x = law₃ (proj₂ (law₄-⇐ x) Pyx-sings) Pyx-sings
      where
        -- If y sings on all days on which x sings, then Pxy sings on all days.
        lemma-Pxy : ∀ y x → (Sings y → Sings x) → Sings (P ∙ y ∙ x)
        lemma-Pxy y x y-sings⇒x-sings with LEM y
        ... | inj₁ y-sings = law₁ (y-sings⇒x-sings y-sings)
        ... | inj₂ ¬y-sings = law₂ ¬y-sings

        law₄-⇒ : ∀ x → ∃[ y ] (Sings y → Sings (P ∙ y ∙ x))
        law₄-⇒ x =
          let (y , p) = law₄ x
          in (y , Equivalence.f p)

        law₄-⇐ : ∀ x → ∃[ y ] (Sings (P ∙ y ∙ x) → Sings y)
        law₄-⇐ x =
          let (y , p) = law₄ x
          in (y , Equivalence.g p)

        y = proj₁ $ law₄ x

        y-sings⇒x-sings : Sings y → Sings x
        y-sings⇒x-sings y-sings = law₃ y-sings $ proj₂ (law₄-⇒ x) y-sings

        Pyx-sings : Sings (P ∙ y ∙ x)
        Pyx-sings = lemma-Pxy y x y-sings⇒x-sings

  module _ (law₁ : ∀ {x y} → Sings y → Sings (P ∙ x ∙ y))
           (law₂ : ∀ {x y} → ¬ Sings (x) → Sings (P ∙ x ∙ y))
           (law₃ : ∀ {x y} → Sings x → Sings (P ∙ x ∙ y) → Sings y)
           ⦃ _ : HasCardinal ⦄ ⦃ _ : HasLark ⦄ where

    problem₂ : ∀ x → Sings x
    problem₂ = problem₁ law₁ law₂ law₃ $ λ x →
      let -- There exists a bird of which CPx is fond.
          (y , isFond) = Chapter₉.problem₂₅ (C ∙ P ∙ x)

          Pyx≈y : P ∙ y ∙ x ≈ y
          Pyx≈y = begin
            P ∙ y ∙ x      ≈˘⟨ isCardinal P x y ⟩
            C ∙ P ∙ x ∙ y  ≈⟨ isFond ⟩
            y              ∎

          law₄ : Sings y ⇔ Sings (P ∙ y ∙ x)
          law₄ = mk⇔ (respects (sym Pyx≈y)) (respects Pyx≈y)
      in (y , law₄)

  module _ (law₁ : ∀ {x y} → Sings y → Sings (P ∙ x ∙ y))
           (law₂ : ∀ {x y} → ¬ Sings (x) → Sings (P ∙ x ∙ y))
           (law₃ : ∀ {x y} → Sings x → Sings (P ∙ x ∙ y) → Sings y) where

    problem₃ : ∃[ A ] (∀ x y z → A ∙ x ∙ y ∙ z ≈ x ∙ (z ∙ z) ∙ y) → ∀ x → Sings x
    problem₃ (A , Axyz≈x[zz]y) = problem₁ law₁ law₂ law₃ $ λ x →
      let y = A ∙ P ∙ x ∙ (A ∙ P ∙ x)

          y≈Pyx : y ≈ P ∙ y ∙ x
          y≈Pyx = begin
            y                                  ≈⟨⟩
            A ∙ P ∙ x ∙ (A ∙ P ∙ x)            ≈⟨ Axyz≈x[zz]y P x (A ∙ P ∙ x) ⟩
            P ∙ (A ∙ P ∙ x ∙ (A ∙ P ∙ x)) ∙ x  ≈⟨⟩
            (P ∙ y ∙ x                         ∎)

          law₄ : Sings y ⇔ Sings (P ∙ y ∙ x)
          law₄ = mk⇔ (respects y≈Pyx) (respects (sym y≈Pyx))
      in (y , law₄)

-- -- TODO: bonus exercises
