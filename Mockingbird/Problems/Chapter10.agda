open import Mockingbird.Forest using (Forest)

-- Is There a Sage Bird?
module Mockingbird.Problems.Chapter10 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Function using (_$_)

open import Mockingbird.Forest.Birds forest

open Forest forest

module _ ⦃ _ : HasComposition ⦄ ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasLark ⦄ where
  private
    hasMockingbirdComposer : ∃[ A ] (∀ x y → A ∙ x ∙ y ≈ x ∙ (M ∙ y))
    hasMockingbirdComposer = (L , isMockingbirdComposer)
      where
        isMockingbirdComposer = λ x y → begin
          L ∙ x ∙ y    ≈⟨ isLark x y ⟩
          x ∙ (y ∙ y)  ≈˘⟨ congˡ $ isMockingbird y ⟩
          x ∙ (M ∙ y)  ∎

  hasSageBird : HasSageBird
  hasSageBird = record
    { Θ = M ∘ L
    ; isSageBird = λ x → begin
        x ∙ ((M ∘ L) ∙ x)        ≈⟨ congˡ $ isComposition M L x ⟩
        x ∙ (M ∙ (L ∙ x))        ≈⟨ congˡ $ isMockingbird (L ∙ x) ⟩
        x ∙ ((L ∙ x) ∙ (L ∙ x))  ≈˘⟨ isLark x (L ∙ x) ⟩
        (L ∙ x) ∙ (L ∙ x)        ≈˘⟨ isMockingbird (L ∙ x) ⟩
        M ∙ (L ∙ x)              ≈˘⟨ isComposition M L x ⟩
        (M ∘ L) ∙ x              ∎
    }

module _ ⦃ _ : HasComposition ⦄ ⦃ _ : HasMockingbird ⦄
         (hasMockingbirdComposer : ∃[ A ] (∀ x y → A ∙ x ∙ y ≈ x ∙ (M ∙ y))) where

  private
    A = proj₁ hasMockingbirdComposer
    [Ax]y≈x[My] = proj₂ hasMockingbirdComposer

    instance
      hasLark : HasLark
      hasLark = record
        { L = A
        ; isLark = λ x y → begin
            (A ∙ x) ∙ y  ≈⟨ [Ax]y≈x[My] x y ⟩
            x ∙ (M ∙ y)  ≈⟨ congˡ $ isMockingbird y ⟩
            x ∙ (y ∙ y)  ∎
        }

  hasSageBird′ : HasSageBird
  hasSageBird′ = hasSageBird
