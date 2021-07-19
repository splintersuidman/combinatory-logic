open import Mockingbird.Forest using (Forest)

-- The Forest Without a Name
module Mockingbird.Problems.Chapter16 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; _⇔_; Equivalence)
open import Relation.Binary using (_Respects_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

open Forest forest
import Mockingbird.Problems.Chapter14 forest as Chapter₁₄
open import Mockingbird.Problems.Chapter15 forest using (⇔-¬)

module _ {s} (Sings : Pred Bird s)
         (respects : Sings Respects _≈_)
         (LEM : ∀ x → Sings x ⊎ ¬ Sings x)
         (e : Bird)
         (law₁ : ∀ {x y} → Sings (e ∙ x ∙ y) → Sings y)
         (law₂ : ∀ {x y} → Sings (e ∙ x ∙ y) ⇔ (¬ Sings x))
         (law₃ : ∀ {x y} → Sings (e ∙ x ∙ y) ⇔ (¬ Sings x × Sings y))
         (law₄ : ∀ x → ∃[ y ] Sings y ⇔ Sings (e ∙ y ∙ x)) where

  IsSilent : Pred Bird s
  IsSilent x = ¬ Sings x

  private
    respects′ : IsSilent Respects _≈_
    respects′ x≈y ¬x-sings y-sings = ¬x-sings $ respects (sym x≈y) y-sings

    LEM′ : ∀ x → IsSilent x ⊎ ¬ IsSilent x
    LEM′ x with LEM x
    ... | inj₁ x-sings = inj₂ λ ¬x-sings → ¬x-sings x-sings
    ... | inj₂ ¬x-sings = inj₁ ¬x-sings

    law₁′ : ∀ {x y} → IsSilent y → IsSilent (e ∙ x ∙ y)
    law₁′ ¬y-sings exy-sings = ¬y-sings $ law₁ exy-sings

    law₂′ : ∀ {x y} → ¬ IsSilent x → IsSilent (e ∙ x ∙ y)
    law₂′ = Equivalence.g $ ⇔-¬ law₂

    law₃′ : ∀ {x y} → IsSilent x → IsSilent (e ∙ x ∙ y) → IsSilent y
    law₃′ {x} {y} ¬x-sings ¬exy-sings y-sings = Equivalence.f (⇔-¬ law₃) ¬exy-sings (¬x-sings , y-sings)

    law₄′ : ∀ x → ∃[ y ] IsSilent y ⇔ IsSilent (e ∙ y ∙ x)
    law₄′ x =
      let (y , y-sings⇔eyx-sings) = law₄ x
      in (y , ⇔-¬ y-sings⇔eyx-sings)

  problem : ∀ x → ¬ Sings x
  problem = Chapter₁₄.problem₁ IsSilent respects′ LEM′ e law₁′ law₂′ law₃′ law₄′
