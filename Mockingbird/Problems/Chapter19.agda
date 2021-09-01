open import Mockingbird.Forest using (Forest)

-- Aristocratic Birds
module Mockingbird.Problems.Chapter19 {ℓb ℓ} (forest : Forest {ℓb} {ℓ}) where

open import Data.Product using (_×_; _,_; ∃-syntax)
open import Function using (_$_)
open import Level using (_⊔_)
open import Data.Vec using ([]; _∷_)
open import Relation.Unary using (Pred; _∈_; _⊆_; _⊇_)

open Forest forest
open import Mockingbird.Forest.Birds forest
open import Mockingbird.Forest.Combination.Vec forest
open import Mockingbird.Forest.Combination.Vec.Properties forest
open import Mockingbird.Forest.Extensionality forest
import Mockingbird.Problems.Chapter11 forest as Chapter₁₁
import Mockingbird.Problems.Chapter12 forest as Chapter₁₂

problem₁″ : ⦃ _ : HasEagle ⦄ ⦃ _ : HasCardinalOnceRemoved ⦄ ⦃ _ : HasCardinalTwiceRemoved ⦄ ⦃ _ : HasWarbler ⦄ → HasJaybird
problem₁″ = record
  { J = C** ∙ (W ∙ (C* ∙ E))
  ; isJaybird = λ x y z w → begin
      C** ∙ (W ∙ (C* ∙ E)) ∙ x ∙ y ∙ z ∙ w  ≈⟨ isCardinalTwiceRemoved (W ∙ (C* ∙ E)) x y z w ⟩
      W ∙ (C* ∙ E) ∙ x ∙ y ∙ w ∙ z          ≈⟨ congʳ $ congʳ $ congʳ $ isWarbler (C* ∙ E) x ⟩
      C* ∙ E ∙ x ∙ x ∙ y ∙ w ∙ z            ≈⟨ congʳ $ congʳ $ isCardinalOnceRemoved E x x y ⟩
      E ∙ x ∙ y ∙ x ∙ w ∙ z                 ≈⟨ isEagle x y x w z ⟩
      x ∙ y ∙ (x ∙ w ∙ z)                   ∎
  }

problem₁′ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasCardinal ⦄ ⦃ _ : HasWarbler ⦄ → HasJaybird
problem₁′ = record
  { J = B ∙ (B ∙ C) ∙ (W ∙ (B ∙ C ∙ (B ∙ (B ∙ B ∙ B))))
  ; isJaybird = isJaybird ⦃ problem₁″ ⦄
  } where
  instance
    hasEagle = Chapter₁₁.problem₇
    hasCardinalOnceRemoved = Chapter₁₁.problem₃₁
    hasCardinalTwiceRemoved = Chapter₁₁.problem₃₅-C**

problem₁ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ ⦃ _ : HasMockingbird ⦄ → HasJaybird
problem₁ = problem₁′
  where
    instance
      hasCardinal = Chapter₁₁.problem₂₁′
      hasWarbler = Chapter₁₂.problem₇

problem₂ : ⦃ _ : HasJaybird ⦄ ⦃ _ : HasIdentity ⦄ → HasQuixoticBird
problem₂ = record
  { Q₁ = J ∙ I
  ; isQuixoticBird = λ x y z → begin
      J ∙ I ∙ x ∙ y ∙ z    ≈⟨ isJaybird I x y z ⟩
      I ∙ x ∙ (I ∙ z ∙ y)  ≈⟨ congʳ $ isIdentity x ⟩
      x ∙ (I ∙ z ∙ y)      ≈⟨ congˡ $ congʳ $ isIdentity z ⟩
      x ∙ (z ∙ y)          ∎
  }

problem₃ : ⦃ _ : HasQuixoticBird ⦄ ⦃ _ : HasIdentity ⦄ → HasThrush
problem₃ = record
  { T = Q₁ ∙ I
  ; isThrush = λ x y → begin
      Q₁ ∙ I ∙ x ∙ y  ≈⟨ isQuixoticBird I x y ⟩
      I ∙ (y ∙ x)     ≈⟨ isIdentity $ y ∙ x ⟩
      y ∙ x           ∎
  }

problem₄ : ⦃ _ : HasJaybird ⦄ ⦃ _ : HasThrush ⦄ → HasRobin
problem₄ = record
  { R = J ∙ T
  ; isRobin = λ x y z → begin
      J ∙ T ∙ x ∙ y ∙ z    ≈⟨ isJaybird T x y z ⟩
      T ∙ x ∙ (T ∙ z ∙ y)  ≈⟨ isThrush x $ T ∙ z ∙ y ⟩
      T ∙ z ∙ y ∙ x        ≈⟨ congʳ $ isThrush z y ⟩
      y ∙ z ∙ x            ∎
  }

problem₅-C* : ⦃ _ : HasCardinal ⦄ ⦃ _ : HasQuixoticBird ⦄ → HasCardinalOnceRemoved
problem₅-C* = record
  { C* = C ∙ (Q₁ ∙ C)
  ; isCardinalOnceRemoved = λ x y z w → begin
      C ∙ (Q₁ ∙ C) ∙ x ∙ y ∙ z ∙ w  ≈⟨ congʳ $ congʳ $ isCardinal (Q₁ ∙ C) x y ⟩
      Q₁ ∙ C ∙ y ∙ x ∙ z ∙ w        ≈⟨ congʳ $ congʳ $ isQuixoticBird C y x ⟩
      C ∙ (x ∙ y) ∙ z ∙ w           ≈⟨ isCardinal (x ∙ y) z w ⟩
      x ∙ y ∙ w ∙ z                 ∎
  }

problem₅ : ⦃ _ : HasRobin ⦄ ⦃ _ : HasQuixoticBird ⦄ → HasBluebird
problem₅ = record
  { B = C* ∙ Q₁
  ; isBluebird = λ x y z → begin
      C* ∙ Q₁ ∙ x ∙ y ∙ z  ≈⟨ isCardinalOnceRemoved Q₁ x y z ⟩
      Q₁ ∙ x ∙ z ∙ y       ≈⟨ isQuixoticBird x z y ⟩
      x ∙ (y ∙ z)          ∎
  } where
  instance
    hasCardinal = Chapter₁₁.problem₂₁
    hasCardinalOnceRemoved = problem₅-C*

problem₆ : ⦃ _ : HasJaybird ⦄ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄
  → ∃[ J₁ ] (∀ x y z w → J₁ ∙ x ∙ y ∙ z ∙ w ≈ y ∙ x ∙ (w ∙ x ∙ z))
problem₆ =
  ( B ∙ J ∙ T
  , λ x y z w → begin
      B ∙ J ∙ T ∙ x ∙ y ∙ z ∙ w    ≈⟨ (congʳ $ congʳ $ congʳ $ isBluebird J T x) ⟩
      J ∙ (T ∙ x) ∙ y ∙ z ∙ w      ≈⟨ isJaybird (T ∙ x) y z w ⟩
      T ∙ x ∙ y ∙ (T ∙ x ∙ w ∙ z)  ≈⟨ congʳ $ isThrush x y ⟩
      y ∙ x ∙ (T ∙ x ∙ w ∙ z)      ≈⟨ congˡ $ congʳ $ isThrush x w ⟩
      y ∙ x ∙ (w ∙ x ∙ z)          ∎
  )

problem₇ : ⦃ _ : HasCardinal ⦄ ⦃ _ : HasThrush ⦄
  → ∃[ J₁ ] (∀ x y z w → J₁ ∙ x ∙ y ∙ z ∙ w ≈ y ∙ x ∙ (w ∙ x ∙ z))
  → HasMockingbird
problem₇ (J₁ , isJ₁) = record
  { M = C ∙ (C ∙ (C ∙ J₁ ∙ T) ∙ T) ∙ T
  ; isMockingbird = λ x → begin
      C ∙ (C ∙ (C ∙ J₁ ∙ T) ∙ T) ∙ T ∙ x  ≈⟨ isCardinal _ T x ⟩
      C ∙ (C ∙ J₁ ∙ T) ∙ T ∙ x ∙ T        ≈⟨ congʳ $ isCardinal _ T x ⟩
      C ∙ J₁ ∙ T ∙ x ∙ T ∙ T              ≈⟨ congʳ $ congʳ $ isCardinal J₁ T x ⟩
      J₁ ∙ x ∙ T ∙ T ∙ T                  ≈⟨ isJ₁ x T T T ⟩
      T ∙ x ∙ (T ∙ x ∙ T)                 ≈⟨ isThrush x (T ∙ x ∙ T) ⟩
      T ∙ x ∙ T ∙ x                       ≈⟨ congʳ $ isThrush x T ⟩
      T ∙ x ∙ x                           ≈⟨ isThrush x x ⟩
      x ∙ x                               ∎
  }

module _  ⦃ _ : HasJaybird ⦄ ⦃ hasIdentity′ : HasIdentity ⦄ where
  private
    instance
      hasQuixoticBird = problem₂

  hasThrush : HasThrush
  hasThrush = problem₃

  private
    instance
      _ = hasThrush
      hasRobin = problem₄

  hasBluebird : HasBluebird
  hasBluebird = problem₅

  private
    instance
      _ = hasBluebird
      hasCardinal = Chapter₁₁.problem₂₁′

  hasMockingbird : HasMockingbird
  hasMockingbird = problem₇ problem₆

  hasIdentity : HasIdentity
  hasIdentity = hasIdentity′

-- Equality of predicates.
infix 4 _≐_
_≐_ : ∀ {a ℓ} {A : Set a} (P Q : Pred A ℓ) → Set (a ⊔ ℓ)
P ≐ Q = P ⊆ Q × Q ⊆ P

module _ ⦃ _ : Extensional ⦄
         ⦃ _ : HasBluebird ⦄ ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasThrush ⦄
         ⦃ _ : HasIdentity ⦄ ⦃ _ : HasJaybird ⦄ where
  private
    ⟨B,M,T,I⟩ = ⟨ B ∷ M ∷ T ∷ I ∷ [] ⟩
    ⟨J,I⟩ = ⟨ J ∷ I ∷ [] ⟩

  module _ where
    private
      instance
        hasCardinal = Chapter₁₁.problem₂₁′
        hasWarbler = Chapter₁₂.problem₇

      b : B ∈ ⟨B,M,T,I⟩
      b = [ here refl ]

      m : M ∈ ⟨B,M,T,I⟩
      m = [ there (here refl) ]

      t : T ∈ ⟨B,M,T,I⟩
      t = [ there (there (here refl)) ]

      c : C ∈ ⟨B,M,T,I⟩
      c = b ⟨∙⟩ b ⟨∙⟩ t ⟨∙⟩ (b ⟨∙⟩ b ⟨∙⟩ t) ⟨∙⟩ (b ⟨∙⟩ b ⟨∙⟩ t)

      w : W ∈ ⟨B,M,T,I⟩
      w = b ⟨∙⟩ (t ⟨∙⟩ (b ⟨∙⟩ m ⟨∙⟩ (b ⟨∙⟩ b ⟨∙⟩ t))) ⟨∙⟩ (b ⟨∙⟩ b ⟨∙⟩ t)

    ⟨J,I⟩⊆⟨B,M,T,I⟩ : ⟨J,I⟩ ⊆ ⟨B,M,T,I⟩
    ⟨J,I⟩⊆⟨B,M,T,I⟩ [ here x≈J ] = subst′
      (trans x≈J $ ext′ $ ext′ $ ext′ $ ext′ $ trans
        (isJaybird _ _ _ _)
        (sym $ isJaybird ⦃ problem₁′ ⦄ _ _ _ _))
      (b ⟨∙⟩ (b ⟨∙⟩ c) ⟨∙⟩ (w ⟨∙⟩ (b ⟨∙⟩ c ⟨∙⟩ (b ⟨∙⟩ (b ⟨∙⟩ b ⟨∙⟩ b)))))
    ⟨J,I⟩⊆⟨B,M,T,I⟩ [ there (here x≈I) ] = [ there (there (there (here x≈I))) ]
    ⟨J,I⟩⊆⟨B,M,T,I⟩ (x∈⟨J,I⟩ ⟨∙⟩ y∈⟨J,I⟩ ∣ xy≈z) = ⟨J,I⟩⊆⟨B,M,T,I⟩ x∈⟨J,I⟩ ⟨∙⟩ ⟨J,I⟩⊆⟨B,M,T,I⟩ y∈⟨J,I⟩ ∣ xy≈z

  module _ where
    private
      instance
        hasQuixoticBird = problem₂
        hasRobin = problem₄
        hasCardinal = Chapter₁₁.problem₂₁
        hasCardinalOnceRemoved = problem₅-C*

      j : J ∈ ⟨J,I⟩
      j = [ here refl ]

      i : I ∈ ⟨J,I⟩
      i = [ there (here refl) ]

      q₁ : Q₁ ∈ ⟨J,I⟩
      q₁ = j ⟨∙⟩ i

      t : T ∈ ⟨J,I⟩
      t = subst′ (ext′ (ext′ (trans (isThrush _ _) (sym (isThrush ⦃ problem₃ ⦄ _ _))))) $
        j ⟨∙⟩ i ⟨∙⟩ i

      r : R ∈ ⟨J,I⟩
      r = j ⟨∙⟩ t

      c : C ∈ ⟨J,I⟩
      c = r ⟨∙⟩ r ⟨∙⟩ r

      c* : C* ∈ ⟨J,I⟩
      c* = c ⟨∙⟩ (q₁ ⟨∙⟩ c)

      b : B ∈ ⟨J,I⟩
      b = subst′ (ext′ (ext′ (ext′ (trans (isBluebird _ _ _) (sym (isBluebird ⦃ problem₅ ⦄ _ _ _)))))) $
        c* ⟨∙⟩ q₁

      m : M ∈ ⟨J,I⟩
      m = subst′ (ext′ (trans (isMockingbird _) (sym (isMockingbird ⦃ problem₇ problem₆ ⦄ _)))) $
        c ⟨∙⟩ (c ⟨∙⟩ (c ⟨∙⟩ (b ⟨∙⟩ j ⟨∙⟩ t) ⟨∙⟩ t) ⟨∙⟩ t) ⟨∙⟩ t

    ⟨J,I⟩⊇⟨B,M,T,I⟩ : ⟨J,I⟩ ⊇ ⟨B,M,T,I⟩
    ⟨J,I⟩⊇⟨B,M,T,I⟩ [ here x≈B ] = subst′ x≈B b
    ⟨J,I⟩⊇⟨B,M,T,I⟩ [ there (here x≈M) ] = subst′ x≈M m
    ⟨J,I⟩⊇⟨B,M,T,I⟩ [ there (there (here x≈T)) ] = subst′ x≈T t
    ⟨J,I⟩⊇⟨B,M,T,I⟩ [ there (there (there (here x≈I))) ] = [ there (here x≈I) ]
    ⟨J,I⟩⊇⟨B,M,T,I⟩ (x∈⟨B,M,T,I⟩ ⟨∙⟩ y∈⟨B,M,T,I⟩ ∣ xy≈z) = ⟨J,I⟩⊇⟨B,M,T,I⟩ x∈⟨B,M,T,I⟩ ⟨∙⟩ ⟨J,I⟩⊇⟨B,M,T,I⟩ y∈⟨B,M,T,I⟩ ∣ xy≈z

  ⟨J,I⟩≐⟨B,M,T,I⟩ : ⟨ J ∷ I ∷ [] ⟩ ≐ ⟨ B ∷ M ∷ T ∷ I ∷ [] ⟩
  ⟨J,I⟩≐⟨B,M,T,I⟩ = (⟨J,I⟩⊆⟨B,M,T,I⟩ , ⟨J,I⟩⊇⟨B,M,T,I⟩)
