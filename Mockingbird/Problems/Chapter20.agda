open import Mockingbird.Forest using (Forest)

-- Craig’s Discovery
module Mockingbird.Problems.Chapter20 {ℓb ℓ} (forest : Forest {ℓb} {ℓ}) where

open import Data.Product using (_,_)
open import Data.Vec using ([]; _∷_)
open import Function using (_$_)
open import Relation.Unary using (Pred; _∈_; _⊆_; _⊇_)

open Forest forest
open import Mockingbird.Forest.Birds forest
open import Mockingbird.Forest.Combination.Vec forest
open import Mockingbird.Forest.Combination.Vec.Properties forest
open import Mockingbird.Forest.Extensionality forest
import Mockingbird.Problems.Chapter11 forest as Chapter₁₁
open import Mockingbird.Problems.Chapter19 forest using (_≐_)

problem₁ : ⦃ _ : HasGoldfinch ⦄ ⦃ _ : HasIdentity ⦄ → HasQuirkyBird
problem₁ = record
  { Q₃ = G ∙ I
  ; isQuirkyBird = λ x y z → begin
      G ∙ I ∙ x ∙ y ∙ z  ≈⟨ isGoldfinch I x y z ⟩
      I ∙ z ∙ (x ∙ y)    ≈⟨ congʳ $ isIdentity z ⟩
      z ∙ (x ∙ y)        ∎
  }

problem₂′ : ⦃ _ : HasQuirkyBird ⦄ ⦃ _ : HasIdentity ⦄ → HasThrush
problem₂′ = record
  { T = Q₃ ∙ I
  ; isThrush = λ x y → begin
      Q₃ ∙ I ∙ x ∙ y  ≈⟨ isQuirkyBird I x y ⟩
      y ∙ (I ∙ x)     ≈⟨ congˡ $ isIdentity x ⟩
      y ∙ x           ∎
  }

problem₂ : ⦃ _ : HasGoldfinch ⦄ ⦃ _ : HasIdentity ⦄ → HasThrush
problem₂ = record
  { T = G ∙ I ∙ I
  ; isThrush = isThrush ⦃ problem₂′ ⦄
  } where
  instance hasQuirkyBird = problem₁

problem₃ : ⦃ _ : HasGoldfinch ⦄ ⦃ _ : HasIdentity ⦄ → HasCardinal
problem₃ = record
  { C = G ∙ G ∙ I ∙ I
  ; isCardinal = λ x y z → begin
      G ∙ G ∙ I ∙ I ∙ x ∙ y ∙ z  ≈⟨ congʳ $ congʳ $ isGoldfinch G I I x ⟩
      G ∙ x ∙ (I ∙ I) ∙ y ∙ z    ≈⟨ isGoldfinch x (I ∙ I) y z ⟩
      x ∙ z ∙ (I ∙ I ∙ y)        ≈⟨ congˡ $ congʳ $ isIdentity I ⟩
      x ∙ z ∙ (I ∙ y)            ≈⟨ congˡ $ isIdentity y ⟩
      x ∙ z ∙ y                  ∎
  }

problem₄-Q : ⦃ _ : HasGoldfinch ⦄ ⦃ _ : HasIdentity ⦄ → HasQueerBird
problem₄-Q = record
  { Q = G ∙ R ∙ Q₃
  ; isQueerBird = λ x y z → begin
      G ∙ R ∙ Q₃ ∙ x ∙ y ∙ z  ≈⟨ congʳ $ isGoldfinch R Q₃ x y ⟩
      R ∙ y ∙ (Q₃ ∙ x) ∙ z    ≈⟨ isRobin y (Q₃ ∙ x) z ⟩
      Q₃ ∙ x ∙ z ∙ y          ≈⟨ isQuirkyBird x z y ⟩
      y ∙ (x ∙ z)             ∎
  } where
  instance
    hasQuirkyBird = problem₁
    hasCardinal = problem₃
    hasRobin = Chapter₁₁.problem₂₃

problem₄-B : ⦃ _ : HasGoldfinch ⦄ ⦃ _ : HasIdentity ⦄ → HasBluebird
problem₄-B = record
  { B = C ∙ Q
  ; isBluebird = λ x y z → begin
      C ∙ Q ∙ x ∙ y ∙ z  ≈⟨ congʳ $ isCardinal Q x y ⟩
      Q ∙ y ∙ x ∙ z      ≈⟨ isQueerBird y x z ⟩
      x ∙ (y ∙ z)        ∎
  } where
  instance
    hasCardinal = problem₃
    hasQueerBird = problem₄-Q

module _ ⦃ _ : Extensional ⦄
         ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄
         ⦃ _ : HasIdentity ⦄ ⦃ _ : HasGoldfinch ⦄ where
  ⟨B,T,I⟩ = ⟨ B ∷ T ∷ I ∷ [] ⟩
  ⟨G,I⟩ = ⟨ G ∷ I ∷ [] ⟩

  module _ where
    private
      instance
        hasCardinal = Chapter₁₁.problem₂₁-bonus
        hasDove = Chapter₁₁.problem₅

      hasGoldfinch = Chapter₁₁.problem₄₇

      b : B ∈ ⟨B,T,I⟩
      b = [ here refl ]

      t : T ∈ ⟨B,T,I⟩
      t = [ there (here refl) ]

      i : I ∈ ⟨B,T,I⟩
      i = [ there (there (here refl)) ]

      c : C ∈ ⟨B,T,I⟩
      c = b ⟨∙⟩ (t ⟨∙⟩ (b ⟨∙⟩ b ⟨∙⟩ t)) ⟨∙⟩ (b ⟨∙⟩ b ⟨∙⟩ t)

      d : D ∈ ⟨B,T,I⟩
      d = b ⟨∙⟩ b

      g : G ∈ ⟨B,T,I⟩
      g = subst′
        (ext′ $ ext′ $ ext′ $ ext′ $ trans
          (isGoldfinch _ _ _ _)
          (sym $ isGoldfinch ⦃ hasGoldfinch ⦄ _ _ _ _))
        (d ⟨∙⟩ c)

    ⟨G,I⟩⊆⟨B,T,I⟩ : ⟨G,I⟩ ⊆ ⟨B,T,I⟩
    ⟨G,I⟩⊆⟨B,T,I⟩ [ here x≈G ] = subst′ x≈G g
    ⟨G,I⟩⊆⟨B,T,I⟩ [ there (here x≈I) ] = [ there (there (here x≈I)) ]
    ⟨G,I⟩⊆⟨B,T,I⟩ (x∈⟨G,I⟩ ⟨∙⟩ y∈⟨G,I⟩ ∣ xy≈z) =
      ⟨G,I⟩⊆⟨B,T,I⟩ x∈⟨G,I⟩ ⟨∙⟩ ⟨G,I⟩⊆⟨B,T,I⟩ y∈⟨G,I⟩ ∣ xy≈z

  module _ where
    private
      g : G ∈ ⟨G,I⟩
      g = [ here refl ]

      i : I ∈ ⟨G,I⟩
      i = [ there (here refl) ]

      t : T ∈ ⟨G,I⟩
      t = subst′
        (ext′ $ ext′ $ trans
          (isThrush _ _)
          (sym $ isThrush ⦃ problem₂ ⦄ _ _))
        (g ⟨∙⟩ i ⟨∙⟩ i)

      b : B ∈ ⟨G,I⟩
      b = subst′
        (ext′ $ ext′ $ ext′ $ trans
          (isBluebird _ _ _)
          (sym $ isBluebird ⦃ problem₄-B ⦄ _ _ _))
        (g ⟨∙⟩ g ⟨∙⟩ i ⟨∙⟩ i ⟨∙⟩ (g ⟨∙⟩ (g ⟨∙⟩ g ⟨∙⟩ i ⟨∙⟩ i ⟨∙⟩ (g ⟨∙⟩ g ⟨∙⟩ i ⟨∙⟩ i)) ⟨∙⟩ (g ⟨∙⟩ i)))

    ⟨G,I⟩⊇⟨B,T,I⟩ : ⟨G,I⟩ ⊇ ⟨B,T,I⟩
    ⟨G,I⟩⊇⟨B,T,I⟩ [ here x≈B ] = subst′ x≈B b
    ⟨G,I⟩⊇⟨B,T,I⟩ [ there (here x≈T) ] = subst′ x≈T t
    ⟨G,I⟩⊇⟨B,T,I⟩ [ there (there (here x≈I)) ] = [ there (here x≈I) ]
    ⟨G,I⟩⊇⟨B,T,I⟩ (x∈⟨B,T,I⟩ ⟨∙⟩ y∈⟨B,T,I⟩ ∣ xy≈z) = ⟨G,I⟩⊇⟨B,T,I⟩ x∈⟨B,T,I⟩ ⟨∙⟩ ⟨G,I⟩⊇⟨B,T,I⟩ y∈⟨B,T,I⟩ ∣ xy≈z

  ⟨G,I⟩≐⟨B,T,I⟩ : ⟨ G ∷ I ∷ [] ⟩ ≐ ⟨ B ∷ T ∷ I ∷ [] ⟩
  ⟨G,I⟩≐⟨B,T,I⟩ = (⟨G,I⟩⊆⟨B,T,I⟩ , ⟨G,I⟩⊇⟨B,T,I⟩)
