open import Mockingbird.Forest using (Forest)

-- Mockingbirds, Warblers, and Starlings
module Mockingbird.Problems.Chapter12 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Product using (_×_; _,_; proj₁; ∃-syntax)
open import Function using (_$_)

open import Mockingbird.Forest.Birds forest
import Mockingbird.Problems.Chapter11 forest as Chapter₁₁

open Forest forest

problem₁ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasMockingbird ⦄ → HasDoubleMockingbird
problem₁ = record
  { M₂ = B ∙ M
  ; isDoubleMockingbird = λ x y → begin
     B ∙ M ∙ x ∙ y    ≈⟨ isBluebird M x y ⟩
     M ∙ (x ∙ y)      ≈⟨ isMockingbird (x ∙ y) ⟩
     x ∙ y ∙ (x ∙ y)  ∎
  }

problem₂-BCM : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ ⦃ _ : HasMockingbird ⦄ → HasLark
problem₂-BCM = record
  { L = C ∙ B ∙ M
  ; isLark = λ x y → begin
      C ∙ B ∙ M ∙ x ∙ y  ≈⟨ congʳ $ isCardinal B M x ⟩
      B ∙ x ∙ M ∙ y      ≈⟨ isBluebird x M y ⟩
      x ∙ (M ∙ y)        ≈⟨ congˡ $ isMockingbird y ⟩
      x ∙ (y ∙ y)        ∎
  } where instance hasCardinal = Chapter₁₁.problem₂₁′

problem₂-BRM : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ ⦃ _ : HasMockingbird ⦄ → HasLark
problem₂-BRM = record
  { L = R ∙ M ∙ B
  ; isLark = λ x y → begin
      R ∙ M ∙ B ∙ x ∙ y  ≈⟨ congʳ $ isRobin M B x ⟩
      B ∙ x ∙ M ∙ y      ≈⟨ isBluebird x M y ⟩
      x ∙ (M ∙ y)        ≈⟨ congˡ $ isMockingbird y ⟩
      x ∙ (y ∙ y)        ∎
  } where instance hasRobin = Chapter₁₁.problem₂₀

problem₃ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasWarbler ⦄ → HasLark
problem₃ = record
  { L = B ∙ W ∙ B
  ; isLark = λ x y → begin
      B ∙ W ∙ B ∙ x ∙ y  ≈⟨ congʳ $ isBluebird W B x ⟩
      W ∙ (B ∙ x) ∙ y    ≈⟨ isWarbler (B ∙ x) y ⟩
      B ∙ x ∙ y ∙ y      ≈⟨ isBluebird x y y ⟩
      x ∙ (y ∙ y)        ∎
  }

problem₄ : ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasQueerBird ⦄ → HasLark
problem₄ = record
  { L = Q ∙ M
  ; isLark = λ x y → begin
      Q ∙ M ∙ x ∙ y  ≈⟨ isQueerBird M x y ⟩
      x ∙ (M ∙ y)    ≈⟨ congˡ $ isMockingbird y ⟩
      x ∙ (y ∙ y)    ∎
  }

problem₅ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasRobin ⦄ ⦃ _ : HasMockingbird ⦄ → HasConverseWarbler
problem₅ = record
  { W′ = M₂ ∙ R
  ; isConverseWarbler = λ x y → begin
      M₂ ∙ R ∙ x ∙ y       ≈⟨ congʳ $ isDoubleMockingbird R x ⟩
      R ∙ x ∙ (R ∙ x) ∙ y  ≈⟨ isRobin x (R ∙ x) y ⟩
      R ∙ x ∙ y ∙ x        ≈⟨ isRobin x y x ⟩
      y ∙ x ∙ x            ∎
  } where instance hasDoubleMockingbird = problem₁

problem₆′ : ⦃ _ : HasCardinal ⦄ ⦃ _ : HasConverseWarbler ⦄ → HasWarbler
problem₆′ = record
  { W = C ∙ W′
  ; isWarbler = λ x y → begin
      C ∙ W′ ∙ x ∙ y ≈⟨ isCardinal W′ x y ⟩
      W′ ∙ y ∙ x     ≈⟨ isConverseWarbler y x ⟩
      x ∙ y ∙ y      ∎
  }

problem₆ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasRobin ⦄ ⦃ _ : HasCardinal ⦄ ⦃ _ : HasMockingbird ⦄ → HasWarbler
problem₆ = record
  { W = C ∙ (B ∙ M ∙ R)
  ; isWarbler = λ x y → begin
      C ∙ (B ∙ M ∙ R) ∙ x ∙ y  ≈⟨⟩
      C ∙ (M₂ ∙ R) ∙ x ∙ y     ≈⟨⟩
      C ∙ W′ ∙ x ∙ y           ≈⟨⟩
      W ∙ x ∙ y                ≈⟨ isWarbler x y ⟩
      x ∙ y ∙ y                ∎
  } where
  instance
    hasDoubleMockingbird = problem₁
    hasConverseWarbler = problem₅
    hasWarbler = problem₆′

problem₇ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ ⦃ _ : HasMockingbird ⦄ → HasWarbler
problem₇ = record
  { W = B ∙ (T ∙ (B ∙ M ∙ (B ∙ B ∙ T))) ∙ (B ∙ B ∙ T)
  ; isWarbler = λ x y → begin
      B ∙ (T ∙ (B ∙ M ∙ (B ∙ B ∙ T))) ∙ (B ∙ B ∙ T) ∙ x ∙ y  ≈˘⟨ congʳ $ congʳ $ isWarbler′ ⟩
      W ∙ x ∙ y                                              ≈⟨ isWarbler x y ⟩
      x ∙ y ∙ y                                              ∎
  } where
  instance
    hasRobin = Chapter₁₁.problem₂₀
    hasCardinal = Chapter₁₁.problem₂₁-bonus
    hasWarbler = problem₆

  isWarbler′ : W ≈ B ∙ (T ∙ (B ∙ M ∙ (B ∙ B ∙ T))) ∙ (B ∙ B ∙ T)
  isWarbler′ = begin
    W                                                            ≈⟨⟩
    C ∙ (B ∙ M ∙ R)                                              ≈⟨⟩
    C ∙ (B ∙ M ∙ (B ∙ B ∙ T))                                    ≈⟨⟩
    B ∙ (T ∙ (B ∙ B ∙ T)) ∙ (B ∙ B ∙ T) ∙ (B ∙ M ∙ (B ∙ B ∙ T))  ≈⟨ isBluebird (T ∙ (B ∙ B ∙ T)) (B ∙ B ∙ T) (B ∙ M ∙ (B ∙ B ∙ T)) ⟩
    T ∙ (B ∙ B ∙ T) ∙ (B ∙ B ∙ T ∙ (B ∙ M ∙ (B ∙ B ∙ T)))        ≈⟨ isThrush (B ∙ B ∙ T) (B ∙ B ∙ T ∙ (B ∙ M ∙ (B ∙ B ∙ T))) ⟩
    B ∙ B ∙ T ∙ (B ∙ M ∙ (B ∙ B ∙ T)) ∙ (B ∙ B ∙ T)              ≈⟨ congʳ $ isBluebird B T (B ∙ M ∙ (B ∙ B ∙ T)) ⟩
    B ∙ (T ∙ (B ∙ M ∙ (B ∙ B ∙ T))) ∙ (B ∙ B ∙ T)                ∎

-- TODO: other expression in problem 7.

-- NOTE: the bluebird B is not necessary.
problem₈ : ⦃ _ : HasThrush ⦄ ⦃ _ : HasWarbler ⦄ → HasMockingbird
problem₈ = record
  { M = W ∙ T
  ; isMockingbird = λ x → begin
      W ∙ T ∙ x  ≈⟨ isWarbler T x ⟩
      T ∙ x ∙ x  ≈⟨ isThrush x x ⟩
      x ∙ x      ∎
  }

problem₉-W* : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ ⦃ _ : HasMockingbird ⦄ → HasWarblerOnceRemoved
problem₉-W* = record
  { W* = B ∙ W
  ; isWarblerOnceRemoved = λ x y z → begin
      B ∙ W ∙ x ∙ y ∙ z  ≈⟨ congʳ $ isBluebird W x y ⟩
      W ∙ (x ∙ y) ∙ z    ≈⟨ isWarbler (x ∙ y) z ⟩
      x ∙ y ∙ z ∙ z      ∎
  } where instance hasWarbler = problem₇

problem₉-W** : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ ⦃ _ : HasMockingbird ⦄ → HasWarblerTwiceRemoved
problem₉-W** = record
  { W** = B ∙ W*
  ; isWarblerTwiceRemoved = λ x y z w → begin
      B ∙ W* ∙ x ∙ y ∙ z ∙ w  ≈⟨ congʳ $ congʳ $ isBluebird W* x y ⟩
      W* ∙ (x ∙ y) ∙ z ∙ w    ≈⟨ isWarblerOnceRemoved (x ∙ y) z w ⟩
      x ∙ y ∙ z ∙ w ∙ w       ∎
  } where
  instance
    hasWarbler = problem₇
    hasWarblerOnceRemoved = problem₉-W*

problem₁₀ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasCardinal ⦄ ⦃ _ : HasWarbler ⦄ → HasHummingbird
problem₁₀ = record
  { H = B ∙ W ∙ (B ∙ C)
  ; isHummingbird = λ x y z → begin
      B ∙ W ∙ (B ∙ C) ∙ x ∙ y ∙ z   ≈⟨ congʳ $ congʳ $ isBluebird W (B ∙ C) x ⟩
      W ∙ (B ∙ C ∙ x) ∙ y ∙ z       ≈⟨ congʳ $ isWarbler (B ∙ C ∙ x) y ⟩
      B ∙ C ∙ x ∙ y ∙ y ∙ z         ≈⟨ congʳ $ congʳ $ isBluebird C x y ⟩
      C ∙ (x ∙ y) ∙ y ∙ z           ≈⟨ isCardinal (x ∙ y) y z ⟩
      x ∙ y ∙ z ∙ y                 ∎
  }

problem₁₁ : ⦃ _ : HasRobin ⦄ ⦃ _ : HasHummingbird ⦄ → HasWarbler
problem₁₁ = problem₆′
  where
    instance
      hasCardinal = Chapter₁₁.problem₂₁

      hasConverseWarbler : HasConverseWarbler
      hasConverseWarbler = record
        { W′ = H ∙ R
        ; isConverseWarbler = λ x y → begin
            H ∙ R ∙ x ∙ y  ≈⟨ isHummingbird R x y ⟩
            R ∙ x ∙ y ∙ x  ≈⟨ isRobin x y x ⟩
            y ∙ x ∙ x      ∎
        }

problem₁₂ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ ⦃ _ : HasMockingbird ⦄ → HasStarling
problem₁₂ = record
  { S = W** ∙ G
  ; isStarling = λ x y z → begin
      W** ∙ G ∙ x ∙ y ∙ z  ≈⟨ isWarblerTwiceRemoved G x y z ⟩
      G ∙ x ∙ y ∙ z ∙ z    ≈⟨ isGoldfinch x y z z ⟩
      x ∙ z ∙ (y ∙ z)      ∎
  } where
  instance
    hasWarblerTwiceRemoved = problem₉-W**
    hasGoldfinch = Chapter₁₁.problem₄₇

problem₁₃ : ⦃ _ : HasStarling ⦄ ⦃ _ : HasRobin ⦄ → HasHummingbird
problem₁₃ = record
  { H = S ∙ R
  ; isHummingbird = λ x y z → begin
      S ∙ R ∙ x ∙ y ∙ z    ≈⟨ congʳ $ isStarling R x y ⟩
      R ∙ y ∙ (x ∙ y) ∙ z  ≈⟨ isRobin y (x ∙ y) z ⟩
      x ∙ y ∙ z ∙ y        ∎
  }

problem₁₄-SR : ⦃ _ : HasStarling ⦄ ⦃ _ : HasRobin ⦄ → HasWarbler
problem₁₄-SR = record
  { W = R ∙ (S ∙ R ∙ R) ∙ R
  ; isWarbler = λ x y → begin
      R ∙ (S ∙ R ∙ R) ∙ R ∙ x ∙ y      ≈˘⟨ congʳ $ congʳ $ isRobin R R (S ∙ R ∙ R) ⟩
      R ∙ R ∙ R ∙ (S ∙ R ∙ R) ∙ x ∙ y  ≈⟨⟩
      C ∙ (S ∙ R ∙ R) ∙ x ∙ y          ≈⟨⟩
      C ∙ (H ∙ R) ∙ x ∙ y              ≈⟨⟩
      W ∙ x ∙ y                        ≈⟨ isWarbler x y ⟩
      x ∙ y ∙ y                        ∎
  } where
  instance
    hasCardinal = Chapter₁₁.problem₂₁
    hasHummingbird = problem₁₃
    hasWarbler = problem₁₁

problem₁₄-SC : ⦃ _ : HasStarling ⦄ ⦃ _ : HasCardinal ⦄ → HasWarbler
problem₁₄-SC = record
  { W = C ∙ (S ∙ (C ∙ C) ∙ (C ∙ C))
  ; isWarbler = λ x y → begin
      C ∙ (S ∙ (C ∙ C) ∙ (C ∙ C)) ∙ x ∙ y  ≈⟨⟩
      C ∙ (S ∙ R ∙ R) ∙ x ∙ y              ≈⟨ isCardinal (S ∙ R ∙ R) x y ⟩
      S ∙ R ∙ R ∙ y ∙ x                    ≈⟨ congʳ $ isStarling R R y ⟩
      R ∙ y ∙ (R ∙ y) ∙ x                  ≈⟨ isRobin y (R ∙ y) x ⟩
      R ∙ y ∙ x ∙ y                        ≈⟨ isRobin y x y ⟩
      x ∙ y ∙ y                            ∎
  } where instance hasRobin = Chapter₁₁.problem₂₃

problem₁₅ : ⦃ _ : HasThrush ⦄ ⦃ _ : HasStarling ⦄ → HasWarbler
problem₁₅ = record
  { W = S ∙ T
  ; isWarbler = λ x y → begin
      S ∙ T ∙ x ∙ y    ≈⟨ isStarling T x y ⟩
      T ∙ y ∙ (x ∙ y)  ≈⟨ isThrush y (x ∙ y) ⟩
      x ∙ y ∙ y        ∎
  }

problem₁₆ : ⦃ _ : HasThrush ⦄ ⦃ _ : HasStarling ⦄ → HasMockingbird
problem₁₆ = record
  { M = S ∙ T ∙ T
  ; isMockingbird = λ x → begin
      S ∙ T ∙ T ∙ x    ≈⟨ isStarling T T x ⟩
      T ∙ x ∙ (T ∙ x)  ≈⟨ isThrush x (T ∙ x) ⟩
      T ∙ x ∙ x        ≈⟨ isThrush x x ⟩
      x ∙ x            ∎
  }

module Exercises where
  exercise₁-a : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄
    → ∃[ G₁ ] (∀ x y z w v → G₁ ∙ x ∙ y ∙ z ∙ w ∙ v ≈ x ∙ y ∙ v ∙ (z ∙ w))
  exercise₁-a =
    ( D₁ ∙ C*
    , λ x y z w v → begin
        D₁ ∙ C* ∙ x ∙ y ∙ z ∙ w ∙ v  ≈⟨ congʳ $ isDickcissel C* x y z w ⟩
        C* ∙ x ∙ y ∙ (z ∙ w) ∙ v     ≈⟨ isCardinalOnceRemoved x y (z ∙ w) v ⟩
        x ∙ y ∙ v ∙ (z ∙ w)          ∎
    )
    where
      instance
        hasCardinal = Chapter₁₁.problem₂₁′
        hasCardinalOnceRemoved = Chapter₁₁.problem₃₁
        hasDickcissel = Chapter₁₁.problem₉

  -- Note: in the solutions, the bluebird is used, but the exercise does not
  -- state that the bluebird may be used.
  exercise₁-b : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasMockingbird ⦄
    → ∃[ G₁ ] (∀ x y z w v → G₁ ∙ x ∙ y ∙ z ∙ w ∙ v ≈ x ∙ y ∙ v ∙ (z ∙ w))
    → ∃[ G₂ ] (∀ x y z w → G₂ ∙ x ∙ y ∙ z ∙ w ≈ x ∙ w ∙ (x ∙ w) ∙ (y ∙ z))
  exercise₁-b (G₁ , isG₁) =
    ( G₁ ∙ (B ∙ M)
    , λ x y z w → begin
        G₁ ∙ (B ∙ M) ∙ x ∙ y ∙ z ∙ w  ≈⟨ isG₁ (B ∙ M) x y z w ⟩
        B ∙ M ∙ x ∙ w ∙ (y ∙ z)       ≈⟨ congʳ $ isBluebird M x w ⟩
        M ∙ (x ∙ w) ∙ (y ∙ z)         ≈⟨ congʳ $ isMockingbird (x ∙ w) ⟩
        x ∙ w ∙ (x ∙ w) ∙ (y ∙ z)     ∎
    )

  exercise₁-c : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ ⦃ _ : HasIdentity ⦄
    → ∃[ I₂ ] (∀ x → I₂ ∙ x ≈ x ∙ I ∙ I)
  exercise₁-c =
    ( B ∙ (T ∙ I) ∙ (T ∙ I)
    , λ x → begin
        B ∙ (T ∙ I) ∙ (T ∙ I) ∙ x  ≈⟨ isBluebird (T ∙ I) (T ∙ I) x ⟩
        T ∙ I ∙ (T ∙ I ∙ x)        ≈⟨ isThrush I (T ∙ I ∙ x) ⟩
        T ∙ I ∙ x ∙ I              ≈⟨ congʳ $ isThrush I x ⟩
        x ∙ I ∙ I                  ∎
    )

  exercise₁-d : ⦃ _ : HasIdentity ⦄ ⦃ _ : HasFinch ⦄
    → (hasI₂ : ∃[ I₂ ] (∀ x → I₂ ∙ x ≈ x ∙ I ∙ I))
    → ∀ x → proj₁ hasI₂ ∙ (F ∙ x) ≈ x
  exercise₁-d (I₂ , isI₂) x = begin
    I₂ ∙ (F ∙ x)   ≈⟨ isI₂ (F ∙ x) ⟩
    F ∙ x ∙ I ∙ I  ≈⟨ isFinch x I I ⟩
    I ∙ I ∙ x      ≈⟨ congʳ $ isIdentity I ⟩
    I ∙ x          ≈⟨ isIdentity x ⟩
    x              ∎

  exercise₁-e : ⦃ _ : HasFinch ⦄ ⦃ _ : HasQueerBird ⦄ ⦃ _ : HasIdentity ⦄
    → (hasG₂ : ∃[ G₂ ] (∀ x y z w → G₂ ∙ x ∙ y ∙ z ∙ w ≈ x ∙ w ∙ (x ∙ w) ∙ (y ∙ z)))
    → (hasI₂ : ∃[ I₂ ] (∀ x → I₂ ∙ x ≈ x ∙ I ∙ I))
    → IsWarbler (proj₁ hasG₂ ∙ F ∙ (Q ∙ proj₁ hasI₂))
  exercise₁-e (G₂ , isG₂) (I₂ , isI₂) x y = begin
    G₂ ∙ F ∙ (Q ∙ I₂) ∙ x ∙ y       ≈⟨ isG₂ F (Q ∙ I₂) x y ⟩
    F ∙ y ∙ (F ∙ y) ∙ (Q ∙ I₂ ∙ x)  ≈⟨ isFinch y (F ∙ y) (Q ∙ I₂ ∙ x) ⟩
    Q ∙ I₂ ∙ x ∙ (F ∙ y) ∙ y        ≈⟨ congʳ $ isQueerBird I₂ x (F ∙ y) ⟩
    x ∙ (I₂ ∙ (F ∙ y)) ∙ y          ≈⟨ congʳ $ congˡ $ exercise₁-d (I₂ , isI₂) y ⟩
    x ∙ y ∙ y                       ∎

  exercise₂ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasCardinal ⦄ ⦃ _ : HasWarbler ⦄
    → IsStarling (B ∙ (B ∙ (B ∙ W) ∙ C) ∙ (B ∙ B))
  exercise₂ x y z = begin
    B ∙ (B ∙ (B ∙ W) ∙ C) ∙ (B ∙ B) ∙ x ∙ y ∙ z  ≈⟨ congʳ $ congʳ $ isBluebird (B ∙ (B ∙ W) ∙ C) (B ∙ B) x ⟩
    B ∙ (B ∙ W) ∙ C ∙ (B ∙ B ∙ x) ∙ y ∙ z        ≈⟨ congʳ $ congʳ $ isBluebird (B ∙ W) C (B ∙ B ∙ x) ⟩
    B ∙ W ∙ (C ∙ (B ∙ B ∙ x)) ∙ y ∙ z            ≈⟨ congʳ $ isBluebird W (C ∙ (B ∙ B ∙ x)) y ⟩
    W ∙ (C ∙ (B ∙ B ∙ x) ∙ y) ∙ z                ≈⟨ isWarbler (C ∙ (B ∙ B ∙ x) ∙ y) z ⟩
    C ∙ (B ∙ B ∙ x) ∙ y ∙ z ∙ z                  ≈⟨ congʳ $ isCardinal (B ∙ B ∙ x) y z ⟩
    B ∙ B ∙ x ∙ z ∙ y ∙ z                        ≈⟨ congʳ $ congʳ $ isBluebird B x z ⟩
    B ∙ (x ∙ z) ∙ y ∙ z                          ≈⟨ isBluebird (x ∙ z) y z ⟩
    x ∙ z ∙ (y ∙ z)                              ∎

  exercise₃ : ⦃ _ : HasStarling ⦄ ⦃ _ : HasBluebird ⦄ → HasPhoenix
  exercise₃ = record
    { Φ = B ∙ (B ∙ S) ∙ B
    ; isPhoenix = λ x y z w → begin
        B ∙ (B ∙ S) ∙ B ∙ x ∙ y ∙ z ∙ w  ≈⟨ congʳ $ congʳ $ congʳ $ isBluebird (B ∙ S) B x ⟩
        B ∙ S ∙ (B ∙ x) ∙ y ∙ z ∙ w      ≈⟨ congʳ $ congʳ $ isBluebird S (B ∙ x) y ⟩
        S ∙ (B ∙ x ∙ y) ∙ z ∙ w          ≈⟨ isStarling (B ∙ x ∙ y) z w ⟩
        B ∙ x ∙ y ∙ w ∙ (z ∙ w)          ≈⟨ congʳ $ isBluebird x y w ⟩
        x ∙ (y ∙ w) ∙ (z ∙ w)            ∎
    }

  exercise₄ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasCardinal ⦄ ⦃ _ : HasWarbler ⦄ → HasPsiBird
  exercise₄ = record
    { Ψ = H* ∙ D₂
    ; isPsiBird = λ x y z w → begin
        H* ∙ D₂ ∙ x ∙ y ∙ z ∙ w     ≈⟨⟩
        B ∙ H ∙ D₂ ∙ x ∙ y ∙ z ∙ w  ≈⟨ congʳ $ congʳ $ congʳ $ isBluebird H D₂ x ⟩
        H ∙ (D₂ ∙ x) ∙ y ∙ z ∙ w    ≈⟨ congʳ $ isHummingbird (D₂ ∙ x) y z ⟩
        D₂ ∙ x ∙ y ∙ z ∙ y ∙ w      ≈⟨ isDovekie x y z y w ⟩
        x ∙ (y ∙ z) ∙ (y ∙ w)       ∎
    } where
    instance
      hasHummingbird = problem₁₀
      hasDovekie = Chapter₁₁.problem₁₁
    H* = B ∙ H

  -- NOTE: my copy of the book contains a mistake (looking at the given
  -- solutions): it says Γxyzwv = y(zw)(xywv) instead of Γxyzwv = y(zw)(xyzwv).
  exercise₅-a : ⦃ _ : HasPhoenix ⦄ ⦃ _ : HasBluebird ⦄
    → ∃[ Γ ] (∀ x y z w v → Γ ∙ x ∙ y ∙ z ∙ w ∙ v ≈ y ∙ (z ∙ w) ∙ (x ∙ y ∙ z ∙ w ∙ v))
  exercise₅-a =
    ( Φ ∙ (Φ ∙ (Φ ∙ B)) ∙ B
    , λ x y z w v → begin
        Φ ∙ (Φ ∙ (Φ ∙ B)) ∙ B ∙ x ∙ y ∙ z ∙ w ∙ v    ≈⟨ congʳ $ congʳ $ congʳ $ isPhoenix (Φ ∙ (Φ ∙ B)) B x y ⟩
        Φ ∙ (Φ ∙ B) ∙ (B ∙ y) ∙ (x ∙ y) ∙ z ∙ w ∙ v  ≈⟨ congʳ $ congʳ $ isPhoenix (Φ ∙ B) (B ∙ y) (x ∙ y) z ⟩
        Φ ∙ B ∙ (B ∙ y ∙ z) ∙ (x ∙ y ∙ z) ∙ w ∙ v    ≈⟨ congʳ $ isPhoenix B (B ∙ y ∙ z) (x ∙ y ∙ z) w ⟩
        B ∙ (B ∙ y ∙ z ∙ w) ∙ (x ∙ y ∙ z ∙ w) ∙ v    ≈⟨ isBluebird (B ∙ y ∙ z ∙ w) (x ∙ y ∙ z ∙ w) v ⟩
        B ∙ y ∙ z ∙ w ∙ (x ∙ y ∙ z ∙ w ∙ v)          ≈⟨ congʳ $ isBluebird y z w ⟩
        y ∙ (z ∙ w) ∙ (x ∙ y ∙ z ∙ w ∙ v)            ∎
    )

  exercise₅-b : ⦃ _ : HasKestrel ⦄
    → ∃[ Γ ] (∀ x y z w v → Γ ∙ x ∙ y ∙ z ∙ w ∙ v ≈ y ∙ (z ∙ w) ∙ (x ∙ y ∙ z ∙ w ∙ v))
    → HasPsiBird
  exercise₅-b (Γ , isΓ) = record
    { Ψ = Γ ∙ (K ∙ K)
    ; isPsiBird = λ x y z w → begin
        Γ ∙ (K ∙ K) ∙ x ∙ y ∙ z ∙ w            ≈⟨ isΓ (K ∙ K) x y z w ⟩
        x ∙ (y ∙ z) ∙ (K ∙ K ∙ x ∙ y ∙ z ∙ w)  ≈⟨ congˡ $ congʳ $ congʳ $ congʳ $ isKestrel K x ⟩
        x ∙ (y ∙ z) ∙ (K ∙ y ∙ z ∙ w)          ≈⟨ congˡ $ congʳ $ isKestrel y z ⟩
        x ∙ (y ∙ z) ∙ (y ∙ w)                  ∎
    }

  exercise₅ : ⦃ _ : HasPhoenix ⦄ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasKestrel ⦄ → HasPsiBird
  exercise₅ = exercise₅-b exercise₅-a

  exercise₆-a : ⦃ _ : HasStarling ⦄ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄
    → ∃[ S′ ] (∀ x y z → S′ ∙ x ∙ y ∙ z ≈ y ∙ z ∙ (x ∙ z))
  exercise₆-a =
    ( C ∙ S
    , λ x y z → begin
        C ∙ S ∙ x ∙ y ∙ z  ≈⟨ congʳ $ isCardinal S x y ⟩
        S ∙ y ∙ x ∙ z      ≈⟨ isStarling y x z ⟩
        y ∙ z ∙ (x ∙ z)    ∎
    )
    where instance hasCardinal = Chapter₁₁.problem₂₁′

  exercise₆-b : ⦃ _ : HasIdentity ⦄
    → ∃[ S′ ] (∀ x y z → S′ ∙ x ∙ y ∙ z ≈ y ∙ z ∙ (x ∙ z))
    → HasWarbler
  exercise₆-b (S′ , isS′) = record
    { W = S′ ∙ I
    ; isWarbler = λ x y → begin
        S′ ∙ I ∙ x ∙ y   ≈⟨ isS′ I x y ⟩
        x ∙ y ∙ (I ∙ y)  ≈⟨ congˡ $ isIdentity y ⟩
        x ∙ y ∙ y        ∎
    }

  exercise₇ : ⦃ _ : HasQueerBird ⦄ ⦃ _ : HasCardinal ⦄ ⦃ _ : HasWarbler ⦄
    → ∃[ Q̂ ] IsStarling (C ∙ Q̂ ∙ W)
  exercise₇ = let Q̂ = Q ∙ (Q ∙ Q ∙ (Q ∙ Q)) ∙ Q in
    ( Q̂
    , λ x y z → begin
        C ∙ Q̂ ∙ W ∙ x ∙ y ∙ z ≈⟨ congʳ $ congʳ $ isCardinal Q̂ W x ⟩
        Q̂ ∙ x ∙ W ∙ y ∙ z                          ≈⟨⟩
        Q ∙ (Q ∙ Q ∙ (Q ∙ Q)) ∙ Q ∙ x ∙ W ∙ y ∙ z  ≈⟨ congʳ $ congʳ $ congʳ $ isQueerBird (Q ∙ Q ∙ (Q ∙ Q)) Q  x ⟩
        Q ∙ (Q ∙ Q ∙ (Q ∙ Q) ∙ x) ∙ W ∙ y ∙ z      ≈⟨ congʳ $ isQueerBird (Q ∙ Q ∙ (Q ∙ Q) ∙ x) W y ⟩
        W ∙ (Q ∙ Q ∙ (Q ∙ Q) ∙ x ∙ y) ∙ z          ≈⟨ isWarbler (Q ∙ Q ∙ (Q ∙ Q) ∙ x ∙ y) z ⟩
        Q ∙ Q ∙ (Q ∙ Q) ∙ x ∙ y ∙ z ∙ z            ≈⟨ congʳ $ congʳ $ congʳ $ isQueerBird Q (Q ∙ Q) x ⟩
        Q ∙ Q ∙ (Q ∙ x) ∙ y ∙ z ∙ z                ≈⟨ congʳ $ congʳ $ isQueerBird Q (Q ∙ x) y ⟩
        Q ∙ x ∙ (Q ∙ y) ∙ z ∙ z                    ≈⟨ congʳ $ isQueerBird x (Q ∙ y) z ⟩
        Q ∙ y ∙ (x ∙ z) ∙ z                        ≈⟨ isQueerBird y (x ∙ z) z ⟩
        x ∙ z ∙ (y ∙ z)                            ∎
    )
