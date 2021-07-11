open import Mockingbird.Forest using (Forest)

-- Birds Galore
module Mockingbird.Problems.Chapter11 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)

import Mockingbird.Problems.Chapter09 forest as Chapter₉

open Forest forest

module Parentheses where
  private
    variable
      u v w x y z A A₁ A₂ B : Bird

  -- A variant of _∙_ that is not parsed as a right-associative operator, to
  -- make sure that the parentheses in the right-hand side of the exercises
  -- below are fully restored.
  infix 6 _∙′_
  _∙′_ = _∙_

  exercise-a : x ∙ y ∙ (z ∙ w ∙ y) ∙ v ≈ ((x ∙′ y) ∙′ ((z ∙′ w) ∙′ y)) ∙′ v
  exercise-a = refl

  exercise-b : (x ∙ y ∙ z) ∙ (w ∙ v ∙ x) ≈ ((x ∙′ y) ∙′ z) ∙′ ((w ∙′ v) ∙′ x)
  exercise-b = refl

  exercise-c : x ∙ y ∙ (z ∙ w ∙ v) ∙ (x ∙ z) ≈ ((x ∙′ y) ∙′ ((z ∙′ w) ∙′ v)) ∙′ (x ∙′ z)
  exercise-c = refl

  exercise-d : x ∙ y ∙ (z ∙ w ∙ v) ∙ x ∙ z ≈ (((x ∙′ y) ∙′ ((z ∙′ w) ∙′ v)) ∙′ x) ∙′ z
  exercise-d = refl

  exercise-e : x ∙ (y ∙ (z ∙ w ∙ v)) ∙ x ∙ z ≈ ((x ∙′ (y ∙′ ((z ∙′ w) ∙′ v))) ∙′ x) ∙′ z
  exercise-e = refl

  exercise-f : x ∙ y ∙ z ∙ (A ∙ B) ≈ (x ∙ y ∙ z) ∙ (A ∙ B)
  exercise-f = refl

  exercise-g : A₁ ≈ A₂ → B ∙ A₁ ≈ B ∙ A₂ × A₁ ∙ B ≈ A₂ ∙ B
  exercise-g A₁≈A₂ = (∙-congˡ A₁≈A₂ , ∙-congʳ A₁≈A₂)

  exercise-h : x ∙ y ≈ z → x ∙ y ∙ w ≈ z ∙ w
  exercise-h {x} {y} {z} {w} xy≈z = begin
    x ∙ y ∙ w      ≈⟨⟩
    (x ∙′ y) ∙′ w  ≈⟨ ∙-congʳ xy≈z ⟩
    z ∙ w          ∎

  -- The other part of exercise h, wxy ≈ wz, does not follow in general.

open import Mockingbird.Forest.Birds forest

problem₁ : ⦃ _ : HasBluebird ⦄ → HasComposition
problem₁ = record
  { _∘_ = λ C D → B ∙ C ∙ D
  ; isComposition = λ C D x → begin
      B ∙ C ∙ D ∙ x  ≈⟨ isBluebird C D x ⟩
      C ∙ (D ∙ x)    ∎
  }

private
  instance
    hasComposition : ⦃ HasBluebird ⦄ → HasComposition
    hasComposition = problem₁

module _ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasMockingbird ⦄ where
  problem₂ : ∀ x → ∃[ y ] x IsFondOf y
  problem₂ x =
    let (_ , isFond) = Chapter₉.problem₁ x

        shorten : M ∙ (B ∙ x ∙ M) ≈ B ∙ x ∙ M ∙ (B ∙ x ∙ M)
        shorten = isMockingbird (B ∙ x ∙ M)

    in (M ∙ (B ∙ x ∙ M) , trans (∙-congˡ shorten) (trans isFond (sym shorten)))

  problem₃ : ∃[ x ] IsEgocentric x
  problem₃ =
    let (_ , isEgocentric) = Chapter₉.problem₂
    in (B ∙ M ∙ M ∙ (B ∙ M ∙ M) , isEgocentric)

module _ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasKestrel ⦄ where
  problem₄ : ∃[ x ] IsHopelesslyEgocentric x
  problem₄ =
    let (_ , isHopelesslyEgocentric) = Chapter₉.problem₉
    in (B ∙ K ∙ M ∙ (B ∙ K ∙ M) , isHopelesslyEgocentric)

module _ ⦃ _ : HasBluebird ⦄ where
  problem₅ : HasDove
  problem₅ = record
    { D = B ∙ B
    ; isDove = λ x y z w → begin
        B ∙ B ∙ x ∙ y ∙ z ∙ w  ≈⟨ ∙-congʳ $ ∙-congʳ $ isBluebird B x y ⟩
        B ∙ (x ∙ y) ∙ z ∙ w    ≈⟨ isBluebird (x ∙ y) z w ⟩
        x ∙ y ∙ (z ∙ w)        ∎
    }

  private instance hasDove = problem₅

  problem₆ : HasBlackbird
  problem₆ = record
    { B₁ = B ∙ B ∙ B
    ; isBlackbird = λ x y z w → begin
        B ∙ B ∙ B ∙ x ∙ y ∙ z ∙ w  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ (isBluebird B B x) ⟩
        B ∙ (B ∙ x) ∙ y ∙ z ∙ w    ≈⟨ ∙-congʳ (isBluebird (B ∙ x) y z) ⟩
        B ∙ x ∙ (y ∙ z) ∙ w        ≈⟨ isBluebird x (y ∙ z) w ⟩
        x ∙ (y ∙ z ∙ w)            ∎
    }

  private instance hasBlackbird = problem₆

  problem₇ : HasEagle
  problem₇ = record
    { E = B ∙ B₁
    ; isEagle = λ x y z w v → begin
        B ∙ B₁ ∙ x ∙ y ∙ z ∙ w ∙ v  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird B₁ x y ⟩
        B₁ ∙ (x ∙ y) ∙ z ∙ w ∙ v    ≈⟨ isBlackbird (x ∙ y) z w v ⟩
        x ∙ y ∙ (z ∙ w ∙ v)         ∎
    }

  private instance hasEagle = problem₇

  problem₈ : HasBunting
  problem₈ = record
    { B₂ = B ∙ B ∙ B₁
    ; isBunting = λ x y z w v → begin
        B ∙ B ∙ B₁ ∙ x ∙ y ∙ z ∙ w ∙ v  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird B B₁ x ⟩
        B ∙ (B₁ ∙ x) ∙ y ∙ z ∙ w ∙ v    ≈⟨ ∙-congʳ $ ∙-congʳ $ isBluebird (B₁ ∙ x) y z ⟩
        B₁ ∙ x ∙ (y ∙ z) ∙ w ∙ v        ≈⟨ isBlackbird x (y ∙ z) w v ⟩
        x ∙ (y ∙ z ∙ w ∙ v)             ∎
    }

  private instance hasBunting = problem₈

  problem₉ : HasDickcissel
  problem₉ = record
    { D₁ = B ∙ D
    ; isDickcissel = λ x y z w v → begin
        B ∙ D ∙ x ∙ y ∙ z ∙ w ∙ v  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird D x y ⟩
        D ∙ (x ∙ y) ∙ z ∙ w ∙ v    ≈⟨ isDove (x ∙ y) z w v ⟩
        x ∙ y ∙ z ∙ (w ∙ v)        ∎
    }

  private instance hasDickcissel = problem₉

  problem₁₀ : HasBecard
  problem₁₀ = record
    { B₃ = B ∙ D ∙ B
    ; isBecard = λ x y z w → begin
        B ∙ D ∙ B ∙ x ∙ y ∙ z ∙ w  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird D B x ⟩
        D ∙ (B ∙ x) ∙ y ∙ z ∙ w    ≈⟨ isDove (B ∙ x) y z w ⟩
        B ∙ x ∙ y ∙ (z ∙ w)        ≈⟨ isBluebird x y (z ∙ w) ⟩
        x ∙ (y ∙ (z ∙ w))          ∎
    }

  private instance hasBecard = problem₁₀

  problem₁₁ : HasDovekie
  problem₁₁ = record
    { D₂ = D ∙ D
    ; isDovekie = λ x y z w v → begin
        D ∙ D ∙ x ∙ y ∙ z ∙ w ∙ v  ≈⟨ ∙-congʳ $ ∙-congʳ $ isDove D x y z ⟩
        D ∙ x ∙ (y ∙ z) ∙ w ∙ v    ≈⟨ isDove x (y ∙ z) w v ⟩
        x ∙ (y ∙ z) ∙ (w ∙ v)      ∎
    }

  private instance hasDovekie = problem₁₁

  problem₁₂ : HasBaldEagle
  problem₁₂ = record
    { Ê = E ∙ E
    ; isBaldEagle = λ x y₁ y₂ y₃ z₁ z₂ z₃ → begin
        E ∙ E ∙ x ∙ y₁ ∙ y₂ ∙ y₃ ∙ z₁ ∙ z₂ ∙ z₃  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isEagle E x y₁ y₂ y₃ ⟩
        E ∙ x ∙ (y₁ ∙ y₂ ∙ y₃) ∙ z₁ ∙ z₂ ∙ z₃    ≈⟨ isEagle x (y₁ ∙ y₂ ∙ y₃) z₁ z₂ z₃ ⟩
        x ∙ (y₁ ∙ y₂ ∙ y₃) ∙ (z₁ ∙ z₂ ∙ z₃)      ∎
    }

  private instance hasBaldEagle = problem₁₂

problem₁₄ : ⦃ _ : HasWarbler ⦄ ⦃ _ : HasIdentity ⦄ → HasMockingbird
problem₁₄ = record
  { M = W ∙ I
  ; isMockingbird = λ x → begin
      W ∙ I ∙ x  ≈⟨ isWarbler I x ⟩
      I ∙ x ∙ x  ≈⟨ ∙-congʳ $ isIdentity x ⟩
      x ∙ x      ∎
  }

problem₁₅ : ⦃ _ : HasWarbler ⦄ ⦃ _ : HasKestrel ⦄ → HasIdentity
problem₁₅ = record
  { I = W ∙ K
  ; isIdentity = λ x → begin
      W ∙ K ∙ x  ≈⟨ isWarbler K x ⟩
      K ∙ x ∙ x  ≈⟨ isKestrel x x ⟩
      x          ∎
  }

problem₁₃ : ⦃ _ : HasWarbler ⦄ ⦃ _ : HasKestrel ⦄ → HasMockingbird
problem₁₃ = problem₁₄
  where instance _ = problem₁₅

problem₁₆ : ⦃ _ : HasCardinal ⦄ ⦃ _ : HasKestrel ⦄ → HasIdentity
problem₁₆ = record
  { I = C ∙ K ∙ K
  ; isIdentity = λ x → begin
      C ∙ K ∙ K ∙ x  ≈⟨ isCardinal K K x ⟩
      K ∙ x ∙ K      ≈⟨ isKestrel x K ⟩
      x              ∎
  }

problem₁₇ : ⦃ _ : HasCardinal ⦄ ⦃ _ : HasIdentity ⦄ → HasThrush
problem₁₇ = record
  { T = C ∙ I
  ; isThrush = λ x y → begin
      C ∙ I ∙ x ∙ y  ≈⟨ isCardinal I x y ⟩
      I ∙ y ∙ x      ≈⟨ ∙-congʳ $ isIdentity y ⟩
      y ∙ x          ∎
  }

problem₁₈ : ⦃ _ : HasThrush ⦄ → (∀ x → IsNormal x) → ∃[ A ] (∀ x → Commute A x)
problem₁₈ isNormal =
  let (A , isFond) = isNormal T

      commute : ∀ x → Commute A x
      commute x = begin
        A ∙ x      ≈˘⟨ (∙-congʳ $ isFond) ⟩
        T ∙ A ∙ x  ≈⟨ isThrush A x ⟩
        x ∙ A      ∎

  in (A , commute)

problem₁₉ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ ⦃ _ : HasMockingbird ⦄ → ∃[ x ] (∀ y → Commute x y)
problem₁₉ = problem₁₈ problem₂

problem₂₀ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ → HasRobin
problem₂₀ = record
  { R = B ∙ B ∙ T
  ; isRobin = λ x y z → begin
      B ∙ B ∙ T ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ ∙-congʳ $ isBluebird B T x ⟩
      B ∙ (T ∙ x) ∙ y ∙ z    ≈⟨ isBluebird (T ∙ x) y z ⟩
      T ∙ x ∙ (y ∙ z)        ≈⟨ isThrush x (y ∙ z) ⟩
      (y ∙ z) ∙ x            ≈⟨⟩
      y ∙ z ∙ x              ∎
  }

problem₂₁ : ⦃ _ : HasRobin ⦄ → HasCardinal
problem₂₁ = record
  { C = R ∙ R ∙ R
  ; isCardinal = λ x y z → begin
      R ∙ R ∙ R ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ ∙-congʳ $ isRobin R R x ⟩
      R ∙ x ∙ R ∙ y ∙ z      ≈⟨ ∙-congʳ $ isRobin x R y ⟩
      R ∙ y ∙ x ∙ z          ≈⟨ isRobin y x z ⟩
      x ∙ z ∙ y              ∎
  }

problem₂₁′ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ → HasCardinal
problem₂₁′ = problem₂₁ ⦃ problem₂₀ ⦄

problem₂₁-bonus : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ → HasCardinal
problem₂₁-bonus = record
  { C = B ∙ (T ∙ (B ∙ B ∙ T)) ∙ (B ∙ B ∙ T)
  ; isCardinal = λ x y z → begin
      B ∙ (T ∙ (B ∙ B ∙ T)) ∙ (B ∙ B ∙ T) ∙ x ∙ y ∙ z    ≈˘⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird B T (B ∙ B ∙ T) ⟩
      B ∙ B ∙ T ∙ (B ∙ B ∙ T) ∙ (B ∙ B ∙ T) ∙ x ∙ y ∙ z  ≈⟨ isCardinal x y z ⟩
      x ∙ z ∙ y                                          ∎
  } where instance hasCardinal = problem₂₁′

module _ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ where
  private
    instance hasRobin = problem₂₀
    instance hasCardinal = problem₂₁′

  problem₂₂-a : ∀ x → C ∙ x ≈ R ∙ x ∙ R
  problem₂₂-a x = begin
    C ∙ x          ≈⟨⟩
    R ∙ R ∙ R ∙ x  ≈⟨ isRobin R R x ⟩
    R ∙ x ∙ R      ∎

  problem₂₂-b : ∀ x → C ∙ x ≈ B ∙ (T ∙ x) ∙ R
  problem₂₂-b x = begin
    C ∙ x ≈⟨ problem₂₂-a x ⟩
    R ∙ x ∙ R          ≈⟨⟩
    B ∙ B ∙ T ∙ x ∙ R  ≈⟨ ∙-congʳ $ isBluebird B T x ⟩
    B ∙ (T ∙ x) ∙ R    ∎

problem₂₃ : ⦃ _ : HasCardinal ⦄ → HasRobin
problem₂₃ = record
  { R = C ∙ C
  ; isRobin = λ x y z → begin
      C ∙ C ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ isCardinal C x y ⟩
      C ∙ y ∙ x ∙ z      ≈⟨ isCardinal y x z ⟩
      y ∙ z ∙ x          ∎
  }

problem₂₄ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasRobin ⦄ ⦃ _ : HasCardinal ⦄ → HasFinch
problem₂₄ = record
  { F = B ∙ C ∙ R
  ; isFinch = λ x y z → begin
      B ∙ C ∙ R ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ ∙-congʳ $ isBluebird C R x ⟩
      C ∙ (R ∙ x) ∙ y ∙ z    ≈⟨ isCardinal (R ∙ x) y z ⟩
      R ∙ x ∙ z ∙ y          ≈⟨ isRobin x z y ⟩
      z ∙ y ∙ x              ∎
  }

problem₂₅ : ⦃ _ : HasThrush ⦄ ⦃ _ : HasEagle ⦄ → HasFinch
problem₂₅ = record
  { F = E ∙ T ∙ T ∙ E ∙ T
  ; isFinch = λ x y z → begin
      E ∙ T ∙ T ∙ E ∙ T ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ ∙-congʳ $ isEagle T T E T x ⟩
      T ∙ T ∙ (E ∙ T ∙ x) ∙ y ∙ z    ≈⟨ ∙-congʳ $ ∙-congʳ $ isThrush T (E ∙ T ∙ x) ⟩
      E ∙ T ∙ x ∙ T ∙ y ∙ z          ≈⟨ isEagle T x T y z ⟩
      T ∙ x ∙ (T ∙ y ∙ z)            ≈⟨ isThrush x (T ∙ y ∙ z) ⟩
      T ∙ y ∙ z ∙ x                  ≈⟨ ∙-congʳ $ isThrush y z ⟩
      z ∙ y ∙ x                      ∎
  }

problem₂₆ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ → HasFinch
problem₂₆ = record
  { F = short
  ; isFinch = shortIsFinch
  }
  where
    instance
      hasRobin = problem₂₀
      hasCardinal = problem₂₁-bonus
      hasEagle = problem₇

    long : Bird
    long = (B ∙ (B ∙ (T ∙ (B ∙ B ∙ T)) ∙ (B ∙ B ∙ T)) ∙ (B ∙ B ∙ T))

    longIsFinch : IsFinch long
    longIsFinch = HasFinch.isFinch problem₂₄

    short : Bird
    short = B ∙ (T ∙ T) ∙ (B ∙ (B ∙ B ∙ B) ∙ T)

    short≈ETTET : short ≈ E ∙ T ∙ T ∙ E ∙ T
    short≈ETTET = begin
      short                                            ≈⟨⟩
      B ∙ (T ∙ T) ∙ (B ∙ (B ∙ B ∙ B) ∙ T)              ≈˘⟨ isBluebird (B ∙ (T ∙ T)) (B ∙ (B ∙ B ∙ B)) T ⟩
      B ∙ (B ∙ (T ∙ T)) ∙ (B ∙ (B ∙ B ∙ B)) ∙ T        ≈˘⟨ ∙-congʳ $ ∙-congʳ $ isBluebird B B (T ∙ T) ⟩
      B ∙ B ∙ B ∙ (T ∙ T) ∙ (B ∙ (B ∙ B ∙ B)) ∙ T      ≈˘⟨ ∙-congʳ $ ∙-congʳ $ isBluebird (B ∙ B ∙ B) T T ⟩
      B ∙ (B ∙ B ∙ B) ∙ T ∙ T ∙ (B ∙ (B ∙ B ∙ B)) ∙ T  ≈⟨⟩
      E ∙ T ∙ T ∙ E ∙ T                                ∎

    shortIsFinch : IsFinch short
    shortIsFinch x y z = begin
      short ∙ x ∙ y ∙ z              ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ short≈ETTET ⟩
      E ∙ T ∙ T ∙ E ∙ T ∙ x ∙ y ∙ z  ≈⟨ HasFinch.isFinch problem₂₅ x y z ⟩
      z ∙ y ∙ x                      ∎

problem₂₇ : ⦃ _ : HasCardinal ⦄ ⦃ _ : HasFinch ⦄ → HasVireo
problem₂₇ = record
  { V = C ∙ F
  ; isVireo = λ x y z → begin
      C ∙ F ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ isCardinal F x y ⟩
      F ∙ y ∙ x ∙ z      ≈⟨ isFinch y x z ⟩
      z ∙ x ∙ y          ∎
  }

problem₂₈ : ⦃ _ : HasFinch ⦄ ⦃ _ : HasRobin ⦄ → HasVireo
problem₂₈ = record
  { V = R ∙ F ∙ R
  ; isVireo = λ x y z → begin
      R ∙ F ∙ R ∙ x ∙ y ∙ z      ≈˘⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isRobin R R F ⟩
      R ∙ R ∙ R ∙ F ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ HasCardinal.isCardinal problem₂₁ F x y ⟩
      F ∙ y ∙ x ∙ z              ≈⟨ isFinch y x z ⟩
      z ∙ x ∙ y                  ∎
  }

problem₂₉ : ⦃ _ : HasCardinal ⦄ ⦃ _ : HasVireo ⦄ → HasFinch
problem₂₉ = record
  { F = C ∙ V
  ; isFinch = λ x y z → begin
      C ∙ V ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ isCardinal V x y ⟩
      V ∙ y ∙ x ∙ z      ≈⟨ isVireo y x z ⟩
      z ∙ y ∙ x          ∎
  }

problem₃₀ : ⦃ _ : HasRobin ⦄ ⦃ _ : HasKestrel ⦄ → HasIdentity
problem₃₀ = problem₁₆
  where instance hasCardinal = problem₂₁

module _ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasCardinal ⦄ where
  problem₃₁ : HasCardinalOnceRemoved
  problem₃₁ = record
    { C* = B ∙ C
    ; isCardinalOnceRemoved = λ x y z w → begin
        B ∙ C ∙ x ∙ y ∙ z ∙ w  ≈⟨ ∙-congʳ $ ∙-congʳ $ isBluebird C x y ⟩
        C ∙ (x ∙ y) ∙ z ∙ w    ≈⟨ isCardinal (x ∙ y) z w ⟩
        x ∙ y ∙ w ∙ z          ∎
    }

  private instance hasCardinalOnceRemoved = problem₃₁

  problem₃₂ : HasRobinOnceRemoved
  problem₃₂ = record
    { R* = C* ∙ C*
    ; isRobinOnceRemoved = λ x y z w → begin
        C* ∙ C* ∙ x ∙ y ∙ z ∙ w  ≈⟨ ∙-congʳ $ isCardinalOnceRemoved C* x y z ⟩
        C* ∙ x ∙ z ∙ y ∙ w       ≈⟨ isCardinalOnceRemoved x z y w ⟩
        x ∙ z ∙ w ∙ y            ∎
    }

  private instance hasRobinOnceRemoved = problem₃₂

  problem₃₃ : HasFinchOnceRemoved
  problem₃₃ = record
    { F* = B ∙ C* ∙ R*
    ; isFinchOnceRemoved = λ x y z w → begin
        B ∙ C* ∙ R* ∙ x ∙ y ∙ z ∙ w  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird C* R* x ⟩
        C* ∙ (R* ∙ x) ∙ y ∙ z ∙ w    ≈⟨ isCardinalOnceRemoved (R* ∙ x) y z w ⟩
        R* ∙ x ∙ y ∙ w ∙ z           ≈⟨ isRobinOnceRemoved x y w z ⟩
        x ∙ w ∙ z ∙ y                ∎
    }

  private instance hasFinchOnceRemoved = problem₃₃

  problem₃₄ : HasVireoOnceRemoved
  problem₃₄ = record
    { V* = C* ∙ F*
    ; isVireoOnceRemoved = λ x y z w → begin
        C* ∙ F* ∙ x ∙ y ∙ z ∙ w  ≈⟨ ∙-congʳ $ isCardinalOnceRemoved F* x y z ⟩
        F* ∙ x ∙ z ∙ y ∙ w       ≈⟨ isFinchOnceRemoved x z y w ⟩
        x ∙ w ∙ y ∙ z            ∎
    }

  private instance hasVireoOnceRemoved = problem₃₄

  problem₃₅-C** : HasCardinalTwiceRemoved
  problem₃₅-C** = record
    { C** = B ∙ C*
    ; isCardinalTwiceRemoved = λ x y z₁ z₂ z₃ → begin
        B ∙ C* ∙ x ∙ y ∙ z₁ ∙ z₂ ∙ z₃  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird C* x y ⟩
        C* ∙ (x ∙ y) ∙ z₁ ∙ z₂ ∙ z₃    ≈⟨ isCardinalOnceRemoved (x ∙ y) z₁ z₂ z₃ ⟩
        x ∙ y ∙ z₁ ∙ z₃ ∙ z₂           ∎
    }

  problem₃₅-R** : HasRobinTwiceRemoved
  problem₃₅-R** = record
    { R** = B ∙ R*
    ; isRobinTwiceRemoved = λ x y z₁ z₂ z₃ → begin
        B ∙ R* ∙ x ∙ y ∙ z₁ ∙ z₂ ∙ z₃  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird R* x y ⟩
        R* ∙ (x ∙ y) ∙ z₁ ∙ z₂ ∙ z₃    ≈⟨ isRobinOnceRemoved (x ∙ y) z₁ z₂ z₃ ⟩
        x ∙ y ∙ z₂ ∙ z₃ ∙ z₁           ∎
    }

  problem₃₅-F** : HasFinchTwiceRemoved
  problem₃₅-F** = record
    { F** = B ∙ F*
    ; isFinchTwiceRemoved = λ x y z₁ z₂ z₃ → begin
        B ∙ F* ∙ x ∙ y ∙ z₁ ∙ z₂ ∙ z₃  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird F* x y ⟩
        F* ∙ (x ∙ y) ∙ z₁ ∙ z₂ ∙ z₃    ≈⟨ isFinchOnceRemoved (x ∙ y) z₁ z₂ z₃ ⟩
        x ∙ y ∙ z₃ ∙ z₂ ∙ z₁           ∎
    }

  problem₃₅-V** : HasVireoTwiceRemoved
  problem₃₅-V** = record
    { V** = B ∙ V*
    ; isVireoTwiceRemoved = λ x y z₁ z₂ z₃ → begin
        B ∙ V* ∙ x ∙ y ∙ z₁ ∙ z₂ ∙ z₃  ≈⟨ ∙-congʳ $ ∙-congʳ $ ∙-congʳ $ isBluebird V* x y ⟩
        V* ∙ (x ∙ y) ∙ z₁ ∙ z₂ ∙ z₃    ≈⟨ isVireoOnceRemoved (x ∙ y) z₁ z₂ z₃ ⟩
        x ∙ y ∙ z₃ ∙ z₁ ∙ z₂           ∎
    }

problem₃₆ : ⦃ _ : HasCardinalOnceRemoved ⦄ ⦃ _ : HasThrush ⦄ → HasVireo
problem₃₆ = record
  { V = C* ∙ T
  ; isVireo = λ x y z → begin
      C* ∙ T ∙ x ∙ y ∙ z  ≈⟨ isCardinalOnceRemoved T x y z ⟩
      T ∙ x ∙ z ∙ y       ≈⟨ ∙-congʳ $ isThrush x z ⟩
      z ∙ x ∙ y           ∎
  }

problem₃₇′ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasCardinal ⦄ → HasQueerBird
problem₃₇′ = record
  { Q = C ∙ B
  ; isQueerBird = λ x y z → begin
      C ∙ B ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ isCardinal B x y ⟩
      B ∙ y ∙ x ∙ z      ≈⟨ isBluebird y x z ⟩
      y ∙ (x ∙ z)        ∎
  }

problem₃₈′ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasCardinalOnceRemoved ⦄ → HasQuixoticBird
problem₃₈′ = record
  { Q₁ = C* ∙ B
  ; isQuixoticBird = λ x y z → begin
      C* ∙ B ∙ x ∙ y ∙ z  ≈⟨ isCardinalOnceRemoved B x y z ⟩
      B ∙ x ∙ z ∙ y       ≈⟨ isBluebird x z y ⟩
      x ∙ (z ∙ y)         ∎
  }

problem₃₉′-F* : ⦃ _ : HasFinchOnceRemoved ⦄ ⦃ _ : HasQueerBird ⦄ → HasQuizzicalBird
problem₃₉′-F* = record
  { Q₂ = F* ∙ Q
  ; isQuizzicalBird = λ x y z → begin
      F* ∙ Q ∙ x ∙ y ∙ z  ≈⟨ isFinchOnceRemoved Q x y z ⟩
      Q ∙ z ∙ y ∙ x       ≈⟨ isQueerBird z y x ⟩
      y ∙ (z ∙ x)         ∎
  }

problem₃₉′-R* : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasRobinOnceRemoved ⦄ → HasQuizzicalBird
problem₃₉′-R* = record
  { Q₂ = R* ∙ B
  ; isQuizzicalBird = λ x y z → begin
      R* ∙ B ∙ x ∙ y ∙ z  ≈⟨ isRobinOnceRemoved B x y z ⟩
      B ∙ y ∙ z ∙ x       ≈⟨ isBluebird y z x ⟩
      y ∙ (z ∙ x)         ∎
  }

problem₄₁′ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasVireoOnceRemoved ⦄ → HasQuirkyBird
problem₄₁′ = record
  { Q₃ = V* ∙ B
  ; isQuirkyBird = λ x y z → begin
      V* ∙ B ∙ x ∙ y ∙ z  ≈⟨ isVireoOnceRemoved B x y z ⟩
      B ∙ z ∙ x ∙ y       ≈⟨ isBluebird z x y ⟩
      z ∙ (x ∙ y)         ∎
  }

problem₄₂′ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasFinchOnceRemoved ⦄ → HasQuackyBird
problem₄₂′ = record
  { Q₄ = F* ∙ B
  ; isQuackyBird = λ x y z → begin
      F* ∙ B ∙ x ∙ y ∙ z  ≈⟨ isFinchOnceRemoved B x y z ⟩
      B ∙ z ∙ y ∙ x       ≈⟨ isBluebird z y x ⟩
      z ∙ (y ∙ x)         ∎
  }

module _ ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ where
  private
    instance
      hasCardinal = problem₂₁-bonus
      hasCardinalOnceRemoved = problem₃₁
      hasRobinOnceRemoved = problem₃₂
      hasFinchOnceRemoved = problem₃₃
      hasVireoOnceRemoved = problem₃₄

  problem₃₇ : HasQueerBird
  problem₃₇ = problem₃₇′

  private instance hasQueerBird = problem₃₇

  problem₃₈ : HasQuixoticBird
  problem₃₈ = problem₃₈′

  private instance hasQuixoticBird = problem₃₈

  problem₃₉-F* : HasQuizzicalBird
  problem₃₉-F* = problem₃₉′-F*

  problem₃₉-R* : HasQuizzicalBird
  problem₃₉-R* = problem₃₉′-R*

  private instance hasQuizzicalBird = problem₃₉-F*

  problem₄₁ : HasQuirkyBird
  problem₄₁ = problem₄₁′

  problem₄₂ : HasQuackyBird
  problem₄₂ = problem₄₂′

module _ ⦃ _ : HasCardinal ⦄ where
  problem₄₀-Q₁ : ⦃ _ : HasQuizzicalBird ⦄ → HasQuixoticBird
  problem₄₀-Q₁ = record
    { Q₁ = C ∙ Q₂
    ; isQuixoticBird = λ x y z → begin
        C ∙ Q₂ ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ isCardinal Q₂ x y ⟩
        Q₂ ∙ y ∙ x ∙ z      ≈⟨ isQuizzicalBird y x z ⟩
        x ∙ (z ∙ y)         ∎
    }

  problem₄₀-Q₂ : ⦃ _ : HasQuixoticBird ⦄ → HasQuizzicalBird
  problem₄₀-Q₂ = record
    { Q₂ = C ∙ Q₁
    ; isQuizzicalBird = λ x y z → begin
        C ∙ Q₁ ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ isCardinal Q₁ x y ⟩
        Q₁ ∙ y ∙ x ∙ z      ≈⟨ isQuixoticBird y x z ⟩
        y ∙ (z ∙ x)         ∎
    }

  problem₄₃-Q₃ : ⦃ _ : HasQuackyBird ⦄ → HasQuirkyBird
  problem₄₃-Q₃ = record
    { Q₃ = C ∙ Q₄
    ; isQuirkyBird = λ x y z → begin
        C ∙ Q₄ ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ isCardinal Q₄ x y ⟩
        Q₄ ∙ y ∙ x ∙ z      ≈⟨ isQuackyBird y x z ⟩
        z ∙ (x ∙ y)         ∎
    }

  problem₄₃-Q₄ : ⦃ _ : HasQuirkyBird ⦄ → HasQuackyBird
  problem₄₃-Q₄ = record
    { Q₄ = C ∙ Q₃
    ; isQuackyBird = λ x y z → begin
        C ∙ Q₃ ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ isCardinal Q₃ x y ⟩
        Q₃ ∙ y ∙ x ∙ z      ≈⟨ isQuirkyBird y x z ⟩
        z ∙ (y ∙ x)         ∎
    }

problem₄₄ : ⦃ _ : HasQuixoticBird ⦄ ⦃ _ : HasThrush ⦄ → HasQuackyBird
problem₄₄ = record
  { Q₄ = Q₁ ∙ T
  ; isQuackyBird = λ x y z → begin
      Q₁ ∙ T ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ isQuixoticBird T x y ⟩
      T ∙ (y ∙ x) ∙ z     ≈⟨ isThrush (y ∙ x) z ⟩
      z ∙ (y ∙ x)         ∎
  }

problem₄₅ : ⦃ _ : HasQueerBird ⦄ ⦃ _ : HasThrush ⦄ → HasBluebird
problem₄₅ = record
  { B = Q ∙ T ∙ (Q ∙ Q)
  ; isBluebird = λ x y z → begin
      Q ∙ T ∙ (Q ∙ Q) ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ ∙-congʳ $ isQueerBird T (Q ∙ Q) x ⟩
      Q ∙ Q ∙ (T ∙ x) ∙ y ∙ z      ≈⟨ ∙-congʳ $ isQueerBird Q (T ∙ x) y ⟩
      T ∙ x ∙ (Q ∙ y) ∙ z          ≈⟨ ∙-congʳ $ isThrush x (Q ∙ y) ⟩
      Q ∙ y ∙ x ∙ z                ≈⟨ isQueerBird y x z ⟩
      x ∙ (y ∙ z)                  ∎
  }

problem₄₆ : ⦃ _ : HasQueerBird ⦄ ⦃ _ : HasThrush ⦄ → HasCardinal
problem₄₆ = record
  { C = Q ∙ Q ∙ (Q ∙ T)
  ; isCardinal = λ x y z → begin
      Q ∙ Q ∙ (Q ∙ T) ∙ x ∙ y ∙ z  ≈⟨ ∙-congʳ $ ∙-congʳ $ isQueerBird Q (Q ∙ T) x ⟩
      Q ∙ T ∙ (Q ∙ x) ∙ y ∙ z      ≈⟨ ∙-congʳ $ isQueerBird T (Q ∙ x) y ⟩
      Q ∙ x ∙ (T ∙ y) ∙ z          ≈⟨ isQueerBird x (T ∙ y) z ⟩
      T ∙ y ∙ (x ∙ z)              ≈⟨ isThrush y (x ∙ z) ⟩
      x ∙ z ∙ y                    ∎
  }

problem₄₇ : ⦃ _ : HasBluebird ⦄ ⦃ _ : HasThrush ⦄ → HasGoldfinch
problem₄₇ = record
  { G = D ∙ C
  ; isGoldfinch = λ x y z w → begin
      D ∙ C ∙ x ∙ y ∙ z ∙ w  ≈⟨ ∙-congʳ $ isDove C x y z ⟩
      C ∙ x ∙ (y ∙ z) ∙ w    ≈⟨ isCardinal x (y ∙ z) w ⟩
      x ∙ w ∙ (y ∙ z)        ∎
  } where
  instance
    hasCardinal = problem₂₁-bonus
    hasDove = problem₅
