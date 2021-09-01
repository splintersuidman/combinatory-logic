open import Mockingbird.Forest.Base using (Forest)

module Mockingbird.Forest.Birds {b ℓ} (forest : Forest {b} {ℓ}) where

open import Level using (_⊔_)
open import Data.Product using (_×_; ∃-syntax)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)

open Forest forest

-- TODO: consider using implicit arguments in the predicates, e.g.
--   IsMockingbird M = ∀ {x} → M ∙ x ≈ x ∙ x.

IsComposition : (A B C : Bird) → Set (b ⊔ ℓ)
IsComposition A B C = ∀ x → C ∙ x ≈ A ∙ (B ∙ x)

-- A forest ‘has composition’ if for every two birds A and B there exists a bird
-- C = A ∘ B such that C is the composition of A and B.
record HasComposition : Set (b ⊔ ℓ) where
  infixr 6 _∘_

  field
    _∘_ : (A B : Bird) → Bird
    isComposition : ∀ A B → IsComposition A B (A ∘ B)

open HasComposition ⦃ ... ⦄ public

IsMockingbird : Pred Bird (b ⊔ ℓ)
IsMockingbird M = ∀ x → M ∙ x ≈ x ∙ x

record HasMockingbird : Set (b ⊔ ℓ) where
  field
    M : Bird
    isMockingbird : IsMockingbird M

open HasMockingbird ⦃ ... ⦄ public

infix 4 _IsFondOf_
_IsFondOf_ : Rel Bird ℓ
A IsFondOf B = A ∙ B ≈ B

IsEgocentric : Pred Bird ℓ
IsEgocentric A = A IsFondOf A

Agree : (A B x : Bird) → Set ℓ
Agree A B x = A ∙ x ≈ B ∙ x

IsAgreeable : Pred Bird (b ⊔ ℓ)
IsAgreeable A = ∀ B → ∃[ x ] Agree A B x

Compatible : Rel Bird (b ⊔ ℓ)
Compatible A B = ∃[ x ] ∃[ y ] (A ∙ x ≈ y) × (B ∙ y ≈ x)

IsHappy : Pred Bird (b ⊔ ℓ)
IsHappy A = Compatible A A

IsNormal : Pred Bird (b ⊔ ℓ)
IsNormal A = ∃[ x ] A IsFondOf x

infix 4 _IsFixatedOn_
_IsFixatedOn_ : Rel Bird (b ⊔ ℓ)
A IsFixatedOn B = ∀ x → A ∙ x ≈ B

IsHopelesslyEgocentric : Pred Bird (b ⊔ ℓ)
IsHopelesslyEgocentric A = A IsFixatedOn A

IsKestrel : Pred Bird (b ⊔ ℓ)
IsKestrel K = ∀ x y → (K ∙ x) ∙ y ≈ x
-- Alternative definition:
-- IsKestrel K = ∀ x → K ∙ x IsFixatedOn x

record HasKestrel : Set (b ⊔ ℓ) where
  field
    K : Bird
    isKestrel : IsKestrel K

open HasKestrel ⦃ ... ⦄ public

IsIdentity : Pred Bird (b ⊔ ℓ)
IsIdentity I = ∀ x → I ∙ x ≈ x

record HasIdentity : Set (b ⊔ ℓ) where
  field
    I : Bird
    isIdentity : IsIdentity I

open HasIdentity ⦃ ... ⦄ public

IsLark : Pred Bird (b ⊔ ℓ)
IsLark L = ∀ x y → (L ∙ x) ∙ y ≈ x ∙ (y ∙ y)

record HasLark : Set (b ⊔ ℓ) where
  field
    L : Bird
    isLark : IsLark L

IsSageBird : Pred Bird (b ⊔ ℓ)
IsSageBird Θ = ∀ x → x IsFondOf (Θ ∙ x)

open HasLark ⦃ ... ⦄ public

record HasSageBird : Set (b ⊔ ℓ) where
  field
    Θ : Bird
    isSageBird : IsSageBird Θ

IsBluebird : Pred Bird (b ⊔ ℓ)
IsBluebird B = ∀ x y z → B ∙ x ∙ y ∙ z ≈ x ∙ (y ∙ z)

open HasSageBird ⦃ ... ⦄ public

record HasBluebird : Set (b ⊔ ℓ) where
  field
    B : Bird
    isBluebird : IsBluebird B

open HasBluebird ⦃ ... ⦄ public
 
IsDove : Pred Bird (b ⊔ ℓ)
IsDove D = ∀ x y z w → D ∙ x ∙ y ∙ z ∙ w ≈ x ∙ y ∙ (z ∙ w)

record HasDove : Set (b ⊔ ℓ) where
  field
    D : Bird
    isDove : IsDove D

open HasDove ⦃ ... ⦄ public

IsBlackbird : Pred Bird (b ⊔ ℓ)
IsBlackbird B₁ = ∀ x y z w → B₁ ∙ x ∙ y ∙ z ∙ w ≈ x ∙ (y ∙ z ∙ w)

record HasBlackbird : Set (b ⊔ ℓ) where
  field
    B₁ : Bird
    isBlackbird : IsBlackbird B₁

open HasBlackbird ⦃ ... ⦄ public

IsEagle : Pred Bird (b ⊔ ℓ)
IsEagle E = ∀ x y z w v → E ∙ x ∙ y ∙ z ∙ w ∙ v ≈ x ∙ y ∙ (z ∙ w ∙ v)

record HasEagle : Set (b ⊔ ℓ) where
  field
    E : Bird
    isEagle : IsEagle E

open HasEagle ⦃ ... ⦄ public

IsBunting : Pred Bird (b ⊔ ℓ)
IsBunting B₂ = ∀ x y z w v → B₂ ∙ x ∙ y ∙ z ∙ w ∙ v ≈ x ∙ (y ∙ z ∙ w ∙ v)

record HasBunting : Set (b ⊔ ℓ) where
  field
    B₂ : Bird
    isBunting : IsBunting B₂

open HasBunting ⦃ ... ⦄ public

IsDickcissel : Pred Bird (b ⊔ ℓ)
IsDickcissel D₁ = ∀ x y z w v → D₁ ∙ x ∙ y ∙ z ∙ w ∙ v ≈ x ∙ y ∙ z ∙ (w ∙ v)

record HasDickcissel : Set (b ⊔ ℓ) where
  field
    D₁ : Bird
    isDickcissel : IsDickcissel D₁

open HasDickcissel ⦃ ... ⦄ public

IsBecard : Pred Bird (b ⊔ ℓ)
IsBecard B₃ = ∀ x y z w → B₃ ∙ x ∙ y ∙ z ∙ w ≈ x ∙ (y ∙ (z ∙ w))

record HasBecard : Set (b ⊔ ℓ) where
  field
    B₃ : Bird
    isBecard : IsBecard B₃

open HasBecard ⦃ ... ⦄ public

IsDovekie : Pred Bird (b ⊔ ℓ)
IsDovekie D₂ = ∀ x y z w v → D₂ ∙ x ∙ y ∙ z ∙ w ∙ v ≈ x ∙ (y ∙ z) ∙ (w ∙ v)

record HasDovekie : Set (b ⊔ ℓ) where
  field
    D₂ : Bird
    isDovekie : IsDovekie D₂

open HasDovekie ⦃ ... ⦄ public

IsBaldEagle : Pred Bird (b ⊔ ℓ)
IsBaldEagle Ê = ∀ x y₁ y₂ y₃ z₁ z₂ z₃ → Ê ∙ x ∙ y₁ ∙ y₂ ∙ y₃ ∙ z₁ ∙ z₂ ∙ z₃ ≈ x ∙ (y₁ ∙ y₂ ∙ y₃) ∙ (z₁ ∙ z₂ ∙ z₃)

record HasBaldEagle : Set (b ⊔ ℓ) where
  field
    Ê : Bird
    isBaldEagle : IsBaldEagle Ê

open HasBaldEagle ⦃ ... ⦄ public

IsWarbler : Pred Bird (b ⊔ ℓ)
IsWarbler W = ∀ x y → W ∙ x ∙ y ≈ x ∙ y ∙ y

record HasWarbler : Set (b ⊔ ℓ) where
  field
    W : Bird
    isWarbler : IsWarbler W

open HasWarbler ⦃ ... ⦄ public

IsCardinal : Pred Bird (b ⊔ ℓ)
IsCardinal C = ∀ x y z → C ∙ x ∙ y ∙ z ≈ x ∙ z ∙ y

record HasCardinal : Set (b ⊔ ℓ) where
  field
    C : Bird
    isCardinal : IsCardinal C

open HasCardinal ⦃ ... ⦄ public

IsThrush : Pred Bird (b ⊔ ℓ)
IsThrush T = ∀ x y → T ∙ x ∙ y ≈ y ∙ x

record HasThrush : Set (b ⊔ ℓ) where
  field
    T : Bird
    isThrush : IsThrush T

open HasThrush ⦃ ... ⦄ public

Commute : (x y : Bird) → Set ℓ
Commute x y = x ∙ y ≈ y ∙ x

IsRobin : Pred Bird (b ⊔ ℓ)
IsRobin R = ∀ x y z → R ∙ x ∙ y ∙ z ≈ y ∙ z ∙ x

record HasRobin : Set (b ⊔ ℓ) where
  field
    R : Bird
    isRobin : IsRobin R

open HasRobin ⦃ ... ⦄ public

IsFinch : Pred Bird (b ⊔ ℓ)
IsFinch F = ∀ x y z → F ∙ x ∙ y ∙ z ≈ z ∙ y ∙ x

record HasFinch : Set (b ⊔ ℓ) where
  field
    F : Bird
    isFinch : IsFinch F

open HasFinch ⦃ ... ⦄ public

IsVireo : Pred Bird (b ⊔ ℓ)
IsVireo V = ∀ x y z → V ∙ x ∙ y ∙ z ≈ z ∙ x ∙ y

record HasVireo : Set (b ⊔ ℓ) where
  field
    V : Bird
    isVireo : IsVireo V

open HasVireo ⦃ ... ⦄ public

IsCardinalOnceRemoved : Pred Bird (b ⊔ ℓ)
IsCardinalOnceRemoved C* = ∀ x y z w → C* ∙ x ∙ y ∙ z ∙ w ≈ x ∙ y ∙ w ∙ z

record HasCardinalOnceRemoved : Set (b ⊔ ℓ) where
  field
    C* : Bird
    isCardinalOnceRemoved : IsCardinalOnceRemoved C*

open HasCardinalOnceRemoved ⦃ ... ⦄ public

IsRobinOnceRemoved : Pred Bird (b ⊔ ℓ)
IsRobinOnceRemoved R* = ∀ x y z w → R* ∙ x ∙ y ∙ z ∙ w ≈ x ∙ z ∙ w ∙ y

record HasRobinOnceRemoved : Set (b ⊔ ℓ) where
  field
    R* : Bird
    isRobinOnceRemoved : IsRobinOnceRemoved R*

open HasRobinOnceRemoved ⦃ ... ⦄ public

IsFinchOnceRemoved : Pred Bird (b ⊔ ℓ)
IsFinchOnceRemoved F* = ∀ x y z w → F* ∙ x ∙ y ∙ z ∙ w ≈ x ∙ w ∙ z ∙ y

record HasFinchOnceRemoved : Set (b ⊔ ℓ) where
  field
    F* : Bird
    isFinchOnceRemoved : IsFinchOnceRemoved F*

open HasFinchOnceRemoved ⦃ ... ⦄ public

IsVireoOnceRemoved : Pred Bird (b ⊔ ℓ)
IsVireoOnceRemoved V* = ∀ x y z w → V* ∙ x ∙ y ∙ z ∙ w ≈ x ∙ w ∙ y ∙ z

record HasVireoOnceRemoved : Set (b ⊔ ℓ) where
  field
    V* : Bird
    isVireoOnceRemoved : IsVireoOnceRemoved V*

open HasVireoOnceRemoved ⦃ ... ⦄ public

IsCardinalTwiceRemoved : Pred Bird (b ⊔ ℓ)
IsCardinalTwiceRemoved C** = ∀ x y z₁ z₂ z₃ → C** ∙ x ∙ y ∙ z₁ ∙ z₂ ∙ z₃ ≈ x ∙ y ∙ z₁ ∙ z₃ ∙ z₂

record HasCardinalTwiceRemoved : Set (b ⊔ ℓ) where
  field
    C** : Bird
    isCardinalTwiceRemoved : IsCardinalTwiceRemoved C**

open HasCardinalTwiceRemoved ⦃ ... ⦄ public

IsRobinTwiceRemoved : Pred Bird (b ⊔ ℓ)
IsRobinTwiceRemoved R** = ∀ x y z₁ z₂ z₃ → R** ∙ x ∙ y ∙ z₁ ∙ z₂ ∙ z₃ ≈ x ∙ y ∙ z₂ ∙ z₃ ∙ z₁

record HasRobinTwiceRemoved : Set (b ⊔ ℓ) where
  field
    R** : Bird
    isRobinTwiceRemoved : IsRobinTwiceRemoved R**

open HasRobinTwiceRemoved ⦃ ... ⦄ public

IsFinchTwiceRemoved : Pred Bird (b ⊔ ℓ)
IsFinchTwiceRemoved F** = ∀ x y z₁ z₂ z₃ → F** ∙ x ∙ y ∙ z₁ ∙ z₂ ∙ z₃ ≈ x ∙ y ∙ z₃ ∙ z₂ ∙ z₁

record HasFinchTwiceRemoved : Set (b ⊔ ℓ) where
  field
    F** : Bird
    isFinchTwiceRemoved : IsFinchTwiceRemoved F**

open HasFinchTwiceRemoved ⦃ ... ⦄ public

IsVireoTwiceRemoved : Pred Bird (b ⊔ ℓ)
IsVireoTwiceRemoved V** = ∀ x y z₁ z₂ z₃ → V** ∙ x ∙ y ∙ z₁ ∙ z₂ ∙ z₃ ≈ x ∙ y ∙ z₃ ∙ z₁ ∙ z₂

record HasVireoTwiceRemoved : Set (b ⊔ ℓ) where
  field
    V** : Bird
    isVireoTwiceRemoved : IsVireoTwiceRemoved V**

open HasVireoTwiceRemoved ⦃ ... ⦄ public

IsQueerBird : Pred Bird (b ⊔ ℓ)
IsQueerBird Q = ∀ x y z → Q ∙ x ∙ y ∙ z ≈ y ∙ (x ∙ z)

record HasQueerBird : Set (b ⊔ ℓ) where
  field
    Q : Bird
    isQueerBird : IsQueerBird Q

open HasQueerBird ⦃ ... ⦄ public

IsQuixoticBird : Pred Bird (b ⊔ ℓ)
IsQuixoticBird Q₁ = ∀ x y z → Q₁ ∙ x ∙ y ∙ z ≈ x ∙ (z ∙ y)

record HasQuixoticBird : Set (b ⊔ ℓ) where
  field
    Q₁ : Bird
    isQuixoticBird : IsQuixoticBird Q₁

open HasQuixoticBird ⦃ ... ⦄ public

IsQuizzicalBird : Pred Bird (b ⊔ ℓ)
IsQuizzicalBird Q₂ = ∀ x y z → Q₂ ∙ x ∙ y ∙ z ≈ y ∙ (z ∙ x)

record HasQuizzicalBird : Set (b ⊔ ℓ) where
  field
    Q₂ : Bird
    isQuizzicalBird : IsQuizzicalBird Q₂

open HasQuizzicalBird ⦃ ... ⦄ public

IsQuirkyBird : Pred Bird (b ⊔ ℓ)
IsQuirkyBird Q₃ = ∀ x y z → Q₃ ∙ x ∙ y ∙ z ≈ z ∙ (x ∙ y)

record HasQuirkyBird : Set (b ⊔ ℓ) where
  field
    Q₃ : Bird
    isQuirkyBird : IsQuirkyBird Q₃

open HasQuirkyBird ⦃ ... ⦄ public

IsQuackyBird : Pred Bird (b ⊔ ℓ)
IsQuackyBird Q₄ = ∀ x y z → Q₄ ∙ x ∙ y ∙ z ≈ z ∙ (y ∙ x)

record HasQuackyBird : Set (b ⊔ ℓ) where
  field
    Q₄ : Bird
    isQuackyBird : IsQuackyBird Q₄

open HasQuackyBird ⦃ ... ⦄ public

IsGoldfinch : Pred Bird (b ⊔ ℓ)
IsGoldfinch G = ∀ x y z w → G ∙ x ∙ y ∙ z ∙ w ≈ x ∙ w ∙ (y ∙ z)

record HasGoldfinch : Set (b ⊔ ℓ) where
  field
    G : Bird
    isGoldfinch : IsGoldfinch G

open HasGoldfinch ⦃ ... ⦄ public

IsDoubleMockingbird : Pred Bird (b ⊔ ℓ)
IsDoubleMockingbird M₂ = ∀ x y → M₂ ∙ x ∙ y ≈ x ∙ y ∙ (x ∙ y)

record HasDoubleMockingbird : Set (b ⊔ ℓ) where
  field
    M₂ : Bird
    isDoubleMockingbird : IsDoubleMockingbird M₂

open HasDoubleMockingbird ⦃ ... ⦄ public

IsConverseWarbler : Pred Bird (b ⊔ ℓ)
IsConverseWarbler W′ = ∀ x y → W′ ∙ x ∙ y ≈ y ∙ x ∙ x

record HasConverseWarbler : Set (b ⊔ ℓ) where
  field
    W′ : Bird
    isConverseWarbler : IsConverseWarbler W′

open HasConverseWarbler ⦃ ... ⦄ public

IsWarblerOnceRemoved : Pred Bird (b ⊔ ℓ)
IsWarblerOnceRemoved W* = ∀ x y z → W* ∙ x ∙ y ∙ z ≈ x ∙ y ∙ z ∙ z

record HasWarblerOnceRemoved : Set (b ⊔ ℓ) where
  field
    W* : Bird
    isWarblerOnceRemoved : IsWarblerOnceRemoved W*

open HasWarblerOnceRemoved ⦃ ... ⦄ public

IsWarblerTwiceRemoved : Pred Bird (b ⊔ ℓ)
IsWarblerTwiceRemoved W** = ∀ x y z w → W** ∙ x ∙ y ∙ z ∙ w ≈ x ∙ y ∙ z ∙ w ∙ w

record HasWarblerTwiceRemoved : Set (b ⊔ ℓ) where
  field
    W** : Bird
    isWarblerTwiceRemoved : IsWarblerTwiceRemoved W**

open HasWarblerTwiceRemoved ⦃ ... ⦄ public

IsHummingbird : Pred Bird (b ⊔ ℓ)
IsHummingbird H = ∀ x y z → H ∙ x ∙ y ∙ z ≈ x ∙ y ∙ z ∙ y

record HasHummingbird : Set (b ⊔ ℓ) where
  field
    H : Bird
    isHummingbird : IsHummingbird H

open HasHummingbird ⦃ ... ⦄ public

IsStarling : Pred Bird (b ⊔ ℓ)
IsStarling S = ∀ x y z → S ∙ x ∙ y ∙ z ≈ x ∙ z ∙ (y ∙ z)

record HasStarling : Set (b ⊔ ℓ) where
  field
    S : Bird
    isStarling : IsStarling S

open HasStarling ⦃ ... ⦄ public

IsPhoenix : Pred Bird (b ⊔ ℓ)
IsPhoenix Φ = ∀ x y z w → Φ ∙ x ∙ y ∙ z ∙ w ≈ x ∙ (y ∙ w) ∙ (z ∙ w)

record HasPhoenix : Set (b ⊔ ℓ) where
  field
    Φ : Bird
    isPhoenix : IsPhoenix Φ

open HasPhoenix ⦃ ... ⦄ public

IsPsiBird : Pred Bird (b ⊔ ℓ)
IsPsiBird Ψ = ∀ x y z w → Ψ ∙ x ∙ y ∙ z ∙ w ≈ x ∙ (y ∙ z) ∙ (y ∙ w)

record HasPsiBird : Set (b ⊔ ℓ) where
  field
    Ψ : Bird
    isPsiBird : IsPsiBird Ψ

open HasPsiBird ⦃ ... ⦄ public

IsTuringBird : Pred Bird (b ⊔ ℓ)
IsTuringBird U = ∀ x y → U ∙ x ∙ y ≈ y ∙ (x ∙ x ∙ y)

record HasTuringBird : Set (b ⊔ ℓ) where
  field
    U : Bird
    isTuringBird : IsTuringBird U

open HasTuringBird ⦃ ... ⦄ public

IsOwl : Pred Bird (b ⊔ ℓ)
IsOwl O = ∀ x y → O ∙ x ∙ y ≈ y ∙ (x ∙ y)

record HasOwl : Set (b ⊔ ℓ) where
  field
    O : Bird
    isOwl : IsOwl O

open HasOwl ⦃ ... ⦄ public

IsChoosy : Pred Bird (b ⊔ ℓ)
IsChoosy A = ∀ x → A IsFondOf x → IsSageBird x

IsJaybird : Pred Bird (b ⊔ ℓ)
IsJaybird J = ∀ x y z w → J ∙ x ∙ y ∙ z ∙ w ≈ x ∙ y ∙ (x ∙ w ∙ z)

record HasJaybird : Set (b ⊔ ℓ) where
  field
    J : Bird
    isJaybird : IsJaybird J

open HasJaybird ⦃ ... ⦄ public
