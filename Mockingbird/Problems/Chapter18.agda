open import Mockingbird.Forest using (Forest)
import Mockingbird.Forest.Birds as Birds

-- The Master Forest
module Mockingbird.Problems.Chapter18 {b ℓ} (forest : Forest {b} {ℓ})
                                      ⦃ _ : Birds.HasStarling forest ⦄
                                      ⦃ _ : Birds.HasKestrel forest ⦄ where

open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Data.Vec.Relation.Unary.Any.Properties using (++⁺ʳ)
open import Function using (_$_)
open import Level using (_⊔_)
open import Mockingbird.Forest.Combination.Vec forest using (⟨_⟩; here; there; [_]; _⟨∙⟩_∣_; _⟨∙⟩_; [#_])
open import Mockingbird.Forest.Combination.Vec.Properties forest using (subst′; weaken-++ˡ; weaken-++ʳ; ++-comm)
open import Relation.Unary using (_∈_)

open Forest forest
open import Mockingbird.Forest.Birds forest

problem₁ : HasIdentity
problem₁ = record
  { I = S ∙ K ∙ K
  ; isIdentity = λ x → begin
      S ∙ K ∙ K ∙ x    ≈⟨ isStarling K K x ⟩
      K ∙ x ∙ (K ∙ x)  ≈⟨ isKestrel x (K ∙ x) ⟩
      x                ∎
  }

private instance hasIdentity = problem₁

problem₂ : HasMockingbird
problem₂ = record
  { M = S ∙ I ∙ I
  ; isMockingbird = λ x → begin
      S ∙ I ∙ I ∙ x    ≈⟨ isStarling I I x ⟩
      I ∙ x ∙ (I ∙ x)  ≈⟨ congʳ $ isIdentity x ⟩
      x ∙ (I ∙ x)      ≈⟨ congˡ $ isIdentity x ⟩
      x ∙ x            ∎
  }

private instance hasMockingbird = problem₂

problem₃ : HasThrush
problem₃ = record
  { T = S ∙ (K ∙ (S ∙ I)) ∙ K
  ; isThrush = λ x y → begin
      S ∙ (K ∙ (S ∙ I)) ∙ K ∙ x ∙ y  ≈⟨ congʳ $ isStarling (K ∙ (S ∙ I)) K x ⟩
      K ∙ (S ∙ I) ∙ x ∙ (K ∙ x) ∙ y  ≈⟨ (congʳ $ congʳ $ isKestrel (S ∙ I) x) ⟩
      S ∙ I ∙ (K ∙ x) ∙ y            ≈⟨ isStarling I (K ∙ x) y ⟩
      I ∙ y ∙ (K ∙ x ∙ y)            ≈⟨ congʳ $ isIdentity y ⟩
      y ∙ (K ∙ x ∙ y)                ≈⟨ congˡ $ isKestrel x y ⟩
      y ∙ x                          ∎
  }

-- TODO: Problem 4.

I∈⟨S,K⟩ : I ∈ ⟨ S ∷ K ∷ [] ⟩
I∈⟨S,K⟩ = subst′ refl $ [# 0 ] ⟨∙⟩ [# 1 ] ⟨∙⟩ [# 1 ]

-- Try to strengthen a proof of X ∈ ⟨ y ∷ xs ⟩ to X ∈ ⟨ xs ⟩, which can be done
-- if y does not occur in X.
strengthen : ∀ {n X y} {xs : Vec Bird n} → X ∈ ⟨ y ∷ xs ⟩ → Maybe (X ∈ ⟨ xs ⟩)
-- NOTE: it could be the case that y ∈ xs, but checking that requires decidable
-- equality.
strengthen [ here X≈y ] = nothing
strengthen [ there X∈xs ] = just [ X∈xs ]
strengthen (Y∈⟨y,xs⟩ ⟨∙⟩ Z∈⟨y,xs⟩ ∣ YZ≈X) = do
  Y∈⟨xs⟩ ← strengthen Y∈⟨y,xs⟩
  Z∈⟨xs⟩ ← strengthen Z∈⟨y,xs⟩
  just $ Y∈⟨xs⟩ ⟨∙⟩ Z∈⟨xs⟩ ∣ YZ≈X
  where
    open import Data.Maybe.Categorical using (monad)
    open import Category.Monad using (RawMonad)
    open RawMonad (monad {b ⊔ ℓ})

eliminate : ∀ {n X y} {xs : Vec Bird n} → X ∈ ⟨ y ∷ xs ⟩ → ∃[ X′ ] (X′ ∈ ⟨ S ∷ K ∷ xs ⟩ × X′ ∙ y ≈ X)
eliminate {X = X} {y} [ here X≈y ] = (I , weaken-++ˡ I∈⟨S,K⟩ , trans (isIdentity y) (sym X≈y))
eliminate {X = X} {y} [ there X∈xs ] = (K ∙ X , [# 1 ] ⟨∙⟩ [ ++⁺ʳ (S ∷ K ∷ []) X∈xs ] , isKestrel X y)
eliminate {X = X} {y} (_⟨∙⟩_∣_ {Y} {Z} Y∈⟨y,xs⟩ [ here Z≈y ] YZ≈X) with strengthen Y∈⟨y,xs⟩
... | just Y∈⟨xs⟩ = (Y , weaken-++ʳ (S ∷ K ∷ []) Y∈⟨xs⟩ , trans (congˡ (sym Z≈y)) YZ≈X)
... | nothing =
  let (Y′ , Y′∈⟨S,K,xs⟩ , Y′y≈Y) = eliminate Y∈⟨y,xs⟩

      SY′Iy≈X : S ∙ Y′ ∙ I ∙ y ≈ X
      SY′Iy≈X = begin
        S ∙ Y′ ∙ I ∙ y    ≈⟨ isStarling Y′ I y ⟩
        Y′ ∙ y ∙ (I ∙ y)  ≈⟨ congʳ $ Y′y≈Y ⟩
        Y ∙ (I ∙ y)       ≈⟨ congˡ $ isIdentity y ⟩
        Y ∙ y             ≈˘⟨ congˡ Z≈y ⟩
        Y ∙ Z             ≈⟨ YZ≈X ⟩
        X                 ∎
  in (S ∙ Y′ ∙ I , [# 0 ] ⟨∙⟩ Y′∈⟨S,K,xs⟩ ⟨∙⟩ weaken-++ˡ I∈⟨S,K⟩ , SY′Iy≈X)
eliminate {X = X} {y} (_⟨∙⟩_∣_ {Y} {Z} Y∈⟨y,xs⟩ Z∈⟨y,xs⟩ YZ≈X) =
  let (Y′ , Y′∈⟨S,K,xs⟩ , Y′y≈Y) = eliminate Y∈⟨y,xs⟩
      (Z′ , Z′∈⟨S,K,xs⟩ , Z′y≈Z) = eliminate Z∈⟨y,xs⟩

      SY′Z′y≈X : S ∙ Y′ ∙ Z′ ∙ y ≈ X
      SY′Z′y≈X = begin
        S ∙ Y′ ∙ Z′ ∙ y    ≈⟨ isStarling Y′ Z′ y ⟩
        Y′ ∙ y ∙ (Z′ ∙ y)  ≈⟨ congʳ Y′y≈Y ⟩
        Y ∙ (Z′ ∙ y)       ≈⟨ congˡ Z′y≈Z ⟩
        Y ∙ Z              ≈⟨ YZ≈X ⟩
        X                  ∎
  in (S ∙ Y′ ∙ Z′ , [# 0 ] ⟨∙⟩ Y′∈⟨S,K,xs⟩ ⟨∙⟩ Z′∈⟨S,K,xs⟩ , SY′Z′y≈X)

module _ (x y : Bird) where
  -- Example: y-eliminating the expression y should give I.
  _ : proj₁ (eliminate {y = y} {xs = x ∷ []} $ [# 0 ]) ≈ I
  _ = refl

  -- Example: y-eliminating the expression x should give Kx.
  _ : proj₁ (eliminate {y = y} {xs = x ∷ []} $ [# 1 ]) ≈ K ∙ x
  _ = refl

  -- Example: y-eliminating the expression xy should give x (Principle 3).
  _ : proj₁ (eliminate {y = y} {xs = x ∷ []} $ [# 1 ] ⟨∙⟩ [# 0 ]) ≈ x
  _ = refl

  -- Example: y-eliminating the expression yx should give SI(Kx).
  _ : proj₁ (eliminate {y = y} {xs = x ∷ []} $ [# 0 ] ⟨∙⟩ [# 1 ]) ≈ S ∙ I ∙ (K ∙ x)
  _ = refl

  -- Example: y-eliminating the expression yy should give SII.
  _ : proj₁ (eliminate {y = y} {xs = x ∷ []} $ [# 0 ] ⟨∙⟩ [# 0 ]) ≈ S ∙ I ∙ I
  _ = refl

strengthen-SK : ∀ {n X y} {xs : Vec Bird n} → X ∈ ⟨ S ∷ K ∷ y ∷ xs ⟩ → Maybe (X ∈ ⟨ S ∷ K ∷ xs ⟩)
strengthen-SK {y = y} {xs} X∈⟨S,K,y,xs⟩ = do
  let X∈⟨y,xs,S,K⟩ = ++-comm (S ∷ K ∷ []) (y ∷ xs) X∈⟨S,K,y,xs⟩
  X∈⟨xs,S,K⟩ ← strengthen X∈⟨y,xs,S,K⟩
  let X∈⟨S,K,xs⟩ = ++-comm xs (S ∷ K ∷ []) X∈⟨xs,S,K⟩
  just X∈⟨S,K,xs⟩
  where
    open import Data.Maybe.Categorical using (monad)
    open import Category.Monad using (RawMonad)
    open RawMonad (monad {b ⊔ ℓ})

-- TODO: formulate eliminate or eliminate-SK in terms of the other.
eliminate-SK : ∀ {n X y} {xs : Vec Bird n} → X ∈ ⟨ S ∷ K ∷ y ∷ xs ⟩ → ∃[ X′ ] (X′ ∈ ⟨ S ∷ K ∷ xs ⟩ × X′ ∙ y ≈ X)
eliminate-SK {X = X} {y} [ here X≈S ] = (K ∙ S , [# 1 ] ⟨∙⟩ [# 0 ] , trans (isKestrel S y) (sym X≈S))
eliminate-SK {X = X} {y} [ there (here X≈K) ] = (K ∙ K , [# 1 ] ⟨∙⟩ [# 1 ] , trans (isKestrel K y) (sym X≈K))
eliminate-SK {X = X} {y} [ there (there (here X≈y)) ] = (I , weaken-++ˡ I∈⟨S,K⟩ , trans (isIdentity y) (sym X≈y))
eliminate-SK {X = X} {y} [ there (there (there X∈xs)) ] = (K ∙ X , ([# 1 ] ⟨∙⟩ [ (++⁺ʳ (S ∷ K ∷ []) X∈xs) ]) , isKestrel X y)
eliminate-SK {X = X} {y} (_⟨∙⟩_∣_ {Y} {Z} Y∈⟨S,K,y,xs⟩ [ there (there (here Z≈y)) ] YZ≈X) with strengthen-SK Y∈⟨S,K,y,xs⟩
... | just Y∈⟨S,K,xs⟩ = (Y , Y∈⟨S,K,xs⟩ , trans (congˡ (sym Z≈y)) YZ≈X)
... | nothing =
  let (Y′ , Y′∈⟨S,K,xs⟩ , Y′y≈Y) = eliminate-SK Y∈⟨S,K,y,xs⟩

      SY′Iy≈X : S ∙ Y′ ∙ I ∙ y ≈ X
      SY′Iy≈X = begin
        S ∙ Y′ ∙ I ∙ y    ≈⟨ isStarling Y′ I y ⟩
        Y′ ∙ y ∙ (I ∙ y)  ≈⟨ congʳ $ Y′y≈Y ⟩
        Y ∙ (I ∙ y)       ≈⟨ congˡ $ isIdentity y ⟩
        Y ∙ y             ≈˘⟨ congˡ Z≈y ⟩
        Y ∙ Z             ≈⟨ YZ≈X ⟩
        X                 ∎
  in (S ∙ Y′ ∙ I , [# 0 ] ⟨∙⟩ Y′∈⟨S,K,xs⟩ ⟨∙⟩ weaken-++ˡ I∈⟨S,K⟩ , SY′Iy≈X)
eliminate-SK {X = X} {y} (_⟨∙⟩_∣_ {Y} {Z} Y∈⟨S,K,y,xs⟩ Z∈⟨S,K,y,xs⟩ YZ≈X) =
  let (Y′ , Y′∈⟨S,K,xs⟩ , Y′y≈Y) = eliminate-SK Y∈⟨S,K,y,xs⟩
      (Z′ , Z′∈⟨S,K,xs⟩ , Z′y≈Z) = eliminate-SK Z∈⟨S,K,y,xs⟩

      SY′Z′y≈X : S ∙ Y′ ∙ Z′ ∙ y ≈ X
      SY′Z′y≈X = begin
        S ∙ Y′ ∙ Z′ ∙ y    ≈⟨ isStarling Y′ Z′ y ⟩
        Y′ ∙ y ∙ (Z′ ∙ y)  ≈⟨ congʳ Y′y≈Y ⟩
        Y ∙ (Z′ ∙ y)       ≈⟨ congˡ Z′y≈Z ⟩
        Y ∙ Z              ≈⟨ YZ≈X ⟩
        X                  ∎
  in (S ∙ Y′ ∙ Z′ , [# 0 ] ⟨∙⟩ Y′∈⟨S,K,xs⟩ ⟨∙⟩ Z′∈⟨S,K,xs⟩ , SY′Z′y≈X)

module _ (x y : Bird) where
  -- Example: y-eliminating the expression y should give I.
  _ : proj₁ (eliminate-SK {y = y} {xs = x ∷ []} $ [# 2 ]) ≈ I
  _ = refl

  -- Example: y-eliminating the expression x should give Kx.
  _ : proj₁ (eliminate-SK {y = y} {xs = x ∷ []} $ [# 3 ]) ≈ K ∙ x
  _ = refl

  -- Example: y-eliminating the expression xy should give x (Principle 3).
  _ : proj₁ (eliminate-SK {y = y} {xs = x ∷ []} $ [# 3 ] ⟨∙⟩ [# 2 ]) ≈ x
  _ = refl

  -- Example: y-eliminating the expression yx should give SI(Kx).
  _ : proj₁ (eliminate-SK {y = y} {xs = x ∷ []} $ [# 2 ] ⟨∙⟩ [# 3 ]) ≈ S ∙ I ∙ (K ∙ x)
  _ = refl

  -- Example: y-eliminating the expression yy should give SII.
  _ : proj₁ (eliminate-SK {y = y} {xs = x ∷ []} $ [# 2 ] ⟨∙⟩ [# 2 ]) ≈ S ∙ I ∙ I
  _ = refl

infixl 6 _∙ⁿ_
_∙ⁿ_ : ∀ {n} → (A : Bird) (xs : Vec Bird n) → Bird
A ∙ⁿ [] = A
A ∙ⁿ (x ∷ xs) = A ∙ⁿ xs ∙ x

eliminateAll′ : ∀ {n X} {xs : Vec Bird n} → X ∈ ⟨ S ∷ K ∷ xs ⟩ → ∃[ X′ ] (X′ ∈ ⟨ S ∷ K ∷ [] ⟩ × X′ ∙ⁿ xs ≈ X)
eliminateAll′ {X = X} {[]} X∈⟨S,K⟩ = (X , X∈⟨S,K⟩ , refl)
eliminateAll′ {X = X} {x ∷ xs} X∈⟨S,K,x,xs⟩ =
  let (X′ , X′∈⟨S,K,xs⟩ , X′x≈X) = eliminate-SK X∈⟨S,K,x,xs⟩
      (X″ , X″∈⟨S,K⟩ , X″xs≈X′) = eliminateAll′ X′∈⟨S,K,xs⟩

      X″∙ⁿxs∙x≈X : X″ ∙ⁿ xs ∙ x ≈ X
      X″∙ⁿxs∙x≈X = begin
        X″ ∙ⁿ xs ∙ x  ≈⟨ congʳ X″xs≈X′ ⟩
        X′ ∙ x           ≈⟨ X′x≈X ⟩
        X                ∎
  in (X″ , X″∈⟨S,K⟩ , X″∙ⁿxs∙x≈X)

-- TOOD: can we do this in some way without depending on xs : Vec Bird n?
eliminateAll : ∀ {n X} {xs : Vec Bird n} → X ∈ ⟨ xs ⟩ → ∃[ X′ ] (X′ ∈ ⟨ S ∷ K ∷ [] ⟩ × X′ ∙ⁿ xs ≈ X)
eliminateAll X∈⟨xs⟩ = eliminateAll′ $ weaken-++ʳ (S ∷ K ∷ []) X∈⟨xs⟩
