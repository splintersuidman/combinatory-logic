open import Mockingbird.Forest using (Forest)

-- To Mock a Mockingbird
module Mockingbird.Problems.Chapter09 {b ℓ} (forest : Forest {b} {ℓ}) where

open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Nullary using (¬_)

open import Mockingbird.Forest.Birds forest

open Forest forest

module _ ⦃ _ : HasComposition ⦄ ⦃ _ : HasMockingbird ⦄ where
  problem₁ : ∀ A → ∃[ B ] A IsFondOf B
  problem₁ A =
    let C = A ∘ M

        isFond : A IsFondOf (C ∙ C)
        isFond = sym $ begin
          C ∙ C        ≈⟨ isComposition A M C ⟩
          A ∙ (M ∙ C)  ≈⟨ ∙-congˡ (isMockingbird C) ⟩
          A ∙ (C ∙ C)  ∎

    in (C ∙ C , isFond)

module _ ⦃ _ : HasComposition ⦄ ⦃ _ : HasMockingbird ⦄ where
  problem₂ : ∃[ E ] IsEgocentric E
  problem₂ =
    let (E , isFond) = problem₁ M

        isEgocentric : IsEgocentric E
        isEgocentric = begin
          E ∙ E  ≈˘⟨ isMockingbird E ⟩
          M ∙ E  ≈⟨ isFond ⟩
          E      ∎

    in (E , isEgocentric)

module _ ⦃ _ : HasComposition ⦄ (hasAgreeable : ∃[ A ] IsAgreeable A) where
  A = proj₁ hasAgreeable
  isAgreeable = proj₂ hasAgreeable

  problem₃ : ∀ B → ∃[ C ] B IsFondOf C
  problem₃ B =
    let D = B ∘ A
        (x , Ax≈Dx) = isAgreeable D

        isFond : B IsFondOf (A ∙ x)
        isFond = begin
          B ∙ (A ∙ x)  ≈˘⟨ isComposition B A x ⟩
          D ∙ x        ≈˘⟨ Ax≈Dx ⟩
          A ∙ x        ∎

    in (A ∙ x , isFond)

-- Bonus question of Problem 3.
C₂→HasAgreeable : ⦃ _ : HasMockingbird ⦄ → ∃[ A ] IsAgreeable A
C₂→HasAgreeable = (M , λ B → (B , isMockingbird B))

module _ ⦃ _ : HasComposition ⦄ (A B C : Bird) (Cx≈A[Bx] : IsComposition A B C) where
  problem₄ : IsAgreeable C → IsAgreeable A
  problem₄ C-isAgreeable D =
    let E = D ∘ B
        (x , Cx≈Ex) = C-isAgreeable E

        agree : Agree A D (B ∙ x)
        agree = begin
          A ∙ (B ∙ x)  ≈˘⟨ Cx≈A[Bx] x ⟩
          C ∙ x        ≈⟨ Cx≈Ex ⟩
          E ∙ x        ≈⟨ isComposition D B x ⟩
          D ∙ (B ∙ x)  ∎

    in (B ∙ x , agree)

module _ ⦃ _ : HasComposition ⦄ where
  problem₅ : ∀ A B C → ∃[ D ] (∀ x → D ∙ x ≈ A ∙ (B ∙ (C ∙ x)))
  problem₅ A B C =
    let E = B ∘ C
        D = A ∘ E
    in (D , λ x → trans (isComposition A E x) $ ∙-congˡ (isComposition B C x))

module _ ⦃ _ : HasComposition ⦄ ⦃ _ : HasMockingbird ⦄ where
  problem₆ : ∀ A B → Compatible A B
  problem₆ A B =
    let C = A ∘ B
        (y , Cy≈y) = problem₁ C
        x = B ∙ y
    in (x , y , trans (sym (isComposition A B y)) Cy≈y , refl)

problem₇ : ∀ A → ∃[ B ] A IsFondOf B → IsHappy A
problem₇ A (B , AB≈B) = (B , B , AB≈B , AB≈B)
-- problem₇ : ∀ A → IsNormal A → IsHappy A

module _ ⦃ _ : HasComposition ⦄ where
  problem₈ : ∃[ H ] IsHappy H → ∃[ N ] IsNormal N
  problem₈ (H , x , y , Hx≈y , Hy≈x) =
    let N = H ∘ H

        isFond : N IsFondOf x
        isFond = begin
          N ∙ x        ≈⟨ isComposition H H x ⟩
          H ∙ (H ∙ x)  ≈⟨ ∙-congˡ Hx≈y ⟩
          H ∙ y        ≈⟨ Hy≈x ⟩
          x            ∎

    in (N , x , isFond)

module _ ⦃ _ : HasComposition ⦄ ⦃ _ : HasMockingbird ⦄ ⦃ _ : HasKestrel ⦄ where
  problem₉ : ∃[ A ] IsHopelesslyEgocentric A
  problem₉ =
    let (A , KA≈A) = problem₁ K

        isHopelesslyEgocentric : IsHopelesslyEgocentric A
        isHopelesslyEgocentric x = begin
          A ∙ x        ≈˘⟨ ∙-congʳ KA≈A ⟩
          (K ∙ A) ∙ x  ≈⟨ isKestrel A x ⟩
          A            ∎

    in (A , isHopelesslyEgocentric)

problem₁₀ : ∀ x y → x IsFixatedOn y → x IsFondOf y
problem₁₀ x y xz≈y = xz≈y y

problem₁₁ : ∀ K → IsKestrel K → IsEgocentric K → IsHopelesslyEgocentric K
problem₁₁ K isKestrel KK≈K x = begin
  K ∙ x        ≈˘⟨ ∙-congʳ KK≈K ⟩
  (K ∙ K) ∙ x  ≈⟨ isKestrel K x ⟩
  K            ∎

problem₁₂ : ⦃ _ : HasKestrel ⦄ → ∀ x → IsEgocentric (K ∙ x) → K IsFondOf x
problem₁₂ x [Kx][Kx]≈Kx = begin
  K ∙ x              ≈˘⟨ [Kx][Kx]≈Kx ⟩
  (K ∙ x) ∙ (K ∙ x)  ≈⟨ isKestrel x (K ∙ x) ⟩
  x                  ∎

problem₁₃ : ∀ A x y → IsHopelesslyEgocentric A → A ∙ x ≈ A ∙ y
problem₁₃ A x y Az≈A = begin
  A ∙ x  ≈⟨ Az≈A x ⟩
  A      ≈˘⟨ Az≈A y ⟩
  A ∙ y  ∎

problem₁₄ : ∀ A x y → IsHopelesslyEgocentric A → (A ∙ x) ∙ y ≈ A
problem₁₄ A x y Az≈A = begin
  (A ∙ x) ∙ y  ≈⟨ ∙-congʳ (Az≈A x) ⟩
  A ∙ y        ≈⟨ Az≈A y ⟩
  A            ∎

problem₁₅ : ∀ A x → IsHopelesslyEgocentric A → IsHopelesslyEgocentric (A ∙ x)
problem₁₅ A x Az≈A y = begin
  (A ∙ x) ∙ y  ≈⟨ ∙-congʳ (Az≈A x) ⟩
  A ∙ y        ≈⟨ Az≈A y ⟩
  A            ≈˘⟨ Az≈A x ⟩
  A ∙ x        ∎

problem₁₆ : ∀ K → IsKestrel K → ∀ x y → K ∙ x ≈ K ∙ y → x ≈ y
problem₁₆ K isKestrel x y Kx≈Ky = begin
  x            ≈˘⟨ isKestrel x K ⟩
  -- NOTE: for the right-most kestrel, we can choose any bird. (Since we know
  -- only of three birds to exist here, the only option is a combination of
  -- {K, x, y}).
  (K ∙ x) ∙ K  ≈⟨ ∙-congʳ Kx≈Ky ⟩
  (K ∙ y) ∙ K  ≈⟨ isKestrel y K ⟩
  y            ∎

problem₁₇ : ∀ A x y → A IsFixatedOn x → A IsFixatedOn y → x ≈ y
problem₁₇ A x y Az≈x Az≈y = begin
  x      ≈˘⟨ Az≈x A ⟩
  -- NOTE: for the right-most A, we can choose any bird. (In this case a
  -- combination of {A, B, C}).
  A ∙ A  ≈⟨ Az≈y A ⟩
  y      ∎

problem₁₈ : ⦃ _ : HasKestrel ⦄ → ∀ x → K IsFondOf K ∙ x → K IsFondOf x
problem₁₈ x K[Kx]≈Kx = begin
  K ∙ x              ≈˘⟨ isKestrel (K ∙ x) x ⟩
  -- NOTE: for the right-most x, we can choose any bird.
  (K ∙ (K ∙ x)) ∙ x  ≈⟨ ∙-congʳ K[Kx]≈Kx ⟩
  (K ∙ x) ∙ x        ≈⟨ isKestrel x x ⟩
  x                  ∎

-- In the circumstances of Problem 19, the only bird in the forest is the
-- kestrel.
problem₁₉ : ∀ K → IsKestrel K → IsEgocentric K → ∀ x → x ≈ K
problem₁₉ K isKestrel KK≈K x = begin
  x            ≈⟨ lemma x x ⟩
  K ∙ x        ≈˘⟨ ∙-congʳ KK≈K ⟩
  (K ∙ K) ∙ x  ≈⟨ isKestrel K x ⟩
  K            ∎
  where
    lemma : ∀ y z → y ≈ K ∙ z
    lemma y z = begin
      y                  ≈˘⟨ isKestrel y z ⟩
      (K ∙ y) ∙ z        ≈˘⟨ ∙-congʳ (∙-congʳ KK≈K) ⟩
      ((K ∙ K) ∙ y) ∙ z  ≈⟨ ∙-congʳ (isKestrel K y) ⟩
      K ∙ z              ∎

module _ ⦃ _ : HasIdentity ⦄ where
  problem₂₀ : IsAgreeable I → ∀ A → ∃[ B ] A IsFondOf B
  problem₂₀ isAgreeable A =
    let (B , IB≈AB) = isAgreeable A

        isFond : A IsFondOf B
        isFond = begin
          A ∙ B  ≈˘⟨ IB≈AB ⟩
          I ∙ B  ≈⟨ isIdentity B ⟩
          B      ∎

    in (B , isFond)

  problem₂₁ : (∀ A → ∃[ B ] A IsFondOf B) → IsAgreeable I
  problem₂₁ isFond A =
    let (B , AB≈B) = isFond A

        agree : I ∙ B ≈ A ∙ B
        agree = begin
          I ∙ B  ≈⟨ isIdentity B ⟩
          B      ≈˘⟨ AB≈B ⟩
          A ∙ B  ∎

    in (B , agree)

  problem₂₂-1 : (∀ A B → Compatible A B) → ∀ A → IsNormal A
  problem₂₂-1 compatible A =
    let (x , y , Ix≈y , Ay≈x) = compatible I A

        isFond : A IsFondOf y
        isFond = begin
          A ∙ y  ≈⟨ Ay≈x ⟩
          x      ≈˘⟨ isIdentity x ⟩
          I ∙ x  ≈⟨ Ix≈y ⟩
          y      ∎
    in (y , isFond)

  problem₂₂-2 : (∀ A B → Compatible A B) → IsAgreeable I
  problem₂₂-2 compatible A =
    let (x , y , Ix≈y , Ay≈x) = compatible I A

        agree : Agree I A y
        agree = begin
          I ∙ y  ≈⟨ isIdentity y ⟩
          y      ≈˘⟨ Ix≈y ⟩
          I ∙ x  ≈⟨ isIdentity x ⟩
          x      ≈˘⟨ Ay≈x ⟩
          A ∙ y  ∎

    in (y , agree)

  problem₂₃ : IsHopelesslyEgocentric I → ∀ x → I ≈ x
  problem₂₃ isHopelesslyEgocentric x = begin
    I      ≈˘⟨ isHopelesslyEgocentric x ⟩
    I ∙ x  ≈⟨ isIdentity x ⟩
    x      ∎

module _ ⦃ _ : HasLark ⦄ ⦃ _ : HasIdentity ⦄ where
  problem₂₄ : HasMockingbird
  problem₂₄ = record
    { M = L ∙ I
    ; isMockingbird = λ x → begin
        (L ∙ I) ∙ x  ≈⟨ isLark I x ⟩
        I ∙ (x ∙ x)  ≈⟨ isIdentity (x ∙ x) ⟩
        x ∙ x        ∎
    }

module _ ⦃ _ : HasLark ⦄ where
  problem₂₅ : ∀ x → IsNormal x
  problem₂₅ x =
    let isFond : x IsFondOf (L ∙ x) ∙ (L ∙ x)
        isFond = begin
          x ∙ ((L ∙ x) ∙ (L ∙ x))  ≈˘⟨ isLark x (L ∙ x) ⟩
          (L ∙ x) ∙ (L ∙ x)        ∎
    in ((L ∙ x) ∙ (L ∙ x) , isFond)

  problem₂₆ : IsHopelesslyEgocentric L → ∀ x → x IsFondOf L
  problem₂₆ isHopelesslyEgocentric x = begin
    x ∙ L        ≈˘⟨ ∙-congˡ $ isHopelesslyEgocentric L ⟩
    x ∙ (L ∙ L)  ≈˘⟨ isLark x L ⟩
    (L ∙ x) ∙ L  ≈⟨ ∙-congʳ $ isHopelesslyEgocentric x ⟩
    L ∙ L        ≈⟨ isHopelesslyEgocentric L ⟩
    L            ∎

module _ ⦃ _ : HasLark ⦄ ⦃ _ : HasKestrel ⦄ where
  problem₂₇ : L ≉ K → ¬ L IsFondOf K
  problem₂₇ L≉K isFond =
    let K-fondOf-KK : K IsFondOf K ∙ K
        K-fondOf-KK = begin
          K ∙ (K ∙ K)              ≈˘⟨ ∙-congʳ isFond ⟩
          (L ∙ K) ∙ (K ∙ K)        ≈⟨ isLark K (K ∙ K) ⟩
          K ∙ ((K ∙ K) ∙ (K ∙ K))  ≈⟨ ∙-congˡ $ isKestrel K (K ∙ K) ⟩
          K ∙ K                    ∎

        isEgocentric : IsEgocentric K
        isEgocentric = problem₁₈ K K-fondOf-KK

        L≈K : L ≈ K
        L≈K = problem₁₉ K isKestrel isEgocentric L

    in L≉K L≈K

  problem₂₈ : K IsFondOf L → ∀ x → x IsFondOf L
  problem₂₈ KL≈L =
    let isHopelesslyEgocentric : IsHopelesslyEgocentric L
        isHopelesslyEgocentric y = begin
          L ∙ y        ≈˘⟨ ∙-congʳ KL≈L ⟩
          (K ∙ L) ∙ y  ≈⟨ isKestrel L y ⟩
          L            ∎
    in problem₂₆ isHopelesslyEgocentric

module _ ⦃ _ : HasLark ⦄ where
  problem₂₉ : ∃[ x ] IsEgocentric x
  problem₂₉ =
    let (y , [LL]y≈y) = problem₂₅ (L ∙ L)

        isEgocentric : IsEgocentric (y ∙ y)
        isEgocentric = begin
          (y ∙ y) ∙ (y ∙ y)  ≈˘⟨ isLark (y ∙ y) y ⟩
          (L ∙ (y ∙ y)) ∙ y  ≈˘⟨ ∙-congʳ (isLark L y) ⟩
          ((L ∙ L) ∙ y) ∙ y  ≈⟨ ∙-congʳ [LL]y≈y ⟩
          y ∙ y              ∎

        -- The expression of yy in terms of L and brackets.
        _  : y ∙ y ≈ ((L ∙ (L ∙ L)) ∙ (L ∙ (L ∙ L))) ∙ ((L ∙ (L ∙ L)) ∙ (L ∙ (L ∙ L)))
        _ = refl

    in (y ∙ y , isEgocentric)
