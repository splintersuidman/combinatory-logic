module CombinatoryLogic.Forest where

open import Data.Product using (_,_)
open import Function using (_$_)
open import Mockingbird.Forest using (Forest)

open import CombinatoryLogic.Equality as Equality using (isEquivalence; ∙-cong)
open import CombinatoryLogic.Semantics as ⊢ using (_≈_)
open import CombinatoryLogic.Syntax as Syntax using (Combinator)

forest : Forest
forest = record
  { Bird = Combinator
  ; _≈_ = _≈_
  ; _∙_ = Syntax._∙_
  ; isForest = record
    { isEquivalence = isEquivalence
    ; ∙-cong = ∙-cong
    }
  }

open Forest forest

open import Mockingbird.Forest.Birds forest
open import Mockingbird.Forest.Extensionality forest
import Mockingbird.Problems.Chapter11 forest as Chapter₁₁
import Mockingbird.Problems.Chapter12 forest as Chapter₁₂

instance
  hasWarbler : HasWarbler
  hasWarbler = record
    { W = Syntax.W
    ; isWarbler = λ _ _ → ⊢.W
    }

  hasKestrel : HasKestrel
  hasKestrel = record
    { K = Syntax.K
    ; isKestrel = λ _ _ → ⊢.K
    }

  hasBluebird : HasBluebird
  hasBluebird = record
    { B = Syntax.B
    ; isBluebird = λ _ _ _ → ⊢.B
    }

  hasIdentity : HasIdentity
  hasIdentity = record
    { I = Syntax.I
    ; isIdentity = λ _ → Equality.prop₉
    }

  hasMockingbird : HasMockingbird
  hasMockingbird = Chapter₁₁.problem₁₄

  hasLark : HasLark
  hasLark = Chapter₁₂.problem₃

  hasComposition : HasComposition
  hasComposition = Chapter₁₁.problem₁
