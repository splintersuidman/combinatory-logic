module CombinatoryLogic.Syntax where

open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Kapitel 1, Abschnitt C, §4 (Symbolische Festsetzungen), Def. 1
infixl 6 _∙_

data Combinator : Set where
  -- Kapitel 1, Abschnitt C, §3 (Die formalen Grundbegriffe)
  B C W K Q Π P ∧ : Combinator
  -- Kapitel 1, Abschnitt C, §2, c (Anwendung)
  _∙_ : (X Y : Combinator) → Combinator

-- NOTE: for the (intensional) equality defined by Kapitel 1, Abschnitt C, §4
-- (Symbolische Festsetzungen), Festsetzung 2, we use the propositional equality
-- _≡_.

toString : Combinator → String
toString (X ∙ Y@(_ ∙ _)) = toString X ++ "(" ++ toString Y ++ ")"
toString (X ∙ Y) = toString X ++ toString Y
toString B = "B"
toString C = "C"
toString W = "W"
toString K = "K"
toString Q = "Q"
toString Π = "Π"
toString P = "P"
toString ∧ = "∧"

_ : toString (K ∙ Q ∙ (W ∙ C)) ≡ "KQ(WC)"
_ = refl

_ : toString (K ∙ ∧ ∙ (Q ∙ Π) ∙ (W ∙ C)) ≡ "K∧(QΠ)(WC)"
_ = refl

_ : toString (K ∙ ∧ ∙ ((Q ∙ Π) ∙ (W ∙ C))) ≡ "K∧(QΠ(WC))"
_ = refl

_ : toString (K ∙ K ∙ K) ≡ "KKK"
_ = refl

infix 5 _==_

-- Kapitel 1, Abschnitt C, §4 (Symbolische Festsetzungen), Def. 2
_==_ : (X Y : Combinator) → Combinator
X == Y = Q ∙ X ∙ Y

-- Kapitel 1, Abschnitt C, §4 (Symbolische Festsetzungen), Def. 3
I : Combinator
I = W ∙ K
