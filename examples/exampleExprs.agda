module examples.exampleExprs where
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_,_)
open import TransitionSystems using () renaming (TransitionSystem to T)
open import Data.Sum using (inj₁; inj₂)
import Bims
import examples.bims

-- Section Start Page 38. This label is place 1
-- page 28 is also done in TransitionSystems.agda

open Bims.Aexp₁-smallstep-semantic hiding (_⇒⟨_⟩_; _⇒*_; _⇒∘⇒_; x⇒x)
open T (examples.bims.Aexp₁-small-step-semantic.Aexp₁ssSemantic)

exampleAexp₂1 : inj₁ (inj₁ ((inj₁ (N (+ 3))) + (inj₁ (N (+ 12)))) * inj₁ (inj₁ (N + 4) * inj₁ ((inj₁ (N + 5)) * (inj₁ (N + 9)))))
         ⇒⟨ 3 ⟩ inj₁ (inj₂ (+ 15)                                 * inj₁ (inj₁ (N + 4) * (inj₁ ((inj₁ (N + 5)) * (inj₁ (N + 9))))))
exampleAexp₂1 = (MULT-1ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ refl)
            ⇒∘⇒ (MULT-1ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ refl)
            ⇒∘⇒ (MULT-1ₛₛₛ PLUS-3ₛₛₛ)
            ⇒∘⇒ x⇒x

-- Problem 3.12
exampleAexp₂2 : inj₁ (inj₁(inj₁(N + 2) + inj₁(N + 3))* inj₁(inj₁(N + 4) + inj₁(N + 9))) ⇒* inj₂ (+ 65)
exampleAexp₂2 = 7 , (MULT-1ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ refl)
                ⇒∘⇒ (MULT-1ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ refl)
                ⇒∘⇒ (MULT-1ₛₛₛ PLUS-3ₛₛₛ)
                ⇒∘⇒ (MULT-2ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ refl)
                ⇒∘⇒ (MULT-2ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ refl)
                ⇒∘⇒ (MULT-2ₛₛₛ PLUS-3ₛₛₛ)
                ⇒∘⇒ (MULT-3ₛₛₛ refl)
                ⇒∘⇒ x⇒x

-- Section End Page 38
