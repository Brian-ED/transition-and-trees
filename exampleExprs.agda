module exampleExprs where
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Product using (_,_)
open import TransitionSystems using (TransitionSystem)
import Bims
import bims

-- Section Start Page 38. This label is place 1
-- page 28 is also done in TransitionSystems.agda

open Bims.Aexp₁-smallstep-semantic
open TransitionSystem (bims.Aexp₁-small-step-semantic.Aexp₁ssSemantic)

exampleAexp₂1 : (((N + 3) + (N + 12)) * ((N + 4)*((N + 5)*(N + 8))))
         ⇒⟨ 3 ⟩ ((++ + 15)            * ((N + 4)*((N + 5)*(N + 8))))
exampleAexp₂1 = MULT-1ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ refl
       step-suc MULT-1ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ refl
       step-suc MULT-1ₛₛₛ PLUS-3ₛₛₛ
       step-suc step-zero

-- Problem 3.12
exampleAexp₂2 : (((N + 2) + (N + 3))*((N + 4) + (N + 9))) ⇒* (++ + 65)
exampleAexp₂2 = 7 , MULT-1ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ refl
           step-suc MULT-1ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ refl
           step-suc MULT-1ₛₛₛ PLUS-3ₛₛₛ
           step-suc MULT-2ₛₛₛ PLUS-1ₛₛₛ NUMₛₛₛ refl
           step-suc MULT-2ₛₛₛ PLUS-2ₛₛₛ NUMₛₛₛ refl
           step-suc MULT-2ₛₛₛ PLUS-3ₛₛₛ
           step-suc MULT-3ₛₛₛ
           step-suc step-zero
-- Section End Page 38
