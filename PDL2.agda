module PDL2 where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
  
open import Data.String
open import Data.Sum
open import Data.List hiding (_++_; drop)
open import Data.Bool.Base using (Bool; false; true; _∧_; if_then_else_)
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- for simplicity, we only define unary and binary relations 
data Relation : Set where
  Unary  : String → Relation
  Binary : String → String → Relation

data Property : Set where
  Prop : String → Property
  
data Premise : Set where
  S : String → Premise
  P : Property → Relation → Premise  

data PremiseSet : Set where
  □   : PremiseSet
  _,_ : Premise → PremiseSet → PremiseSet


data RuleId : Set where
  Id     : String → RuleId

data Rule : Set where
  _⊢_∷_ : PremiseSet → RuleId → Premise → Rule

data RuleCtx : Set where
  □ : RuleCtx
  _,_ : Rule → RuleCtx → RuleCtx


ruleParent : Rule
ruleParent = ((S "y") , ((S "x") , □)) ⊢ (Id "ruleParent") ∷ (P (Prop "parent") (Binary "x" "y"))

ruleMale : Rule
ruleMale = ((S "x") , □) ⊢ (Id "ruleMale") ∷ (P (Prop "male") (Unary "x"))

ruleFather : Rule
ruleFather = ((P (Prop "male") (Unary "x")) , ((P (Prop "parent") (Binary "x" "y")) , □)) ⊢ (Id "ruleFather") ∷ (P (Prop "father") (Binary "x" "y"))

ruleGrandparent : Rule
ruleGrandparent = ((P (Prop "parent") (Binary "y" "z")) , ((P (Prop "parent") (Binary "x" "y")) , □)) ⊢ (Id "ruleGrandparent") ∷ (P (Prop "grandparent") (Binary "x" "z"))


-- Example: ruleCtx
ctx1 : RuleCtx 
ctx1 = (ruleGrandparent , (ruleFather , (ruleMale , (ruleParent , □))))


data Exp : Set

data PremiseExp : Set where
  □   : PremiseExp
  _,_ : (String ⊎ Exp) → PremiseExp → PremiseExp

data Exp where
  App      : PremiseExp → RuleId → Exp
  Check    : PremiseExp → Exp → Exp


-- (
--   [
--     ["Vader" "Luke"] -> parent("Vader", "Luke")
--     ["Vader"] -> male("Vader")
--   ]
--   ?-
--   father("Vader", "Luke")
-- )

-- fact 1
VaderIsLukeParent : Exp
VaderIsLukeParent = (App (( inj₁ "Luke" , ( inj₁ "Vader" , □))) (Id "ruleParent"))

-- fact 2
VaderIsMale : Exp
VaderIsMale = (App (( inj₁ "Vader" , □)) (Id "ruleMale"))

-- assumption
VaderIsLukeFather : Exp
VaderIsLukeFather = (App (( inj₁ "Luke" , ( inj₁ "Vader" , □))) (Id "ruleFather"))


-- This expression is used to check the facts we have can infer our assumption 
checkVaderIsLukeFather : Exp
checkVaderIsLukeFather = (Check (inj₂ VaderIsLukeParent , (inj₂ VaderIsMale , □)) VaderIsLukeFather)

-- (
--   [
--     ["John", "Mose"] -> parent("John", "Mose")
--     ["Mose", "Inca"] -> parent("Mose", "Inca")
--   ]
--   ->
--   grandparent("Ada", "Inca")
-- )


JohnIsMoseParent : Exp
JohnIsMoseParent = (App (( inj₁ "Mose" , ( inj₁ "John" , □))) (Id "ruleParent"))

MoseIsIncaParent : Exp
MoseIsIncaParent = (App (( inj₁ "John" , ( inj₁ "Inca" , □))) (Id "ruleParent"))

-- -- This one is not correct
-- JohnIsAdaGrandparent : Exp
-- JohnIsAdaGrandparent = (App (inj₂ MoseIsIncaParent , (inj₂ JohnIsMoseParent , □)) (Id "ruleGrandparent"))

-- -- This one is correct
-- JohnIsIncaGrandparent : Exp
-- JohnIsIncaGrandparent = (App (inj₂ MoseIsIncaParent , (inj₂ JohnIsMoseParent , □)) (Id "ruleGrandparent")) 
