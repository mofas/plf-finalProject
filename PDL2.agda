module PDL2 where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
  
open import Data.String
open import Data.Sum
open import Data.List hiding (_++_; drop)
open import Data.Bool.Base using (Bool; false; true; _∧_; _∨_; if_then_else_)
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

data ParamSet : Set where
  □   : ParamSet
  _,_ : String → ParamSet → ParamSet
  
data Fact : Set where  
  App      : ParamSet → RuleId → Fact

data FactSet : Set where
  □   : FactSet
  _,_ : Fact → FactSet → FactSet

data Assumption : Set where
   Asump   : Premise → Assumption 

data Exp : Set where
  Check    : FactSet → Assumption → Exp

data VarMapping : Set where
  □   : VarMapping
  _>_,_ : String → String → VarMapping → VarMapping

data NotFind : Set where
  none : NotFind

-- Check Mechanism

lookup : RuleCtx → Premise → (Rule ⊎ NotFind)
lookup □ premise = inj₂ none
lookup ((require ⊢ id ∷ S x) , ctx) (S y) = if x == y then inj₁ (require ⊢ id ∷ S x) else (lookup ctx (S y))
lookup ((require ⊢ id ∷ P (Prop pr1) x) , ctx) (P (Prop pr2) y) =  if pr1 == pr2 then inj₁ (require ⊢ id ∷ P (Prop pr1) x) else (lookup ctx (P (Prop pr2) y)) 
lookup (_ , ctx) target = lookup ctx target

GetVarMapping : Relation → Relation → VarMapping 
GetVarMapping (Unary x) (Unary y) =  x > y , □
GetVarMapping (Unary _) (Binary _ _) = □
GetVarMapping (Binary _ _) (Unary _) = □
GetVarMapping (Binary x₁ x₂) (Binary y₁ y₂) = ( x₂ > y₂ , (x₁ > y₁ , □))

SubstituteVariable : String → VarMapping → (String ⊎ NotFind)
SubstituteVariable s □ = inj₂ none
SubstituteVariable x (x' > y , map) = if x == x' then inj₁ y else SubstituteVariable x map

SubstituteRelation : Relation → VarMapping → (Relation ⊎ NotFind)
SubstituteRelation (Unary s) map with (SubstituteVariable s map)
... | inj₁ y  = inj₁ (Unary y)
... | inj₂ x  = inj₂ x
SubstituteRelation (Binary s1 s2) map with (SubstituteVariable s1 map) | (SubstituteVariable s2 map)
... | inj₁ y1 | inj₁ y2 = inj₁ (Binary y1 y2)
... | _       | _    = inj₂ none

SubstitutePremise : Premise → VarMapping → (Premise ⊎ NotFind)
SubstitutePremise _ □ = inj₂ none
SubstitutePremise (S x) (x' > y , map) = if x == x' then inj₁ (S y) else (SubstitutePremise (S x) map)
SubstitutePremise (P prop relation) map with (SubstituteRelation relation map)
... | inj₁ relation' = inj₁ (P prop relation')
... | inj₂ x         = inj₂ x

SubstitutePremiseSet : PremiseSet → VarMapping → (PremiseSet ⊎ NotFind)
SubstitutePremiseSet □ _ = inj₁ □
SubstitutePremiseSet (premise , set) map with (SubstitutePremise premise map) | (SubstitutePremiseSet set map)
... | inj₁ premise' | inj₁ set' = inj₁ (premise' , set')
... | inj₂ x        | _         = inj₂ x
... | _             | inj₂ x    = inj₂ x


Derive : (Rule ⊎ NotFind) → Premise → (PremiseSet ⊎ NotFind)
Derive (inj₂ none) premise = inj₂ none
-- we simplify problem. If we find our conclusion is a simple conclusion, 
-- then we just say nothing is required.
Derive (inj₁ (premises ⊢ _ ∷ (S x))) (S y) = inj₁ □
Derive (inj₁ (premises ⊢ _ ∷ (P pr1 re1))) (P pr2 re2) =
  let map = (GetVarMapping re1 re2) in (SubstitutePremiseSet premises map)      
Derive _ _ = inj₂ none

_≡Re_ : Relation → Relation → Bool
Unary x ≡Re Unary y =  if x == y then true else false
Binary x1 y1 ≡Re Binary x2 y2 = if (x1 == x2) ∧ (y1 == y2) then true else false  
_ ≡Re _ = false

-- the first premise is from fact, the second is from assumption 
CheckFact : Premise → Premise → Bool
CheckFact (S x) (S y) = if x == y then true else false
CheckFact (P (Prop p1) re1) (P (Prop p2) re2) = if (p1 == p2) ∧ (re1 ≡Re re2) then true else false 
CheckFact _ _ = false

isValidPremise : (PremiseSet ⊎ NotFind) → Premise → Bool
isValidPremise (inj₂ _) _ = false
isValidPremise (inj₁ □) p = false
isValidPremise (inj₁ (fact , factSet)) p = (CheckFact fact p) ∨ (isValidPremise (inj₁ factSet) p)


CheckRequirePremiseSet : (PremiseSet ⊎ NotFind) → (PremiseSet ⊎ NotFind) → Bool
CheckRequirePremiseSet factSet (inj₁ □) = true
CheckRequirePremiseSet factSet (inj₁ (premise , set)) with isValidPremise factSet premise | CheckRequirePremiseSet factSet (inj₁ set)
... | true   |  true       = true
... | _      | _           = false
CheckRequirePremiseSet _ _ = false


InstantiateRelation : ParamSet → Relation → (Relation ⊎ NotFind)
InstantiateRelation (x , param) (Unary _) = inj₁ (Unary x)
InstantiateRelation (x , (y , param)) (Binary _ _) = inj₁ (Binary y x) 
InstantiateRelation _ _ = inj₂ none


-- ParamSet : (("Luke" , ("Vader" , □)))
-- (P (Prop "parent") (Binary "x" "y"))
InstantiateFact : ParamSet → Premise → (Premise ⊎ NotFind)
InstantiateFact □ _ = inj₂ none
InstantiateFact (x , param) (S _) = inj₁ (S x)
InstantiateFact param (P prop relation) with (InstantiateRelation param relation)
... | inj₁ relation' = inj₁ (P prop relation')
... | _ = inj₂ none


ApplyFactRule : Fact → RuleCtx → (Premise ⊎ NotFind)
ApplyFactRule (App x x₁) □ = inj₂ none
ApplyFactRule (App param (Id id)) ((require ⊢ (Id id') ∷ conclusion) , ctx) = if id == id' then (InstantiateFact param conclusion) else (ApplyFactRule (App param (Id id)) ctx)


ApplyFactSetRule : FactSet → RuleCtx → (PremiseSet ⊎ NotFind)
ApplyFactSetRule factSet □ = inj₂ none
ApplyFactSetRule □ _   =  inj₁ □
ApplyFactSetRule (fact , factSet) ctx with (ApplyFactRule fact ctx) | (ApplyFactSetRule factSet ctx)
... | inj₁ premise | inj₁ premiseSet = inj₁ (premise , premiseSet) 
... | _            |  _              = inj₂ none


EvalExp : Exp → RuleCtx → Bool
EvalExp (Check factSet (Asump premise)) ctx = 
  let rule = (lookup ctx premise) in
    let requirePremiseSet = (Derive rule premise) in
      CheckRequirePremiseSet (ApplyFactSetRule factSet ctx) requirePremiseSet
 


-- Example

-- Rule
ruleParent : Rule
ruleParent = ((S "y") , ((S "x") , □)) ⊢ (Id "ruleParent") ∷ (P (Prop "parent") (Binary "x" "y"))

ruleMale : Rule
ruleMale = ((S "x") , □) ⊢ (Id "ruleMale") ∷ (P (Prop "male") (Unary "x"))


ruleFather : Rule
ruleFather = ((P (Prop "male") (Unary "x")) , ((P (Prop "parent") (Binary "x" "y")) , □)) ⊢ (Id "ruleFather") ∷ (P (Prop "father") (Binary "x" "y"))

ruleGrandparent : Rule
ruleGrandparent = ((P (Prop "parent") (Binary "y" "z")) , ((P (Prop "parent") (Binary "x" "y")) , □)) ⊢ (Id "ruleGrandparent") ∷ (P (Prop "grandparent") (Binary "x" "z"))


-- (
--   [
--     ["Vader" "Luke"] -> parent("Vader", "Luke")
--     ["Vader"] -> male("Vader")
--   ]
--   ?-
--   father("Vader", "Luke")
-- )


-- RuleCtx
ctx1 : RuleCtx 
ctx1 = (ruleGrandparent , (ruleFather , (ruleMale , (ruleParent , □))))

-- Lookup Rule by Prop
lookupEx1 : (Rule ⊎ NotFind)
lookupEx1 = lookup ctx1 (P (Prop "female") (Unary "y"))

lookupEx2 : (Rule ⊎ NotFind)
lookupEx2 = lookup ctx1 (P (Prop "father") (Binary "Vader" "Luke"))

lookupEx3 : (Rule ⊎ NotFind)
lookupEx3 = lookup ctx1 (P (Prop "grandparent") (Binary "John" "Inca"))

-- Create var mapping
-- Map x > Vadar , y > Luke
varMapping1 : VarMapping
varMapping1 = GetVarMapping (Binary "x" "y") (Binary "Vader" "Luke")


-- ((P (Prop "male") (Unary "Vader")) , ((P (Prop "parent") (Binary "Vader" "Luke")) , □))
exSubPreSet : (PremiseSet ⊎ NotFind)
exSubPreSet = SubstitutePremiseSet ((P (Prop "male") (Unary "x")) , ((P (Prop "parent") (Binary "x" "y")) , □)) varMapping1

-- fact 1
VaderIsLukeParent : Fact
VaderIsLukeParent = (App (("Luke" , ("Vader" , □))) (Id "ruleParent"))

-- fact 2
VaderIsMale : Fact
VaderIsMale = (App (("Vader" , □)) (Id "ruleMale"))

-- assumption
VaderIsLukeFather : Assumption
VaderIsLukeFather = (Asump (P (Prop "father") (Binary "Vader" "Luke")))


-- This expression is used to check whether the facts we provided can infer the assumption 
checkVaderIsLukeFather : Exp
checkVaderIsLukeFather = (Check (VaderIsLukeParent , (VaderIsMale , □)) VaderIsLukeFather)


-- InstantiateFact 
instEx1 : (Relation ⊎ NotFind)
instEx1 = InstantiateRelation (("Luke" , ("Vader" , □))) (Binary "x" "y")

-- instinate fact inj₁ (P (Prop "parent") (Binary "Vader" "Luke"))
applyRule1 : (Premise ⊎ NotFind)
applyRule1 = ApplyFactRule VaderIsLukeParent ctx1

-- instinate fact (P (Prop "male") (Unary "Vader"))
applyRule2 : (Premise ⊎ NotFind)
applyRule2 = ApplyFactRule VaderIsMale ctx1


-- inj₁ (P (Prop "parent") (Binary "Vader" "Luke") , (P (Prop "male") (Unary "Vader") , □))
applyRuleSet1 : (PremiseSet ⊎ NotFind)
applyRuleSet1 = (ApplyFactSetRule (VaderIsLukeParent , (VaderIsMale , □)) ctx1)


--
-- Eval Example
--


-- true!
result1 : Bool
result1 = EvalExp checkVaderIsLukeFather ctx1


-- If we don't give enough facts, then it will become false
result2 : Bool
result2 = EvalExp (Check (VaderIsLukeParent , □) (Asump (P (Prop "father") (Binary "Vader" "Luke")))) ctx1


-- How about say "Yoda is the father of Luke", the answer is false
result3 : Bool
result3 = EvalExp (Check (VaderIsLukeParent , (VaderIsMale , □)) (Asump (P (Prop "father") (Binary "Yoda" "Luke")))) ctx1


-- (
--   [
--     ["John", "Mose"] -> parent("John", "Mose")
--     ["Mose", "Inca"] -> parent("Mose", "Inca")
--   ]
--   ?-
--   grandparent("Ada", "Inca")
-- )


JohnIsMoseParent : Fact
JohnIsMoseParent = (App (("Mose" , ("John" , □))) (Id "ruleParent"))

MoseIsIncaParent : Fact
MoseIsIncaParent = (App (("John" , ("Inca" , □))) (Id "ruleParent"))

JohnIsAdaGrandparent : Assumption
JohnIsAdaGrandparent = (Asump (P (Prop "grandparent") (Binary "John" "Ada")))

JohnIsIncaGrandparent : Assumption
JohnIsIncaGrandparent = (Asump (P (Prop "grandparent") (Binary "John" "Inca")))


-- This one is false 
checkWithoutFact : Exp
checkWithoutFact = (Check □ JohnIsAdaGrandparent)

-- This one is false 
checkJohnIsAdaGrandparent : Exp
checkJohnIsAdaGrandparent = (Check (MoseIsIncaParent , (JohnIsMoseParent , □)) JohnIsAdaGrandparent)

-- This one is true
checkJohnIsIncaGrandparent : Exp
checkJohnIsIncaGrandparent = (Check (MoseIsIncaParent , (JohnIsMoseParent , □)) JohnIsIncaGrandparent)

-- I find this part we still need the unification to solve it ...
-- TODO ...



