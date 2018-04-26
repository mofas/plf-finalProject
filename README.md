# Rule Derivation Language

You can find my slide here.

https://docs.google.com/presentation/d/1tt-JI24wW9j9pE_WUAUVhfyT2Pxlel-8WlimB4pv7l0/edit#slide=id.p

## Syntax

For simplicity, we don't define the rules in our language, all rules are predefiend and put in the context in advanced.

```agda
data Rule : Set where
  _⊢_∷_ : PremiseSet → String → String → Rule

-- D : [i j k -> x]
ruleD : Rule
ruleD = ( "k" , ( "j" , ("i" , □))) ⊢ "D" ∷ "x"
```

Expression is composed by two data type, PremiseExp and Exp.

```agda
data Exp : Set

data PremiseExp : Set where
  □   : PremiseExp
  _,_ : (String ⊎ Exp) → PremiseExp → PremiseExp

data Exp where
  App      : PremiseExp → RuleVar → Exp

exp1 : Exp
exp1 = (App
        (inj₁ "c" ,
        (inj₂ (App
                (inj₁ "b" ,
                (inj₁ "a" ,
                □))
              (Var "A")) ,
          □))
        (Var "D"))
```

## Type System

## Operational Semantic

## Search
