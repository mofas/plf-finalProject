# Rule Derivation Language

You can find my slide here.

https://docs.google.com/presentation/d/1tt-JI24wW9j9pE_WUAUVhfyT2Pxlel-8WlimB4pv7l0/edit#slide=id.p

## Syntax

For simplicity, I don't define the rules in my language, all rules are predefiend and put in the context in advanced.

```agda
data Rule : Set where
  _⊢_∷_ : PremiseSet → String → String → Rule

-- D : [i j k -> x]
ruleD : Rule
ruleD = ( "k" , ( "j" , ("i" , □))) ⊢ "D" ∷ "x"
```

Expression is composed by two data type, `PremiseExp` and `Exp`.

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

For all valid expressions, it has only one conclusion to return in the end. Therefore, it has only one type. However, we can also take the type system as a static check, to rule out some "invalid" expression.

In my type system, I have only one type that call "valid" in type system. An expression need to satisify certain conditions to meet the "valid" type. For example, the number of the premises in "App" expression should be larger than that required by the rule.

## Operational Semantic

I do the big step and small step operational semantic for this language.

In big step, I implement an exception. If there is invalid rule application, then exception will arise.

In small step evaluation, I only implemented valid path, because implemented exception is quite tedious. Just like we do in the class, we need to bubble up the exception to the surface by adding new state transition for all existing cases.

Both implementation is the same, and you can the example of reduction in the slides I provide at beginning.

The whole implementation is at [PDL.agda](./PDL.agda)

## Extend language with properities

Now, I finish our language but it is not so interesting, so I try to add more thing into my language.

There are many other languages have similar derivation system like I did here, and they are more sophisticated and powerful. Prolog is a good example, it is a logic language which have a rule and unification system to solve logic complex relation.

For example, Prolog has the following syntax.

```
mortal(X) :- human(X)
```

It means "For a given X, X is mortal if X is human." In our language, we don't have universial variables to achieve this. It may be interesting if we could extend our language like this.

```
Rule mortal : ([x] -> ("mortal" x))
Rule human : ([x] -> ("human" x))
Rule A:  ([("human" x)] -> ("mortal" x))
```

In rule human: if you give me a premise x, then I will return a conclusion x is human.
In rule a: if you give me a premise x is human, then I will return a conclusion x is mortal.

That is to say, now conclusions or premises can have properties attached on them. Let us see another complex example.

```
Rule parent : ([x y] -> ("parent" x y))
Rule male : ([z] -> ("male" z))
Rule B:  ([("parent" x y) ("male" x)] -> ("father" x y))
```

Now you can see the property "parent" could have two premises inside.
It says :

In rule parent: if you give me premises x and y, then I will return a conclusion x is the parent of y.
In rule male: if you give me a premise z, then I will return a conclusion z is male.
In rule B: if your give me premise that "x is the parent of y" and "x is a male", then I will return a conclusion that "x is the father of y."

The whole implementation is at [PDL2.agda](./PDL2.agda)
