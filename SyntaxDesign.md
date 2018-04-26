# The premise derivation language (PDL)

## Syntax Design

How to organize the rule and premises in readable way is one challenge when designing such language.

There are several element we want to show

### Inline Rule Style

Assume we have two rules, A: `[[a b] -> c]`, B: `[[c d e] -> f]`.

One way to represent f can derive from rules `A`, `B` with premises `a`, `b`, `d`, `e` is replace c in rule B by rule A.

Then we can get the following expression.

```
[[[[a b] -> c] d e] -> f]
```

In this way, we can clearly know how those premises gradually derive to the final conclusion.

Even this expression is quite intuitive, it has several problems.

1.  Lose the information of imply rule

We don't put our rule label on our code. It may be hard to trace which rules apply here when code grow bigger.

We can try to put those information back.

```
[[[[a b] ->A c] d e] ->B f]
```

2.  Too many brackets

Another problem is there is too many brackes, and we feel a little bit noisy.

Therefore, we may remove brackets wraped the premises input.

```
[[a b ->A c] d e ->B f]
```

Or we can format it like

```
[
  [a b ->A c]
  d
  e
  ->B f
]
```

3.  Duplicated premises or rules

For example, if we have four rules `[[a b] -> i]`, `[[a c] -> j]`, `[[b c] -> k]`, `[[i j k] -> x]`, the whole code will look like following.

```
[
  [a b ->A i]
  [a c ->B j]
  [b c ->C k]
  ->D x
]
```

We can see we need to write `a`, `b`, and `c` several times. If some premises are occur in different rules, then those premises will occupy lots of space.

Even worse, for rules which use the the same conclusion from other rules, we will need to repeat the whole "inherit" line.

For example:

A: `[[a] -> b]`, B: `[[b] -> c]`, C: `[[b] -> d]`, D: `[[c, d] -> e]`.

```
[
  [
    [a ->A b]
    ->B c
  ]
  [
    [a ->A b]
    ->C d
  ]
  ->D e  
]
```

### Rule Flow Style

What if we omit all premises and only keep rule instead?

For getting `f` from two rules A: `[[a b] -> c]`, B: `[[c d e] -> f]`.

```
A -> B
```

It looks quite simple. However, it also has some problems here.

1.  Lack of initial premises information

Firstly, we don't even know what premises supply to A and B initially.

If we take a premise be the conclusion of a rule with empty premises. For example, premise `a` is just a shorthand for rule `[[] -> a]`. In addition, we use `:` to mean rules don't have any premises. Then we can write the above program in this way.

```
:a -> :b -> A -> :d -> :e -> B
```

Now we can see what premises we need to have to apply a rule.

2.  Hard to trace what premises we already have

Because we remove the structure of what premises used by the rule, now we need a context to keep track what premises we have.

For example, for four rules A: `[[a b] -> i]`, B: `[[a c] -> j]`, C: `[[b c] -> k]`, D: `[[i j k] -> x]`

We have the following program for getting conclusion `x`.

```
:a -> :b -> A -> :c -> B -> C -> D
```

Even we know we use :a :b :c to get our conclusion, we certainly need a context, like `PremiseCtx`, to record what premises we currently have. However, I feel it is not a big problem because most languages also keep similar "environment" for variables.

3.  Cannot see the detail of rules.

As above example, we need to lookup rules definition from time to time. Nevertheless, I think we can solve this problem by maintaining another context for storing all rules.

In other words, we will need a syntax for defining all rules in advanced.

For example:

```
A : a b -> i
B : a c -> j
C : b c -> k
D : i j k -> x
:a -> :b -> A -> :c -> B -> C -> D
```

4.  We get a set of premises instead of a conclusion in the end

You can notice that the final result we get will be the context of whole expression, instead of a single conclusion. We may need another syntax for abstract the last conclusion from context.

If we want to say what is our target conclusion, we may need an syntax to indicate it.

For example:

```
x ∈ :a -> :b -> A -> :c -> B -> C -> D
```

#### Assembly code style

We also can represent our logic in assembly code style.

For example:

```
define A be a b to i;
define B be a c to j;
define C be b c to k;
define D be i j k to x;
provide a;
provide b;
get i by A;
provide c;
get j by B;
get k by C;
get x by D;
```

However, this syntax is just sparse format as previous one, they are essentially the same.

### Function Call Style

We can also think applying a rule is similiar to applying arguments to a function in lambda calculus.

For example, for four rules A: `[[a b] -> i]`, B: `[[a c] -> j]`, C: `[[b c] -> k]`, D: `[[i j k] -> x]`. We can have the following program.

```
(D
  (A [a, b])
  (B [b, c])
  (C [a, c])
)
```

Or we can switch position, the premises is a function and rules is a argument.

```
(
  [([a, b] A), ([b, c] B), ([a, c] C)]
  D
)
```

In this style, we will also need rules definition syntax.

```
(A : a b => i)
(B : a c => j)
(C : b c => k)
(D : i j k => x)
```

Even I feel this syntax is pretty good, It has some problems need to be addressed.

1.  Duplicated premises or rules

Just like inline rule style, this type of syntax also has problem when we have repeated rules.

For example, A: `[[a] -> b]`, B: `[[b] -> c]`, C: `[[b] -> d]`, D: `[[c, d] -> e]`.
Then we will have the following program

```
(
  [
    ([([a] A)] B),
    ([([a] A)] C)
  ]
  D
)
```

We could have variable in our syntax to address such duplication, but I feel it is not necessary for now.

## Summary

Through above discussion, we find several ways to design our premise derivation language.

Inline rules style is quite straightforward, but it is verbose. If we want to reuse rules, we will need rule definition and variable syntax.

Next we need to decide we want to use rule flow style, or function call style.

If we use rule flow style, it is concise, but the end result will be a set of premises instead of single conclusion. This is a little bit annoying.

If we use function call style, it is easy to trace while a little bit verbose. However, because we only need to deal with tokenized exp, so it is not a big deal.

In short, I feel function call style is the best design I have for now.
For implement such language, we will need the following syntaxs in our language.

1.  Rule definition.

2.  Rule variable.

3.  Rule application.

4.  Premise / Premises set.
