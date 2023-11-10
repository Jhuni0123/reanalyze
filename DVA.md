## Dead Value Analysis

The dead value analysis is designed to find as many useless values ans expressions as possible. The reanalyze's DCE analysis also finds some dead declared values and suggests deleting the declaration codes. However there are dead expressions that do not affect the program, although the codes cannot be deleted directly.

A simple example with unused record fields is here:

```rescript
type recordA = {a: int, b: int}
let f = (x, y) => x + y
let r = {a: 10, b: f(20, 30)}
Js.log(r.a)
```

The value of `r.a` is printed to console, but the value of `r.b` is not used here. So the result value of `f(20, 30)` never change the final result of the program, and then the value of `f`, `20`, and `30` are also useless in chain. This example is simple enough to track values with our eyes, but real programs are so large that I introduced syntax-based rules.

Rules are initially quite intuitive. If `r.a` is used, then field `a` in record `r` is used. And If `r` is used, the record `{a: 10, b: f(20, 30)}` is used because the record was binded to name `r` by 'let' syntax. Here, the term 'used' does not mean a boolean in the formal version because values are nested and only partial values can be used. `r` also partially used here (only the `a` field).

With branches and function calls, we cannot identify which branch is taken and which function is called, so control flow analysis should come first. Then rules should also be changed to "may be used".

Then we can collect many rules with the form of "If this value's some parts are used, then that value's some parts may be used" from the entire codes. Now, the form of the rule seems like a dependency between values so we can consider an dependency graph between values with the rules as the edges. If we find a solution that satisfies the dependency graph, the unused portion of each value in that solution, particularly the value that are not entirely used, can be considered as dead.

With those dead values/dead expressions, we may not able to delete them directly. Instead, we may replace the expression with a dummy value or change some structures to remove unintended dead values. For example with the above code, we can replace `f(20, 30)` with a dummy value `0` or we may able to remove the useless `b` field of `recordA` type and these do not change the program's result.

## Benchmarks
I tested this analyzer with two benchmarks: [eko](https://github.com/Zeta611/eko) and [sinsunhi-frontend-mirror](https://github.com/green-labs/sinsunhi-frontend-mirror).

### eko

'eko' is a small rescript react project with about 2000 lines of code. The analyzer runs for a few seconds and reports a good example with some trivial cases.

There is a function called `constructForest` in [JargonPost.res](https://github.com/Zeta611/eko/blob/9287bd7248b89b6bf51da9feb7ac5495bdedc40d/src/JargonPost.res) which returns a tuple.
```rescript
let constructForest = (comments: array<Comment.t>) => {

  ... (omitted)

  (roots, commentNodeTable)
}
```

And there is only one use of this function (line 115). However, the variable `commentNodeTable` was never used here.

```rescript
... 
let (roots, commentNodeTable) = constructForest(comments)
...
```

The analyzer reports that the second field of the tuple is dead in both the function definition and its use.

```
  Warning Dead Expression
  File "/home/Workspaces/eko/src/JargonPost.res", line 28, characters 10-26
  This expression has values that are never used and has no side effect
  <-- line 28
    (roots, commentNodeTable)
            ----------------

  Warning Dead Variable
  File "/home/Workspaces/eko/src/JargonPost.res", line 115, characters 20-36
  This variable has values that are never used
  <-- line 115
          let (roots, commentNodeTable) = constructForest(comments)
                      ----------------
```


### sinsunhi-frontend

This project is a large rescript project with abount 250000 lines of code. It has about 5 milion expressions in the internal representation (typedtree) because the react inflates the number of expressions. The analyzer runs for about 3 minutes in my lcoal computer.

The analyzer reports many unused modules and values, and there is also an example that shows the analyzer follows the control flow well.

```rescript
let upload = (~userId=?, ~kind, ~file, ~onSuccess, ~onFailure, ()) => {

    ...(omitted)

      |> Js.Promise.catch(err => Js.Promise.resolve(err->onFailure))

    ...(omitted)
}
```

Here, the variable `err` is dead because every `onFailure` function that passed to `upload` function does not use `err`.


#### Possible improvements with relay
In fact, just this may not very useful in real-world scenarios. Therefore, I suggest some possible improvements with the rescript-relay project. The project makes many queries using relay, and the analyzer can statically analyze which parts are used in the query data. If we know that some fields are never used in a query, there is no need to requst that data from the server. Consequently, we can simply remove that fields from the query description.
