# redder

Experimental dead value / dead code analyzer for ReScript projects.

## Dead Value Analysis

The dead value analysis finds expressions and variables that do not affect the program's execution result.
An expression can affect the program's result in two ways: through its result value and via a side effect. So, if the expression's result value never affect the program result and the expression has no side effect, the expression is considered a dead expression. With this definition, it can find dead field values in a partialy dead record or tuple.

The analyzer infers whether the value of each expression is dead by applying syntax-based rules based on the result of Control Flow Analysis. Please check out [DVA.md](DVA.md) for more informations.

## Build & Run

```sh
opam install dune
npm run build
# _build/default/src/Redder.exe
```

Build the ReScript project before running the analyzer.

```sh
npm run build # or whatever command to build the project
/path/to/redder.exe -dva
```

## License

This project has started as a fork of [rescript-association/reanalyze](https://github.com/rescript-association/reanalyze). Both the original reanalyze code and this analyzer are licensed under the [MIT License](LICENSE).
