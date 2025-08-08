# Total Type Classes

## Structure

Here is a brief overview of the structure of the code as it relates to the paper.
* `src/TotalClassPlugin.hs` defines the user-visible API of the plugin, primarily the `TotalConstraint` class which is used to declare total constraints
* `src/TotalClassPlugin/Solver.hs` is the entry point for the plugin, which solves constraints by invoking the checker or inserting placeholders for the rewriter.
* `src/TotalClassPlugin/Checker` contains the code for the totality checker (section 3 of the paper). The checks themselves are in `Check.hs`, using the custom `CM` monad to track state, and in particular to record which checks failed, which is used for testing/debugging. `Errors.hs` reports check failures using GHC's error reporting system. `TH.hs` contains the Template Haskell code for the exhaustiveness check (section 3.2)
* `src/TotalClassPlugin/Rewriter` implements the program rewriting from section 4 of the paper. `Placeholder.hs` produces fake placeholder evidence terms that can later be identified and removed (section 4.3). `Bind.hs` contains the pass which turns placeholders into new elements of type signatures, while `Call.hs` is the second pass which emits new constraints from function calls. `Capture.hs` contains utilities for capturing newly emitted constraints and attaching them to the AST; this is used in both passes. `Validate.hs` includes steps to run after a `Bind` pass to ensure no placeholders remain.
* `test/` contains various tests and demonstrations. `Demo.hs` provides a concise example matching the one in the paper. `Checker.hs` shows how various totality checks fail and succeed as expected. `Rewriter.hs` contains many different functions that the plugin rewrites correctly. `Main.hs` calls all the rewritten functions to show that they behave correctly at runtime.

## Usage

Refer to GHC documentation (https://downloads.haskell.org/ghc/9.12.2/docs/users_guide/extending_ghc.html#using-compiler-plugins) for instructions on how to use the plugin. To see it in action, try loading the test modules in `cabal repl` and inspecting the types of the rewritten functions.
