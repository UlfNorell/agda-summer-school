
## Programming with Dependent Types

### Getting Started

#### Prerequisites
- Haskell Platform
- Emacs
- git

#### Installing Agda
- cabal update
- cabal install Agda
- agda-mode setup

#### Getting the libraries
- git clone https://github.com/UlfNorell/agda-prelude
- git clone https://github.com/UlfNorell/agda-summer-school
- cd agda-prelude/agda-ffi
- cabal install

#### Set up Emacs paths
- M-x agda2-mode
- M-x customize-group agda2
- Add path to agda-prelude/src to Include Dirs (make sure to **NOT** remove "." from the list)

#### Check that it works
- Open agda-summer-school/exercises/Lambda.agda in Emacs
- Hit `C-c C-l` to type check
- Hit `C-c C-x C-c` to compile
- You should now have an executable Lambda in exercises/
- Run `./Lambda example.lam`. This should print a desugared lambda term and the
  result of running it through the SECD machine.

### Exercises

#### Resources

- [Agda Wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php)
- [Mailing list](https://lists.chalmers.se/mailman/listinfo/agda)
- [IRC channel #agda on freenode](http://webchat.freenode.net)
- `doc/AgdaCheatSheet.agda` contains a number of small examples showing some of the features of Agda.
- `doc/EmacsCheatSheet.html` lists the most commonly used Emacs mode commands.
- Browse the library. Use `M-.` or `middle mouse` to jump to the definitions of library functions.

#### Day 1

- `exercises/Lists.agda`
- Bonus: `exercises/Grep.agda`

#### Day 2

- `exercises/Term.agda`
- `exercises/Term/Eval.agda`
- `exercises/TypeCheck.agda`

#### Day 3

- Copy `exercises/SECD/Unchecked.agda` to `exercises/SECD/StackSafe.agda` and add types to ensure stack safety.
- Copy your stack safe SECD machine to `exercises/SECD/TypeSafe.agda` and add type safety (running well-typed terms).
- Change the compiler in `exercises/SECD/Compiled.agda` to compile well-typed terms and adapt your type safe SECD machine to run the compiled terms.
- Bonus (hard): Track semantics in the types. In the end you should have a run function that is guaranteed to compute a value corresponding to `eval t` for an input term `t`.

#### Day 4

- Add more features to the lambda calculus (natrec, booleans, ...).
- Invent your own exercises.
