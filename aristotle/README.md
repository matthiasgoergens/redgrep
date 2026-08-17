Context: redgrep is a Haskell extended-regex library (union, concatenation,
star, intersection, complement) matched by Brzozowski derivatives, with two
extra closure operations: inverse string homomorphism and reversal (plus
left/right quotient by a string). Statements.lean states the language-level
laws that the engine's per-constructor derivative rules implement. The task
is to prove every theorem (replace each `sorry`), without new axioms, and
without weakening any statement. Adapting list-API names (flatMap/bind,
flatten/join) to the current Mathlib is fine as long as meaning is
preserved.
