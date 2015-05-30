redgrep
=======

Re-implementing redgrep in Haskell.  With an Applicative interface.  (Or at least an non-monadic one.)

This is a regular expression matcher that also support intersection and complement
in addition to the traditional regular expression operations.

It is also a proper parser, so perhaps I will add sed-like functionality.

In future, like redgrep, I plan to support compilation to llvm.  The matching functionality
right now, is only a proof of concept, and doesn't make any performance claims.

See https://github.com/google/redgrep for the original.
