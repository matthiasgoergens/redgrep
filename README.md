redgrep
=======

Re-implementing redgrep in Haskell.  With an Applicative interface.

This is a regular expression matcher that also support intersection and complement
in addition to the traditional regular expression operations.

In future, like redgrep, I plan to support compilation to llvm.  The matching functionality
right now, is only a proof of concept, and doesn't make any performance claims.


See https://github.com/google/redgrep for the original.
