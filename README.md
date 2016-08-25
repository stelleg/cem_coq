% Verifiably Lazy : A Verified Compiler for Call-By-Need.

# Building / Proof Checking

Requirements: 
- `coqc` and `coqdep` (tested with 8.4)
- `runhaskell` and Shake

To Build: `./build.hs` (requires runhaskell and Shake, the Haskell build system) 

Notes: 
We use the convention that filenames correspond to that datatype and theorems
, supporting datatypes, transitions for those datatypes, while filenames with
underscores, e.g.  `c1_c2.v` represents the connections between `c1` and
`c2`. 

