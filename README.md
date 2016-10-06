# Verifiably Lazy : A Verified Compiler for Call-By-Need.

# Building / Proof Checking

Requirements: 
- `coqc` and `coqdep` (tested with 8.4pl6)
- `runhaskell` and Shake

To Build: `./build.hs` (requires runhaskell and Shake, the Haskell build system) 

Notes: 
We use the convention that filenames without underscores correspond to semantics
while relations between semantics use underscores, e.g.  `c1_c2.v` contains the
relations between `c1` and `c2`. 

