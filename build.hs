#!/usr/bin/env runhaskell 

import Development.Shake
import Development.Shake.FilePath

main = shakeArgs shakeOptions $ do  
  want ["compiler.vo"]
  "*.vo" %> \out -> do
    let source = out -<.> ".v"
    deps <- cmd $ "coqdep " ++ source 
    need $ drop 3 $ words $ head $ lines $ fromStdout deps
    cmd $ "coqc " ++ source
  "*.vio" %> \out -> do
    let source = out -<.> ".v"
    deps <- cmd $ "coqdep " ++ source 
    need $ drop 3 $ words $ (!!1) $ lines $ fromStdout deps
    cmd $ "coqc -quick " ++ source
  phony "clean" $ removeFilesAfter "." ["//*.vo", "//*.glob", "//*.vio"]
