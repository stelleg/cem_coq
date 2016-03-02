import Development.Shake
import Development.Shake.FilePath

main = shakeArgs shakeOptions $ do  
  want ["compiler.vo"]
  "*.vo" %> \out -> do
    let source = out -<.> ".v"
    deps <- cmd $ "coqdep -I . " ++ source 
    need $ drop 3 $ words $ fromStdout deps
    cmd $ "coqc " ++ source
  phony "clean" $ removeFilesAfter "." ["//*.vo", "//*.glob"]
