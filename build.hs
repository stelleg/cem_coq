import Development.Shake
import Development.Shake.Util
import Development.Shake.FilePath
import Data.Maybe

main = shakeArgs shakeOptions $ do  
  want ["compiler.vo"]
  "*.vo" %> \out -> do
    let source = out -<.> ".v"
    deps <- cmd $ "coqdep -I . " ++ source 
    need $ fromMaybe [] $ lookup out $ parseMakefile $ fromStdout deps
    cmd $ "coqc " ++ source
  phony "clean" $ removeFilesAfter "." ["//*.vo", "//*.glob"]
