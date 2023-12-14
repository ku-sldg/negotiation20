import System.IO     
    
main = do     
    withFile "manifest.hs" ReadMode (\handle -> do  
        contents <- hGetContents handle     
        putStr contents)  