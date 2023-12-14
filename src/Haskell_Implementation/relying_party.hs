main = do
  putStrLn "The relying party is asking target for a protocol." 
  protocol <- getLine
  if null protocol
    then putStrLn ("No protocol found.")
    else putStrLn ("The target has selected the following protocol(s): " ++ protocol)

