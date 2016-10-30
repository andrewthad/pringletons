module Data.Case.Enumerate
  ( enumerateConstructors
  ) where

import Language.Haskell.TH
import Control.Monad

{-| This will create a pattern match on the first argument
    that splices in the third argument for each pattern.
    Example:

 > data Color = Red | Blue | Green deriving Show
 > myFunc :: Color -> String
 > myFunc c = $(enumerateConstructors 'c ''Color =<< [|show c|])

   I should fix this function to actually make it work that
   way. It actually uses the singletonized data type instead.
-}

enumerateConstructors :: Name -> Name -> Exp -> Q Exp
enumerateConstructors vname name expr = do
  TyConI (DataD _ _ _ _ ctors _) <- reify name
  matches <- forM ctors $ \(NormalC cname args) -> case args of
    [] -> return $ Match (ConP (sketchyNameSingletonize cname) []) (NormalB expr) []
    _ -> fail "constConstructors2: empty data constructor required"
  return $ CaseE (VarE vname) matches

sketchyNameSingletonize :: Name -> Name
sketchyNameSingletonize = id
  . mkName . ('S':) . reverse
  . takeWhile (/= '.') . reverse . show

