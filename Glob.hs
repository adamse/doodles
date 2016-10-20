-- |

module Glob where


match
  :: String -- ^ pattern
  -> String -- ^ string
  -> Bool
match [] [] = True
match ('?':pat) (_:cs) = match pat cs
match ('*':pat) (_:cs) =
  match pat cs || match ('*' : pat) cs
match (p:pat) (c:cs)
  | p == c = match pat cs
  | otherwise = False
match _ _ = False

examples = ["/Dir/Page", "/Dir/*", "*/Page"]

test = map (flip match "/Dir/Page") examples
