import Text.ParserCombinators.ReadP 
import Control.Monad.State (State)
import Control.Monad
import Control.Applicative ((<|>))
import Data.Maybe
import Data.Char
import Data.List

import qualified Control.Monad.State as S
import qualified Data.Map.Lazy as M

type Var = String
type Env = (M.Map Int Expr, Int, M.Map Var Expr)

data Expr
  = Var Var
  | App Expr Expr
  | Abs Var Expr
  | Ptr Int
  | Let Var Expr (Maybe Expr)
  deriving Eq

instance Show Expr where
  show (Var x) = x
  show a@(App _ _) = intercalate " " $ map br (collect a)
    where br (Var v) = v
          br x = "(" ++ show x ++ ")"
          collect (App x y) = collect x ++ [y]
          collect x = [x]
  show (Abs x e) = "λ" ++ x ++ "." ++ show e
  show (Ptr n) = "&" ++ show n
  show (Let x e Nothing) = "let " ++ x ++ " = " ++ show e
  show (Let x e (Just b)) = "let " ++ x ++ " = " ++ show e ++ " in " ++ show b

lam :: String -> Expr
lam = fst . last . readP_to_S (skipSpaces *> expr)

expr :: ReadP Expr
expr = chainl1 (letEx <++ value <++ abstr <++ bracket expr) $ (many1 $ char ' ') *> return App

letEx :: ReadP Expr
letEx = do
  string "let" >> spaces1
  v <- ident
  spaces1 >> char '=' >> spaces1
  e <- expr <* skipSpaces
  b <- (string "in" >> skipSpaces *> expr >>= return . Just) <++ return Nothing
  return $ Let v e b

spaces1 :: ReadP ()
spaces1 = void $ many1 (satisfy isSpace)

ident :: ReadP String
ident = do
  first <- satisfy $ \c -> isAlpha c && c /= 'λ'
  rest <- many $ satisfy (\c -> isAlpha c || isDigit c)
  let id = first : rest
  guard $ not (id `elem` ["let", "in"])
  return id

value :: ReadP Expr
value = var <++ num

var :: ReadP Expr
var = Var <$> ident

num :: ReadP Expr
num = Abs "f" <$> Abs "x" <$> convert <$> read <$> many1 (satisfy isDigit)
  where convert 0 = Var "x"
        convert n = App (Var "f") (convert (n - 1))

abstr :: ReadP Expr
abstr = do
  char '\\' <|> char 'λ'
  x <- ident
  char '.'
  e <- expr
  return $ Abs x e

bracket :: ReadP a -> ReadP a
bracket e = do
  char '('
  skipSpaces
  x <- e
  skipSpaces
  char ')'
  return x

reducible :: Expr -> State Env Bool
reducible (Var x) = do
  (_, _, vars) <- S.get
  return $ M.member x vars
reducible (App (Abs _ _) _) = return True
reducible (App a b) = (||) <$> reducible a <*> reducible b
reducible (Abs _ _) = return False
reducible (Ptr _) = return True
reducible (Let x e _) = return True

eval' :: Expr -> State Env Expr
eval' (Var x) = do
  (_, _, vars) <- S.get
  return $ fromMaybe (Var x) $ M.lookup x vars
eval' (App (Abs x b) e) = return $ sub x e b
eval' (App a b) = do
  ra <- reducible a
  rb <- reducible b
  if ra then eval' a >>= \a' -> return (App a' b)
  else if rb then eval' b >>= \b' -> return (App a b')
  else undefined
eval' e@(Abs _ _) = return e
eval' (Let x e Nothing) = do
  r <- reducible e
  if r then eval' e >>= \e' -> return (Let x e' Nothing)
  else do
    (ps, n, vs) <- S.get
    let vs' = M.insert x e vs
    S.put (ps, n, vs')
    return e
eval' (Let x e (Just b)) = return $ sub x e b

fullEval' :: Expr -> State Env Expr
fullEval' e = do
  r <- reducible e
  if r then eval' e >>= fullEval' else return e

eval :: Expr -> Expr
eval e = S.evalState (fullEval' e) stdlib

evalS :: String -> Expr
evalS = eval . lam

countVars :: Var -> Expr -> Int
countVars v (Var x) = fromEnum (v == x)
countVars v (App e1 e2) = countVars v e1 + countVars v e2
countVars v (Abs w e)
  | v == w = 0
  | otherwise = countVars v e
countVars v (Ptr n) = error $ "can't count variables in a pointer " ++ show n

sub :: Var -> Expr -> Expr -> Expr
sub v to (Var x) | x == v = to
                 | otherwise = Var x
sub v to (App e1 e2) = App (sub v to e1) (sub v to e2)
sub v to (Abs x b) | x == v = Abs x b
                   | x /= v && not (isFree x to) = Abs x (sub v to b)
                   | otherwise = sub v to (Abs (x ++ "'") (sub x (Var $ x ++ "'") b))
sub v to (Ptr n) = error $ "can't substitute into a pointer " ++ show n

free :: Expr -> [Var]
free (Var x) = [x]
free (App e1 e2) = nub $ free e1 ++ free e2
free (Abs x b) = filter (/= x) (free b)
free (Ptr n) = error $ "can't get free variables of a pointer " ++ show n

isFree :: Var -> Expr -> Bool
isFree v e = v `elem` free e

stdlib :: Env
stdlib = (mempty, 0, fns)
  where fns = M.fromList $ [ ("add",   lam "\\a.\\b.\\f.\\x.a f (b f x)")
                           , ("pair",  lam "\\x.\\y.\\z.z x y")
                           , ("fst",   lam "\\p.p (\\x.\\y.x)")
                           , ("snd",   lam "\\p.p (\\x.\\y.y)")
                           , ("true",  lam "\\x.\\y.x")
                           , ("false", lam "\\x.\\y.y")
                           , ("and",   lam "\\a.\\b.a b a")
                           , ("or",    lam "\\a.\\b.a a b")
                           , ("not",   lam "\\a.a false true")
                           ]

main :: IO ()
main = void $ repl stdlib

repl :: Env -> IO Env
repl env = do
  putStr "λ "
  l <- getLine
  case readP_to_S (skipSpaces *> expr) l of
    [] -> putStrLn "invalid syntax" >> repl env
    xs -> case last xs of
            (e, "") -> do
              let (e', env') = S.runState (fullEval' e) env
              print e'
              repl env'
            _ -> putStrLn "invalid syntax: garbage after input" >> repl env
  
