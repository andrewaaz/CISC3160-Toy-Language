import System.IO
import Control.Monad
import Data.Char
import System.Environment
import qualified Data.Set as S
import qualified Data.List as L

main :: IO ()
main = do
   args <- getArgs
   execProg args

printExpect :: IO ()
printExpect = putStrLn "Usage: ./toy '<file>'"

prettyPrintClosure :: Closure Int -> String
prettyPrintClosure =
  L.foldr (\(name, val) acc -> acc ++ name ++ " = " ++ show val ++ "\n") ""

execProg :: [String] -> IO ()
execProg [] = printExpect
execProg [file] = do
  handle <- openFile file ReadMode
  contents <- hGetContents handle
  let result = interpretProgram contents  
  case result of
    (Just closure) -> putStr $ prettyPrintClosure closure
    Nothing        -> putStr "error"
execProg _ = printExpect

data ExprToken a
    = Value a
    | Id String
    | Operator Char
    | Eof
    | Invalid
    deriving (Eq, Show)

data Expr a
    = Single (Expr a)
    | Sequence (Expr a) (Expr a)
    | Assignment (Expr a) (Expr a)
    | Add (Expr a) (Expr a)
    | Sub (Expr a) (Expr a)
    | Mul (Expr a) (Expr a)
    | Negate (Expr a)
    | Literal a
    | Identifier String

type ParseState = [ExprToken Int]
type ParseResult = (Expr Int, ParseState)
type ParseResultStep = (Expr Int, ParseState, Bool)

isAtEof :: ParseState -> Bool
isAtEof [Eof] = True
isAtEof _     = False

parseLeaf :: ParseState -> Maybe ParseResult
parseLeaf (Value i:ts) = return (Literal i, ts)
parseLeaf (Id i:ts)    = return (Identifier i, ts)
parseLeaf _            = Nothing

parseLiteral :: ParseState -> Maybe ParseResult
parseLiteral (Value i:ts) = return (Literal i, ts)
parseLiteral _            = Nothing

parseIdentifier :: ParseState -> Maybe ParseResult
parseIdentifier (Id i:ts) = return (Identifier i, ts)
parseIdentifier _         = Nothing

parseParen :: ParseState -> Maybe ParseResult
parseParen (Operator '(':ts) = do
  (mexpr, rest0) <- parseAdd ts
  case rest0 of
    (Operator ')'):rest1 -> return (mexpr, rest1)
    _                    -> Nothing
parseParen ts = parseLeaf ts

parseNeg :: ParseState -> Maybe ParseResult
parseNeg (Operator '-':ts) = do
  (mexpr, rest0) <- parseNeg ts
  return (Negate mexpr, rest0)
parseNeg ts = parseParen ts

parseMul :: ParseState -> Maybe ParseResult
parseMul ts = do
  (mexpr, rest0) <- parseNeg ts
  iterateOnTokens extractMul mexpr rest0
  where extractMul a (Operator '*':rest1) = do
          (rexpr, rest2) <- parseMul rest1
          return (Mul a rexpr, rest2, True)
        extractMul a rest1                =
          return (a, rest1, False)

parseAdd :: ParseState -> Maybe ParseResult
parseAdd ts = do
  (mexpr, rest0) <- parseMul ts
  iterateOnTokens extractPlus mexpr rest0
  where extractPlus a (Operator '+':rest1) = do
          (rexpr, rest2) <- parseMul rest1
          return (Add a rexpr, rest2, True)
        extractPlus a (Operator '-':rest1) = do
          (rexpr, rest2) <- parseMul rest1
          return (Sub a rexpr, rest2, True)
        extractPlus a rest1                =
          return (a, rest1, False)

parseAssignment :: ParseState -> Maybe ParseResult
parseAssignment ts = do
  (mexpr, rest0) <- parseIdentifier ts
  case rest0 of
    (Operator '=':rest1) -> do
      (mexpr2, rest2) <- parseAdd rest1
      return (Assignment mexpr mexpr2, rest2)
    _                    -> Nothing

parseProgram :: ParseState -> Maybe ParseResult
parseProgram ts = do
  (mexpr, rest0) <- parseAssignment ts
  iterateOnTokens extractSemicolon (Single mexpr) rest0
  where extractSemicolon a (Operator ';':[Eof]) = do
          return (a, [Eof], False)
        extractSemicolon a (Operator ';':rest1) = do
          (rexpr, rest2) <- parseAssignment rest1
          return (Sequence a rexpr, rest2, True)
        extractSemicolon a rest1 =
          return (a, [], False)

iterateOnTokens :: (Expr Int -> ParseState -> Maybe ParseResultStep) -> Expr Int -> ParseState -> Maybe ParseResult
iterateOnTokens f a xs = do
  (mexpr, rest, continue) <- f a xs
  if continue then iterateOnTokens f mexpr rest else return (mexpr, rest)

-- step 2
parseTokens :: [ExprToken Int] -> Maybe (Expr Int)
parseTokens [] = Nothing
parseTokens xs = parseProgram xs >>= (\(root, rest) -> if isAtEof rest then Just root else Nothing)


-- valueStartSet = [1-9]
valueStartSet = S.fromList ['1'..'9']
-- valueSet = [0-9]
valueSet = S.fromList ['0'..'9']
-- idStartSet = [_a-zA-Z]
idStartSet = S.fromList $ '_' : ['a'..'z'] ++ ['A'..'Z']
-- idSet = [_a-zA-Z0-9]
idSet = S.union idStartSet valueSet
opSet = S.fromList ['+', '-', '*', '(', ')', '=', ';']

-- step 1
tokenizeStr :: String -> [ExprToken Int]
tokenizeStr [] = [Eof]
tokenizeStr str@(h:t)
   | h `S.member` valueStartSet = Value (read $ takeValues str):tokenizeStr (dropValues t)
   | h == '0'                   = Value 0:tokenizeStr t
   | h `S.member` idStartSet    = Id (takeId str):tokenizeStr (dropId t)
   | h `S.member` opSet         = Operator h:tokenizeStr t
   | isSpace h                  = tokenizeStr $ eatSpace t
   | otherwise                  = [Invalid]
   where takeValues = takeWhile (`S.member` valueSet)
         dropValues = dropWhile (`S.member` valueSet)
         takeId     = takeWhile (`S.member` idSet)
         dropId     = dropWhile (`S.member` idSet)
         eatSpace   = dropWhile isSpace

type Closure a = [(String, a)]
type EvalResult a = (a, Closure a)

closureLookup :: String -> Closure Int -> Maybe Int
closureLookup id c =
  snd <$> L.find (\(varname, val) -> varname == id) c

updateClosure :: Closure Int -> String -> Int -> Closure Int
updateClosure c id val =
  let newClosure = filter (\(varname, _) -> varname /= id) c
  in  (id, val) : newClosure

runAssignment :: Expr Int -> Expr Int -> Closure Int -> Maybe (EvalResult Int)
runAssignment (Identifier id) e1 c = do
  (rhs, c1) <- evalAst e1 c
  return (rhs, updateClosure c1 id rhs)
runAssignment _ _ _ = Nothing

-- Interpret the AST
evalAst :: Expr Int -> Closure Int -> Maybe (EvalResult Int)
evalAst (Assignment e0 e1) c = runAssignment e0 e1 c
evalAst (Single e) c         = evalAst e  c >>= \(r0, c1) -> return (r0, c1)
evalAst (Sequence e0 e1) c   = evalAst e0 c >>= \(_, c1)  -> evalAst e1 c1 >>= \(r1, c2) -> return (r1, c2)
evalAst (Add e0 e1) c        = evalAst e0 c >>= \(r0, c1) -> evalAst e1 c1 >>= \(r1, c2) -> return (r0 + r1, c2)
evalAst (Sub e0 e1) c        = evalAst e0 c >>= \(r0, c1) -> evalAst e1 c1 >>= \(r1, c2) -> return (r0 - r1, c2)
evalAst (Mul e0 e1) c        = evalAst e0 c >>= \(r0, c1) -> evalAst e1 c1 >>= \(r1, c2) -> return (r0 * r1, c2)
evalAst (Negate e0) c        = evalAst e0 c >>= \(r0, c1) -> return (-r0, c1)
evalAst (Literal i) c        = return (i, c)
evalAst (Identifier id) c    = closureLookup id c >>= \val -> return (val, c)

showAst :: Expr Int -> String
showAst (Sequence e0 e1)   = let lhs = showAst e0; rhs = showAst e1 in lhs ++ rhs ++ ";\n"
showAst (Single e0)        = let expr = showAst e0 in expr ++ ";\n"
showAst (Assignment e0 e1) = let lhs = showAst e0; rhs = showAst e1 in lhs ++ " = " ++ rhs
showAst (Add e0 e1)        = let lhs = showAst e0; rhs = showAst e1 in "(" ++ lhs ++ " + " ++ rhs ++ ")"
showAst (Sub e0 e1)        = let lhs = showAst e0; rhs = showAst e1 in "(" ++ lhs ++ " - " ++ rhs ++ ")"
showAst (Mul e0 e1)        = let lhs = showAst e0; rhs = showAst e1 in "(" ++ lhs ++ " * " ++ rhs ++ ")"
showAst (Negate e0)        = let expr = showAst e0 in "(-" ++ expr ++ ")"
showAst (Literal i)        = let val = show i in val
showAst (Identifier n)     = let val = show n in val

parseAndStringifyProgram :: String -> Maybe String
parseAndStringifyProgram s = do
  ast <- parseTokens $ tokenizeStr s
  Just $ showAst ast

interpretProgram :: String -> Maybe (Closure Int)
interpretProgram s = do
  ast <- parseTokens $ tokenizeStr s
  snd <$> evalAst ast []