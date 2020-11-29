{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
import Control.Monad
import Data.Bifunctor
import Data.Bits ((.|.))
import Data.Char
import Data.Foldable
import Data.Monoid hiding (All(..))
import Data.Maybe
import Data.List
import Data.Ord
import Data.Array (Array)
import Data.Traversable
import System.Environment
import System.FilePath
import Debug.Trace
import qualified Data.ByteString.Char8 as BS
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Printf
import Text.Regex.PCRE 

type S = BS.ByteString

type Module = S

data What
    = All CountableItem

    | Function Function
    | TypeClass TypeClass
    | Axiom Axiom

    | Headers
    | Types
    | Tactics

    | WellFormedness
    | WellFormednessLemmas

    | Lists
    | CoqInterface
  deriving (Show, Eq, Ord)

data FuncOrInstance = AFunc ExpStatus | AnInst
  deriving (Show, Eq, Ord)
data ExpStatus = Exported | Internal
  deriving (Show, Eq, Ord, Enum, Bounded)
data HowFar = Verif | Unverif | Untrans | Axiomatized
  deriving (Show, Eq, Ord, Enum, Bounded)
type CountableItem = (FuncOrInstance, HowFar)

type Group = What -- a bit ugly

modules :: [Module]
modules = ["CSE",
           "CoreFVs",
           "CoreSubst",
           "Exitify",
           "FV",
           "TrieMap",
           "Unique",
           "Util",           
           "Var",
           "VarEnv",
           "VarSet",
           "Core"
           ]

-- Common up some highly related functions under a common name
normWhat :: Module -> Column -> What -> What
normWhat _ _ WellFormednessLemmas = WellFormedness -- disable this distinction
normWhat _ _ Types = Headers -- disable this distinction

-- normWhat "Utils" _ (Function _) = Functions

normWhat _ _ (Function "op_zrzr__") = Function "difference"
normWhat _ _ (Function "op_zn__") = Function "find"
normWhat _ _ (Function "op_znz3fU__") = Function "lookup"

-- Smart accessor
normWhat m c (Function "bin")           = normWhat m c Types

-- These are edited away, but thats not the same as untranslated or unverified.
normWhat m c (Function "hetPtrEq")      = normWhat m c Types
normWhat m c (Function "ptrEq")         = normWhat m c Types
normWhat m c (Function "intFromNat")    = normWhat m c Types
normWhat m c (Function "natFromInt")    = normWhat m c Types
normWhat m c (Function "wordSize")      = normWhat m c Types
normWhat m c (Function "prefixBitMask") = normWhat m c Types
-- Actually not defined when compiled with GHC (tally.hs ignores CPP)
normWhat m c (Function "lazy")          = normWhat m c Types

-- record accessors
normWhat m c (Function "matchedKey")      = normWhat m c Types
normWhat m c (Function "getMergeSet")     = normWhat m c Types
normWhat m c (Function "missingKey")      = normWhat m c Types
normWhat m c (Function "missingSubtree")  = normWhat m c Types

normWhat m c (Function "fromListConstr")  = normWhat m c (TypeClass "Data")
normWhat m c (Function "setDataType")     = normWhat m c (TypeClass "Data")
normWhat m c (Function "mapDataType")     = normWhat m c (TypeClass "Data")
normWhat m c (Function "intSetDataType")  = normWhat m c (TypeClass "Data")

normWhat m c (Function "delta")           = normWhat m c Types
normWhat m c (Function "ratio")           = normWhat m c Types
normWhat m c (Function "set_size")        = normWhat m c Types
normWhat m c (Function "map_size")        = normWhat m c Types
normWhat m c (Function "size_nat")        = normWhat m c Types
normWhat _ _ (Function f)
    | f `elem` BS.words "showTreeWith showWide showsBars showsTree showsTreeHang withBar withEmpty node showBin showsBitMap showBitMap"
    = Function "showTree"
normWhat _ _ w = w

showWhat :: What -> BS.ByteString
showWhat (Function f)   = f
showWhat (TypeClass f)  = "instance " <> f
showWhat (Axiom f)      = "axiomatize " <> f
showWhat (All (AFunc _, Verif))       = "Functions, verified"
showWhat (All (AFunc _, Unverif))     = "Functions, unverified"
showWhat (All (AFunc _, Untrans))     = "Functions, untranslated"
showWhat (All (AFunc _, Axiomatized)) = "Functions, axiomatized"
showWhat (All (AnInst, Verif))        = "Type classes, verified"
showWhat (All (AnInst, Unverif))      = "Type classes, unverified"
showWhat (All (AnInst, Untrans))      = "Type classes, untranslated"
showWhat WellFormedness        = "Well-formedness"
showWhat WellFormednessLemmas  = "(lemmas)"
showWhat Headers  = "Headers and types"
showWhat CoqInterface  = "\\texttt{FSetInterface}"
showWhat w              = BS.pack (show w)

showWhatShort :: What -> BS.ByteString
showWhatShort (Function f)   = f
showWhatShort (TypeClass f)  = "instance " <> f
showWhatShort (All (AFunc _, Verif))   = "Funcs, verf."
showWhatShort (All (AFunc _, Unverif)) = "\\ldots, unverif."
showWhatShort (All (AFunc _, Untrans)) = "\\ldots, untrans."
showWhatShort (All (AFunc _, Axiomatized)) = "\\ldots, axiom."
showWhatShort (All (AnInst, Verif))    = "Classes, verif."
showWhatShort (All (AnInst, Unverif))  = "\\ldots, unverif."
showWhatShort (All (AnInst, Untrans))  = "\\ldots, untrans."
showWhatShort WellFormedness        = "WF"
showWhatShort WellFormednessLemmas  = "(lemmas)"
showWhatShort w              = BS.pack (show w)

type Function = S
type TypeClass = S
type Axiom = S
type Pats = [(Regex, ToFun)]
data Column = Haskell | Gallina | Proofs deriving (Show, Eq, Ord, Enum, Bounded)

publicFiles :: [(FilePath, Module)]
publicFiles =
    [ 
      ("ghc/compiler/coreSyn/CoreFVs.hs",   "CoreFVs")
    , ("ghc/compiler/coreSyn/CoreSubst.hs", "CoreSubst")
    , ("ghc/compiler/coreSyn/CoreStats.hs", "CoreStats")
    , ("ghc/compiler/coreSyn/CoreUtils.hs", "CoreUtils")
    , ("ghc/compiler/coreSyn/TrieMap.hs",   "TrieMap")                    
    , ("ghc/compiler/simplCore/Exitify.hs", "Exitify")
    , ("ghc/compiler/simplCore/CSE.hs",     "CSE")    
    , ("ghc/compiler/utils/FV.hs",          "FV")
    , ("ghc/compiler/utils/Util.hs",        "Util")
    , ("ghc/compiler/coreSyn/TrieMap.hs",   "TrieMap")
    , ("ghc/compiler/basicTypes/Unique.hs", "Unique")
    , ("ghc/compiler/basicTypes/Var.hs",    "Var")
    , ("ghc/compiler/basicTypes/VarEnv.hs", "VarEnv")
    , ("ghc/compiler/basicTypes/VarSet.hs", "VarSet")
    , ("ghc/compiler/coreSyn/CoreSyn.hs",   "CoreSyn")
    ]

files :: [(FilePath, Pats, Module, Column)]
files =
    [ ("theories/CSE.v",                       proofs, "CSE", Proofs)
    , ("theories/CoreFVs.v",                   proofs, "CoreFVs", Proofs)
    , ("theories/CoreSubst.v",                 proofs, "CoreSubst", Proofs)
    , ("theories/Exitify.v",                   proofs, "Exitify", Proofs)    

    , ("theories/Core.v",                      proofs, "Core", Proofs)
    , ("theories/CoreInduct.v",                proofs, "Core", Proofs)
    , ("theories/CoreStats.v",                 proofs, "CoreStats", Proofs)
    , ("theories/FV.v",                        proofs, "FV", Proofs)
{-
theories/Forall.v
theories/GhcTactics.v
theories/GhcUtils.v
theories/JoinPointInvariants.v
theories/JoinPointInvariantsInductive.v
theories/ScopeInvariant.v
-}
     , ("theories/StateLogic.v",               proofs, "State", Proofs)
     , ("theories/TrieMap.v",                  proofs, "TrieMap", Proofs)
     , ("theories/UniqSetInv.v",               proofs, "UniqSet", Proofs)
     , ("theories/Unique.v",                   proofs, "Uniq", Proofs)
     , ("theories/Util.v",                     proofs, "Util", Proofs)
     , ("theories/Var.v",                      proofs, "Core", Proofs)
     , ("theories/VarEnv.v",                   proofs, "Core", Proofs)
     , ("theories/VarSet.v",                   proofs, "Core", Proofs)
     , ("theories/VarSetFSet.v",               proofs, "Core", Proofs)
    
    , ("lib/CSE.v",                             gallina,     "CSE",    Gallina)
    , ("lib/CoreFVs.v",                         gallina,     "CoreFVs", Gallina)
    , ("lib/CoreSubst.v",                       gallina,     "CoreSubst", Gallina)
    , ("lib/Exitify.v",                         gallina,     "Exitify", Gallina)    
    , ("lib/Core.v",                      gallina, "Core", Gallina)
    , ("lib/CoreStats.v",                 gallina, "CoreStats", Gallina)
    , ("lib/FV.v",                        gallina, "FV", Gallina)
    , ("lib/State.v",                    gallina, "State", Gallina)
    , ("lib/TrieMap.v",                  gallina, "TrieMap", Gallina)
    , ("lib/UniqSet.v",                  gallina, "UniqSet", Gallina)
    , ("lib/Unique.v",                   gallina, "Uniq", Gallina)
    , ("lib/Util.v",                     gallina, "Util", Gallina)

    , ("ghc/compiler/simplCore/CSE.hs",         hs,   "CSE",       Haskell)
    , ("ghc/compiler/coreSyn/CoreFVs.hs",       hs,   "CoreFVs",   Haskell)
    , ("ghc/compiler/coreSyn/CoreSubst.hs",     hs,   "CoreSubst", Haskell)
    , ("ghc/compiler/simplCore/Exitify.hs", hs,  "Exitify",   Haskell)
    , ("ghc/compiler/coreSyn/CoreStats.hs", hs,  "CoreStats", Haskell)
    , ("ghc/compiler/coreSyn/CoreUtils.hs", hs,  "CoreUtils", Haskell)
    , ("ghc/compiler/coreSyn/TrieMap.hs", hs,    "TrieMap", Haskell)                    
    , ("ghc/compiler/simplCore/Exitify.hs", hs,  "Exitify", Haskell)
    , ("ghc/compiler/simplCore/CSE.hs", hs,      "CSE", Haskell)    
    , ("ghc/compiler/utils/FV.hs", hs,           "FV", Haskell)
    , ("ghc/compiler/utils/Util.hs", hs,         "Util", Haskell)
    , ("ghc/compiler/coreSyn/TrieMap.hs", hs,    "TrieMap", Haskell)
    , ("ghc/compiler/basicTypes/Unique.hs", hs,  "Unique", Haskell)
    , ("ghc/compiler/basicTypes/Var.hs", hs,     "Core", Haskell)
    , ("ghc/compiler/basicTypes/VarEnv.hs", hs,  "Core", Haskell)
    , ("ghc/compiler/basicTypes/VarSet.hs", hs,  "Core", Haskell)
    , ("ghc/compiler/coreSyn/CoreSyn.hs", hs,    "Core", Haskell)
    , ("ghc/compiler/basicTypes/IdInfo.hs", hs,  "Core", Haskell)
    , ("ghc/compiler/types/Class.hs", hs,    "Core", Haskell)
    , ("ghc/compiler/types/TyCon.hs", hs,    "Core", Haskell)
    , ("ghc/compiler/basicTypes/DataCon.hs", hs,  "Core", Haskell)
    , ("ghc/compiler/basicTypes/PatSyn.hs", hs,   "Core", Haskell)
    , ("ghc/compiler/basicTypes/Demand.hs", hs,   "Core", Haskell)
    , ("ghc/compiler/types/Type.hs", hs,   "Core", Haskell)
    , ("ghc/compiler/types/TyCoRep.hs", hs,   "Core", Haskell)
    , ("ghc/compiler/types/Coercion.hs", hs,   "Core", Haskell)                                    
    
    ]
  where
    all :: What -> Pats
    all w = [(mkM ".*", k w)]

type ToFun = MatchResult S -> What
k :: What -> ToFun
k = const
f1 :: ToFun
f1 = Function . head . mrSubList
tc1 :: ToFun
tc1 = TypeClass . head . mrSubList
a1 :: ToFun
a1 = Axiom . head.mrSubList

hs :: Pats
hs = first mk <$>
    [ ("^data Set",                        k Types)
    , ("^data Map",                        k Types)
    , ("^data IntSet",                     k Types)
    , ("^newtype Identity",                k Types)
    , ("^data WhenMissing",                k Types)
    , ("^instance .*WhenMatched",          k Types)
    , ("instance.* (?:.*\\.)?(.*?) \\(?(?:Set|IntSet|Map)",  tc1)
    , ("^(insertMin)",                     f1)
    , ("^(insertMax)",                     f1)
    , ("^(lowestBitSet|highestBitSet|fold.'?Bits) ", f1)
    , ("^infixl . \\\\\\\\",               k (Function "difference"))
    , ("^\\(\\\\\\\\\\)",                  k (Function "difference"))
    , ("^\\(!\\)",                         k (Function "find"))
    , ("^\\(!\\?\\)",                      k (Function "lookup"))
    , ("^([a-zA-Z0-9'_]*?)(?:,.*)? +::",   f1)
    , ("^(mergeA)$",                       f1)
    ]

all_valid :: Pats
all_valid = first mk <$>
    [ ("^valid ::",                        k (Function "valid"))
    , ("^Definition",                      k (Function "valid"))
    ]

gallina :: Pats
gallina = first mk <$>
    [ ("^Definition Size",                 k Types)
    , ("^Inductive Set_",                  k Types)
    , ("^Inductive IntSet",                k Types)
    , ("^Inductive Map",                   k Types)
    , ("^Axiom patternFailure",            k Headers)
    , ("^Axiom unsafeFix",                 k Headers)
    , ("^Ltac",                            k Tactics)
    , ("^Local Definition (.+?)__",        tc1)
    , ("^Program Instance (.+?)__",        tc1)
    , ("^Fixpoint (.*?) ",                 f1)
    , ("^Program Fixpoint (.*?) ",         f1)
    , ("^Definition ([A-Z].*?) ",          k Types)
    , ("^Definition ([a-z].*?) ",          f1)
    , ("^Program Definition ([a-z].*?) ",  f1)
    , ("^Axiom ([a-z].*?) ",               a1)
    , ("^Axiom ([A-Z].*?) ",               a1)    
    ]

proofs :: Pats
proofs = first mk <$>
    [ (sect "Tactics",                               k Tactics)
    , (sect "General utility tactics",               k Tactics)
    , (sect "An omega that "         ,               k Tactics)
    , (sect "Utilities about sorted ",               k Lists)
    , (sect "The \\[nonneg\\] tactic",               k Tactics)
    , (sect "Verification of \\[(Eq1?|Ord1?|Monoid|Semigroup)\\]",              tc1)
    , (sect "Verification of \\[(.*?)\\]",           f1)
    , (sect "Lemmas related to well-formedness",     k WellFormednessLemmas)
    , (sect "Well-formedness",                       k WellFormedness)
    , (sect "Well-formed IntSets",                   k WellFormedness)
    , (sect "A setup for complete specification",    k WellFormednessLemmas)
    , (sect "Instantiating the \\[FSetInterface\\]", k CoqInterface)
    ]
  where
    sect = ("^\\(\\*\\* \\*\\*?\\*? " <>)

mk, mkM :: S -> Regex
mk s = makeRegexOpts (defaultCompOpt .|. compMultiline) defaultExecOpt (s <> ".*$")
mkM  = makeRegexOpts (defaultCompOpt .|. compDotAll .|. compMultiline) defaultExecOpt

type Table = [(Module, What, Column, S, Int)]
type Summary = M.Map (Module, What, Column) Int
type ItemDesc = (Module, What) -> Maybe CountableItem
type GroupSummary = M.Map (Module, Group, Column) Int
type Exported = S.Set (Module, Function)

categorizeItems :: Exported -> Summary -> ItemDesc
categorizeItems exported summary = (`M.lookup` m)
  where
    howFar m w | (m,w,Proofs)  `M.member` summary = Verif
               | (m,w,Gallina) `M.member` summary = Unverif
               | otherwise                        = Untrans

    exp m f | (m,f) `S.member` exported = Exported
            | otherwise                 = Internal

    m = M.fromList $
          [ ((m,w), (AFunc (exp m f),howFar m w))
          | ((m, w@(Function f), _), _) <- M.toList summary] ++
          [ ((m,w), (AnInst,howFar m w))
          | ((m, w@TypeClass{}, _), _) <- M.toList summary]

summarizeGroups :: Summary -> ItemDesc -> GroupSummary
summarizeGroups summary itemDesc =
    M.fromListWith (+) [ ((mod, groupOf mod what, col), n)
                       | ((mod, what, col), n) <- M.toList summary ]
  where
    groupOf m w | Just ci <- itemDesc (m, w) = All ci
                | otherwise                  =  w

summarize :: Table -> Summary
summarize table = M.fromListWith (+)
    [ ((mod, what, col), n)
    | (mod, what, col, _, n) <- table
    , n > 0
    ]

parseExportList :: S -> [Function]
parseExportList txt
    | [[_,export_list]] <- match re1 txt
    = [ fn | [_,fn] <- toList @(Array Int) $ getAllTextMatches $ match re2 (export_list::S) ]
    | otherwise = []
  where
    re1 = mkM "module +[a-zA-Z.]+ +\\((.*?)(?:-- \\* Debugging.*?)?(?:#if defined\\(TESTING\\).*?)?\\) +where"
    re2 = mkM "^ +, (?:I?S\\.)?(.*?)$"
    -- re = mkM "module +[a-zA-Z.]+ (.*?, (:?[^\n]*\\.)?\\([a-zA-Z0-9].*?\\)$.*?) +where"

main :: IO ()
main = do
    args <- getArgs
    let path = case args of
                [d] -> d
                _ ->    error "Usage: ./tally .../hs-to-coq/examples/ghc"

    table <- concat <$> (for files $ \(fn, pats, mod, col) -> do
        f <- BS.readFile (path </> fn)
        pure $ classify pats mod col "" f Headers)

    exported <- S.fromList . concat <$> sequence
        [ do txt <- BS.readFile (path </> fn)
             return [ (mod, f) | f <- parseExportList txt ]
        | (fn, mod) <- publicFiles ]

    BS.writeFile "tally.debug" $ BS.unlines $ concat
        [ (BS.pack $ printf "%s in %s %s (%d non-comment lines):" (BS.unpack $ showWhat what) (show col) (BS.unpack mod) n) :
          map ("    " <>) (BS.lines txt) -- (stripComments txt)
        | (mod, what, col, txt, n) <- table ]

    let summary = summarize table
    let itemDesc = categorizeItems exported summary
    let gsummary = summarizeGroups summary itemDesc

    BS.writeFile "tally.csv" $ printSummary summary
    BS.writeFile "tally.tex" $ mconcat
        [ def "summarytallytable"
        $ printLaTeXSummary gsummary
        , def "translationcoordinates"
        $ printTransCoordinateList summary
        , def "provingcoordinates"
        $ printProvingCoordinateList summary
        , def2 "modsummarysymboliccoords" "modsummaryplots"
        $ printModSummaryPlots gsummary
        , def2 "modsummarysymboliccoordsSet" "modsummaryplotsSet"
        $ printModSummaryPlots' "Set" gsummary
        , def2 "modsummarysymboliccoordsMap" "modsummaryplotsMap"
        $ printModSummaryPlots' "Map" gsummary
        , def2 "modsummarysymboliccoordsIntSet" "modsummaryplotsIntSet"
        $ printModSummaryPlots' "IntSet" gsummary
        , def2 "modsummarysymboliccoordsUtils" "modsummaryplotsUtils"
        $ printModSummaryPlots' "Utils" gsummary
        , printNumbers summary itemDesc
        , printFuncLists summary itemDesc
        ]

printTransCoordinateList :: Summary -> S
printTransCoordinateList summary = BS.unlines $ sort
    [ coordinateData (showBS g) (showBS h) m (showBS w)
    | (m, w) <- S.toList $ S.fromList [ (m,w) | (m,w,_) <- M.keys summary, isInteresting w ]
    , Just h <- pure $ M.lookup (m,w,Haskell) summary
    , Just g <- pure $ M.lookup (m,w,Gallina) summary
    ]
  where
    isInteresting (Function _) = True
    isInteresting (TypeClass _) = True
    isInteresting _ = False

printProvingCoordinateList :: Summary -> S
printProvingCoordinateList summary = BS.unlines $ sort
    [ coordinateData (showBS p) (showBS g) m (showBS w)
    | (m, w) <- S.toList $ S.fromList [ (m,w) | (m,w,_) <- M.keys summary, isInteresting w ]
    , Just g <- pure $ M.lookup (m,w,Gallina) summary
    , Just p <- pure $ M.lookup (m,w,Proofs) summary
    ]
  where
    isInteresting (Function _) = True
    isInteresting (TypeClass _) = True
    isInteresting _ = False

printModSummaryPlots :: GroupSummary -> (S, S)
printModSummaryPlots summary = (symboliccoords, plots)
  where
    symboliccoords = "symbolic y coords={" <> commas [ barLabel c m | (m,c) <- bars] <> "}"
    plots = BS.unlines $
      [ "\\addplot coordinates {" <> BS.unwords
        [ coordinate (showBS n) (barLabel c m)
        | (m,c) <- bars
        , let n = lookupInt (m,g,c) summary
        ] <>
        "};"
      | g <- groups
      ] ++
      [ "\\legend{ " <> commas ["{" <> showWhatShort g <> "}"| g <- groups ] <> "}" ]
    barLabel Haskell m = m <> ".hs"
    barLabel Gallina m = m <> ".v"
    barLabel Proofs m  = m <> "Proofs.v"
    cols = [minBound..maxBound]
    mods = S.toList $ S.fromList [ m | (m,g,c) <- M.keys summary]
    bars = reverse $ (,) <$> modules <*> cols
    groups = S.toList $ S.fromList [ g | (m,g,c) <- M.keys summary]

printModSummaryPlots' :: Module -> GroupSummary -> (S, S)
printModSummaryPlots' mod summary = (symboliccoords, plots)
  where
    symboliccoords = "symbolic y coords={" <> commas [ showBS c | c <- cols] <> "}"
    plots = BS.unlines $
      [ "\\addplot coordinates {" <> BS.unwords
        [ coordinate (showBS n) (showBS c)
        | c <- cols
        , let n = lookupInt (mod,g,c) summary
        ] <>
        "};"
      | g <- groups
      ] ++
      [ "\\legend{ " <> commas ["{" <> showWhatShort g <> "}"| g <- groups ] <> "}" ]
    cols = reverse $ [minBound..maxBound]
    groups = S.toList $ S.fromList [ g | (m,g,c) <- M.keys summary]

pruneUnverified :: Summary -> Summary
pruneUnverified summary = M.filterWithKey test summary
  where test (mod,what,col) _ = M.member (mod,what,Proofs) summary


coordinate :: S -> S -> S
coordinate x y = "(" <> x <> "," <> y <> ")"

coordinateData :: S -> S -> S -> S -> S
coordinateData x y d w = "(" <> x <> "," <> y <> ") [" <> d <> "] % " <> w

def :: S -> S -> S
def n c = "\\newcommand{\\" <> n <> "}{" <> c <> "}\n"

def2 :: S -> S -> (S,S) -> S
def2 n1 n2 (c1,c2) = def n1 c1 <> def n2 c2

defN :: S -> Int -> S
defN n c = def n (prettyNum (showBS c))
  where
    prettyNum xs | l > 3 = prettyNum (BS.take (l - 3) xs) <> "" <> BS.drop (l - 3) xs
                 | otherwise = xs
      where l = BS.length xs

defI :: S -> Int -> S
defI n c = def n (showBS c)
  where
    prettyNum xs | l > 3 = prettyNum (BS.take (l - 3) xs) <> "" <> BS.drop (l - 3) xs
                 | otherwise = xs
      where l = BS.length xs

defP :: S -> Int -> Int -> S
defP n a b = def n (showBS p)
  where p = round ((100::Double) * fromIntegral a / fromIntegral b)

defF :: S -> Int -> Int -> S
defF n a b = def n (BS.pack (printf "%.1f" p))
  where p = fromIntegral a / fromIntegral b :: Double

printSummary :: M.Map (S,What,Column) Int -> S
printSummary summary
    = BS.unlines $
    ( commas $ "Module" : "Function" : map (BS.pack . show) cols) :
    [ BS.intercalate "," $
       x : showWhat y : [ lookupIntS (x,y,c) summary | c <- cols]
    | (x,y) <- rows ]
  where
    cols = [minBound..maxBound]
    rows = S.toList $ S.fromList [ (x,y) | (x,y,_)   <- M.keys summary]


commas :: [S] -> S
commas = BS.intercalate ","
commas_ :: [S] -> S
commas_ = BS.intercalate ", "

lookupInt :: Ord a => a -> M.Map a Int -> Int
lookupInt x = fromMaybe 0 . M.lookup x

lookupIntS :: Ord a => a -> M.Map a Int -> S
lookupIntS x = maybe "" (BS.pack . show) . M.lookup x

printFuncLists :: Summary -> ItemDesc -> S
printFuncLists gsummary itemDesc = mconcat
    [ def ("list" <> showBS howFar <> mod) $ mconcat
        [ commas_ $ map showTT [ f | (m,Function f,Just (AFunc Exported, h),Haskell,n) <- l, m == mod, h == howFar]
        , "\\\\\\textbf{Instances:} "
        , commas_ $ map showTT [ f | (m,TypeClass f,Just (_, h),Haskell,n) <- l, m == mod, h == howFar]
        , "\\\\\\textbf{Internal functions:} "
        , commas_ $ map showTT [ f | (m,Function f,Just (AFunc Internal, h),Haskell,n) <- l, m == mod, h == howFar]
        ]
    | mod <- modules , howFar <- [minBound..maxBound]
    ]
  where
    l = [(m,w,d,c,n) | ((m,w,c),n) <- M.toList gsummary, let d = itemDesc (m, w)]
    showTT f  = "\\texttt{" <> f <> "}"

printNumbers :: Summary -> ItemDesc -> S
printNumbers gsummary itemDesc = mconcat $
    [ defN "funcs" $ length
        [ n | (m,w,Just (AFunc _, _),Haskell,n) <- l]
    , defN "tycls" $ length
        [ n | (m,w,Just (AnInst,_),Haskell,n) <- l]
    , defN "locHaskell" $ sum
        [ n | (_,_,_,Haskell,n) <- l ]
    , defN "funcsUntranslated" $ length
        [ n | (m,w,Just (AFunc _, Untrans),Haskell,n) <- l]
    , defN "tyclsUntranslated" $ length
        [ n | (m,w,Just (AnInst,Untrans),Haskell,n) <- l]
    , defN "locHaskellUntranslated" $ sum $
        [ n | (m,w,Just (_,Untrans),Haskell,n) <- l]
    , defN "locGallina" $ sum
        [ n | (_,_,_,Gallina,n) <- l ]
    , defN "funcsVerified" $ length
        [ n | (m,w,Just (AFunc _, Verif),Haskell,n) <- l]
    , defN "tyclsVerified" $ length
        [ n | (m,w,Just (AnInst, Verif), Haskell,n) <- l]

    , defN "locHaskellVerified" $ sum $
        [ n | (m,w,Just (_,Verif), Haskell,n) <- l] ++
        [ n | (_,Headers,_,Haskell,n) <- l ]
    , defN "locGallinaVerified" $ sum $
        [ n | (m,w,Just (_, Verif), Gallina,n) <- l] ++
        [ n | (_,Headers,_,Gallina,n) <- l ]
    , defP "percVerifiedSet"
        (length [ () | ("Set",   w,Just (_, Verif), Haskell,n) <- l ])
        (length [ () | ("Set",   w,Just (_, _    ), Haskell,n) <- l ])
    , defP "percVerifiedMap"
        (length [ () | ("Map",   w,Just (_, Verif), Haskell,n) <- l ])
        (length [ () | ("Map",   w,Just (_, _    ), Haskell,n) <- l ])
    , defP "percVerifiedIntSet"
        (length [ () | ("IntSet",w,Just (_, Verif), Haskell,n) <- l ])
        (length [ () | ("IntSet",w,Just (_, _    ), Haskell,n) <- l ])
    , defN "locProofs"       $ sum $ [ n | (_,_,             _, Proofs,n) <- l ]
    , defN "locProofsHeader" $ sum $ [ n | (_,Headers,       _, Proofs,n) <- l ]
    , defN "locWF"           $ sum $ [ n | (_,WellFormedness,_, Proofs,n) <- l ]
    , defN "locTactics"      $ sum $ [ n | (_,Tactics,       _, Proofs,n) <- l ]
    , defN "locCoqInterface" $ sum $ [ n | (_,CoqInterface,  _, Proofs,n) <- l ]
    , defN "locLists"        $ sum $ [ n | (_,Lists,         _, Proofs,n) <- l ]
    , defN "locProofsFunctions"   $ sum
        [ n | (_,w,Just (AFunc _,_), Proofs,n) <- l]
    , defN "locProofsTypeClasses" $ sum
        [ n | (_,w,Just (AnInst,_), Proofs,n) <- l]
    , defF "locProofPerHaskell"
        (sum [ n | (m,        w,Just (_, Verif), Proofs,n) <- l ])
        (sum [ n | (m,        w,Just (_, Verif), Haskell,n) <- l ])
    , defF "locProofPerHaskellSet"
        (sum [ n | ("Set",    w,Just (_, Verif), Proofs,n) <- l ])
        (sum [ n | ("Set",    w,Just (_, Verif), Haskell,n) <- l ])
    , defF "locProofPerHaskellIntSet"
        (sum [ n | ("IntSet", w,Just (_, Verif), Proofs,n) <- l ])
        (sum [ n | ("IntSet", w,Just (_, Verif), Haskell,n) <- l ])
    ] ++
    trace double_counted
    [ defI cmd $ sum $ [ n | (m,w,d,c,n) <- filtered cmd l]
    | cmd <- ["plot"] <<>> plotCmds
    ]
  where
    l = [(m,w,d,c,n) | ((m,w,c),n) <- M.toList gsummary, let d = itemDesc (m, w)]
    xs <<>> ys = (<>) <$> xs <*> ys
    plotCmds =
      (["Haskell","Gallina","Proofs"] <<>>
         (
         (["Constant", "Verified", "Unverified", "Untranslated"] <<>> ["Set","IntSet"])))
      ++ ["Lists", "CoqInterface"]

    double_counted = unlines [ show (x, cmds)
        | x <- l
        , let cmds = [ cmd | cmd <- plotCmds, not (null (filtered cmd [x])) ]
        , length cmds /= 1
        ]


    extra_modular = [Lists, CoqInterface]
    selectors =
        [ ("Haskell",      \l -> [ x | x@(_,_,_,Haskell,_) <- l])
        , ("Gallina",      \l -> [ x | x@(_,_,_,Gallina,_) <- l])
        , ("Proofs",       \l -> [ x | x@(_,_,_,Proofs,_) <- l])
        , ("Verified",     \l -> [ x | x@(_,_,Just (_, Verif),_,_) <- l])
        , ("Unverified",   \l -> [ x | x@(_,_,Just (_, Unverif),_,_) <- l])
        , ("Untranslated", \l -> [ x | x@(_,_,Just (_, Untrans),_,_) <- l])
        , ("Constant",     \l -> [ x | x@(_,w,Nothing, _,_) <- l, w `notElem` extra_modular])
        , ("Lists",        \l -> [ x | x@(_,Lists,_, _,_) <- l])
        , ("CoqInterface", \l -> [ x | x@(_,CoqInterface,_, _,_) <- l])
        ]
    filtered cmd l = foldl' go l selectors
      where go l ("Set", f) | "IntSet" `BS.isInfixOf` cmd = l
            go l (w, f)     | w `BS.isInfixOf` cmd = f l
                            | otherwise            = l


printLaTeXSummary :: GroupSummary -> S
printLaTeXSummary summary
    = BS.unlines $
    [ "\\begin{tabular}{l|rrr|rrr|rrr}"
    , row' ("" : map center (map showBS cols))
    , row  ("" : concatMap (const subColumns) cols)
    ] ++ concat
    [ [ "\\noalign{\\hrule height 0.4pt}" ] ++
      [ row' $ firstLine :
              [ lookupIntS (w,c) gsummary | c <- cols ]
      | showTotal
      ] ++
      [ row $ secondLine :
              [ lookupIntS (m,w,c) summary | c <- cols, m <- subColumns]
      ]
    | (w, groupRows) <- M.toList groupedRows
    , let showTotal = length groupRows > 1
    , let (firstLine, secondLine)
            | showTotal = second ("\\quad " <>) $ splitComma (showWhat w)
            | otherwise = (undefined, showWhat w)
    ] ++
    [ "\\end{tabular}" ]
  where
    splitComma x | BS.null b = (a,b)
                 | otherwise = (a <> ",", BS.tail b)
      where
        (a,b) = BS.break (','==) x
    center x = "\\multicolumn{1}{c}{" <> x <> "}"
    row xs = BS.intercalate " & " xs <> "\\\\"
    row' (x:xs) = BS.intercalate " & " ys <> "\\\\"
      where ys = x : concatMap (\y -> if BS.null y then ["","",""] else ["",y,""]) xs
    cols = [minBound..maxBound]
    rows = S.toList $ S.fromList [ (x,y) | (x,y,_)   <- M.keys summary]
    gsummary = M.fromListWith (+)
        [ ((what, col), n)
        | ((mod, what, col), n) <- M.toList summary
        ]
    groupedRows = M.fromListWith (++) [(w, [m]) | (m,w) <- rows]
    subColumns = modules


showBS :: Show a => a -> S
showBS = BS.pack . show

showMod :: Module -> S
showMod m = "{\\codefont " <> m <> "}"


classify :: Pats -> Module -> Column -> S -> S -> What -> Table
classify pats mod col = go
  where
    go :: S -> S -> What -> Table
    go begin rest current
        | not (BS.null rest)
        , Just (mr, toFun) <- matchFirst pats rest
        , let this = begin <> mrBefore mr
        , let next = normWhat mod col $ toFun mr
        = if current == next
          then go (begin <> mrBefore mr <> mrMatch mr) (mrAfter mr) next
          else (mod, current, col, this, countLines this)
               : go (mrMatch mr) (mrAfter mr) next
        | otherwise
        , let this = begin <> rest
        = [(mod, current, col, this, countLines this)]

countLines :: S -> Int
countLines = length . BS.lines . stripComments

stripComments :: S -> S
stripComments =
    BS.unlines .
    filter (not . BS.all isSpace) .
    BS.lines .
    del (mk "--") .
    del (mkM "\\(\\*.*?\\*\\)") .
    del (mkM "{-.*?-}")

del :: Regex -> S -> S
del r s | Just mr <- matchM r s
        = mrBefore mr <> del r (mrAfter mr)
        | otherwise
        = s

matchFirst :: [(Regex,a)] -> S -> Maybe (MatchResult S, a)
matchFirst regexes input
    = if null matches then Nothing else Just best
  where
    best = minimumBy (comparing (BS.length . mrBefore . fst)) matches
    matches = [ (mr, d) | (r,d) <- regexes, mr <- matchM r input]
