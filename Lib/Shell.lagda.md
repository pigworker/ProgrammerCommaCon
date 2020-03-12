```agda
module Lib.Shell where

open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Nat renaming (_*_ to _*N_)     -- conflicts with mine...

{-# FOREIGN GHC import qualified Lib.ANSIEscapes as ANSIEscapes #-}
{-# FOREIGN GHC import qualified Lib.HaskellSetup as HaskellSetup #-}

open import Lib.List
open import Lib.Sigma
open import Lib.Equality
open import Lib.One
open import Lib.Pi

open import Lib.Interact
```

For compilation purposes we make _*_ into its own data type.

```agda
record _**_ (S T : Set) : Set where
  constructor _,_
  field
    outl : S
    outr : T
open _**_
{-# COMPILE GHC _**_ = data (,) ((,)) #-}
infixr 4 _**_
```

```agda
postulate       -- Connecting to the Haskell IO monad
  IO        : Set -> Set
  returnIO  : {A : Set} -> A -> IO A
  _>>IO=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
infixl 1 _>>IO=_
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}
{-# COMPILE GHC returnIO = (\ _ -> return) #-}
{-# COMPILE GHC _>>IO=_ = (\ _ _ -> (>>=)) #-}
```

```agda
data Colour : Set where
  black red green yellow blue magenta cyan white : Colour

{-# COMPILE GHC Colour = data HaskellSetup.Colour (HaskellSetup.Black | HaskellSetup.Red | HaskellSetup.Green | HaskellSetup.Yellow | HaskellSetup.Blue | HaskellSetup.Magenta | HaskellSetup.Cyan | HaskellSetup.White) #-}

data ColourChar : Set where
  _-_/_ : (fg : Colour)(c : Char)(bg : Colour) -> ColourChar
```

```agda
data Direction : Set where up down left right : Direction

data Modifier : Set where normal shift control : Modifier

data Key : Set where
  char       : Char -> Key
  arrow      : Modifier -> Direction -> Key
  enter      : Key
  backspace  : Key
  delete     : Key
  escape     : Key
  tab        : Key

{-# COMPILE GHC Key = data HaskellSetup.Key (HaskellSetup.Char | HaskellSetup.Arrow | HaskellSetup.Enter | HaskellSetup.Backspace | HaskellSetup.Delete | HaskellSetup.Escape | HaskellSetup.Tab) #-}
{-# COMPILE GHC Direction = data ANSIEscapes.Dir (ANSIEscapes.DU | ANSIEscapes.DD | ANSIEscapes.DL | ANSIEscapes.DR) #-}
{-# COMPILE GHC Modifier = data HaskellSetup.Modifier (HaskellSetup.Normal | HaskellSetup.Shift | HaskellSetup.Control) #-}
```

```agda
data Event : Set where
  key     : (k : Key) -> Event
  resize  : (w h : Nat) -> Event
{-# COMPILE GHC Event = data HaskellSetup.Event (HaskellSetup.Key | HaskellSetup.Resize) #-}
```

```agda
data Action : Set where
  goRowCol : Nat -> Nat -> Action        -- send the cursor somewhere
  sendText : List Char -> Action         -- send some text
  move     : Direction -> Nat -> Action  -- which way and how much
  fgText   : Colour -> Action            -- change foreground colour
  bgText   : Colour -> Action            -- change background colour

{-# COMPILE GHC Action = data HaskellSetup.Action (HaskellSetup.GoRowCol | HaskellSetup.SendText | HaskellSetup.Move | HaskellSetup.FgText | HaskellSetup.BgText) #-}
```

```agda
data Vec (X : Set) : Nat -> Set where
  []   : Vec X zero
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

Matrix : Set -> Nat * Nat -> Set
Matrix C (w , h) = Vec (Vec C w) h

pureV : forall {n : Nat} {X : Set} -> X -> Vec X n
pureV {zero} x = []
pureV {suc n} x = x ,- pureV x
```

```agda
Painting : Nat * Nat -> Set
Painting = Matrix ColourChar

paintAction : {wh : Nat * Nat} -> Matrix ColourChar wh -> List Action
paintAction [] = []
paintAction (line ,- rest) = paintLine line +L paintAction rest
  where paintLine : {n : Nat} -> Vec ColourChar n -> List Action
        paintLine [] = []
        paintLine ((fg - c / bg) ,- xs) = fgText fg ,- bgText bg ,- sendText (c ,- []) ,- paintLine xs
```

```agda
SHELL : (Nat * Nat) ?> (Nat * Nat)
Question SHELL wh = Event
Answer SHELL wh q = One
status SHELL wh (key k)      <> = wh
status SHELL _  (resize w h) <> = w , h

record HAppy (wh : Nat * Nat) : Set where
  field
    painting : Painting wh
    cursorAt : Nat * Nat -- should really be bounded by wh
open HAppy public
```

```agda
postulate
  mainShellLoop : {S : Set} ->             -- program state
    -- INITIALIZER
    S ->                              -- initial state
    -- EVENT HANDLER
    (Event -> S ->                    -- event and state in
     S ** List Action) ->              -- new state and screen actions out
    -- PUT 'EM TOGETHER AND YOU'VE GOT A SHELL APPLICATION!
    IO One
{-# COMPILE GHC mainShellLoop = (\ _ -> HaskellSetup.mainAppLoop) #-}
```

```agda
appMain : [ Server SHELL HAppy ] -> IO One
appMain app = mainShellLoop {(Nat * Nat) >< Server SHELL HAppy}
              ((0 , 0) , app)
              go
  where
  paint : (Nat * Nat) >< Server SHELL HAppy -> List Action
  paint (_ , s) with display s
  paint (_ , s) | record { painting = css ; cursorAt = x , y } = 
    goRowCol 0 0 ,-  paintAction css +L goRowCol y x ,- []
  
  go : Event ->
      (Nat * Nat) >< Server SHELL HAppy ->
      ((Nat * Nat) >< Server SHELL HAppy) ** List Action
  go e (wh , s) with react s e
  go e (wh , s) | <> , s' = (_ , s') , paint (_ , s')
```
