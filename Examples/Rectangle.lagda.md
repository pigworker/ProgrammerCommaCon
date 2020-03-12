```agda
module Examples.Rectangle where

open import Agda.Builtin.Char

open import Lib.One
open import Lib.Pi
open import Lib.Sigma
open import Lib.Interact
open import Lib.Shell
```


```agda

example : Char -> Colour -> [ Server SHELL HAppy ]
painting (display (example c fg)) = pureV (pureV (fg - c / black))
cursorAt (display (example c fg)) = 0 , 0
react (example c fg) (key (char c')) = <> , example c' fg
react (example c fg) (key enter)     = <> , example c (next fg)
  where
  next : Colour -> Colour
  next black   = red
  next red     = green
  next green   = yellow
  next yellow  = blue
  next blue    = magenta
  next magenta = cyan
  next cyan    = white
  next white   = black
react (example c fg) (key _)         = <> , example c fg 
react (example c fg) (resize w h)    = <> , example c fg

main : IO One
main = appMain (example '*' green)

```

To compile

    agda --compile --ghc-flag "-lncurses" Examples/Rectangle.lagda.md

To run:

    ./Rectangle
