# Session Types

```agda
module SPLV.Friday where

open import Lib.Zero
open import Lib.Sum
open import Lib.One
open import Lib.Equality
open import Lib.Datoid
open import Lib.Sigma

data SType : Set where S0 S1 S2 : SType

Signal : SType -> Set
Signal S0 = Zero
Signal S1 = One
Signal S2 = Two

data Head : Set where red blu : Head

data Session : Set
Traffic : Session -> Set

data Session where
  signal : Head -> SType -> Session
  sigma  : (S : Session)(T : Traffic S -> Session) -> Session

Traffic (signal who X) = Signal X
Traffic (sigma S T) = Traffic S >< \ s -> Traffic (T s)

record Party (S : Session) : Set1 where
  field
    Active : Set
    Passive : Active -> Set
    perception : (a : Active)(p : Passive a) -> Traffic S
open Party

party : (h : Head)(S : Session) -> Party S
Active (party h (sigma S T)) =
  Active (party h S) >< \ as -> 
                                  (ps : Passive (party h S) as) ->
  Active (party h (T (perception (party h S) as ps)))
Passive (party h (sigma S T)) (as , psk) =
  Passive (party h S) as >< \ ps ->
  Passive (party h (T (perception (party h S) as ps))) (psk ps)
perception (party h (sigma S T)) (as , psk) (ps , pt) =
  perception (party h S) as ps ,
  perception (party h (T (perception (party h S) as ps))) (psk ps) pt

Active (party red (signal red X)) = Signal X
Active (party red (signal blu X)) = One
Active (party blu (signal red X)) = One
Active (party blu (signal blu X)) = Signal X
Passive (party red (signal red X)) x  = One
Passive (party red (signal blu X)) <> = Signal X
Passive (party blu (signal red X)) <> = Signal X
Passive (party blu (signal blu X)) x  = One
perception (party red (signal red X)) x <> = x
perception (party red (signal blu X)) <> x = x
perception (party blu (signal red X)) <> x = x
perception (party blu (signal blu X)) x <> = x

chat : (S : Session)(r : Active (party red S))(b : Active (party blu S)) ->
       (Passive (party red S) r) >< \ r' ->
       (Passive (party blu S) b) >< \ b' ->
       perception (party red S) r r' ~ perception (party blu S) b b'
chat S r b = {!!}
```

